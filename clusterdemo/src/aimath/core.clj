(ns aimath.core
  (:require [clojure.zip :as zip]))

;;; Parameters

;; GP tree
(def ^:const internal-node-bias false)
(def ^:const max-size 1000)
(def ^:const mutation-new-subterm-expected-size 10)
(def ^:const mutation-new-subterm-max-depth 10)

;; Selection method:
;;   :tournament       — classic tournament selection
;;   :lexicase         — standard lexicase (Spector 2012)
;;   :epsilon-lexicase — epsilon-relaxed lexicase (Helmuth et al. 2014)
;;   :dalex            — case-variance-weighted tournament (simplified DALex, Ding et al. 2023)
(def ^:const selector :epsilon-lexicase)
(def ^:const tournament-size 7)

;; Epsilon method (used when selector = :epsilon-lexicase):
;;   :mad          — Median Absolute Deviation (Helmuth & Spector 2014)
;;   :min-variance — minimum-variance partition threshold (Ding et al. 2024)
(def ^:const epsilon-method :mad)

;; Down-sampling (Hernandez et al. 2019 / Boldi et al. 2023)
(def ^:const use-down-sampling true)
(def ^:const down-sample-rate 0.5)
(def ^:const use-informed-down-sampling true)

;; Population
(def ^:const persistence-probability 0.9)
(def ^:const elitism-count 1)             ; was 5 — fewer elites reduces anchoring to local optima
(def ^:const deduplicate-behaviors true)

;; Stagnation restart — when best error does not improve for this many generations,
;; replace a fraction of the population with fresh random individuals.
;; Each consecutive restart without error improvement escalates through restart-fractions.
;; 0.999 keeps only the single best individual, giving the population a clean slate
;; while still preserving the best-known solution.  Resets to index 0 on any improvement.
(def ^:const stagnation-threshold 50)
(def ^:const restart-fractions [0.50 0.75 0.90 0.999])

;; Bloat control
;; lexicase-prefer-smaller: when lexicase reduces survivors to a pool, pick the smallest
;; term rather than a random one. This keeps selection pressure toward compact solutions
;; without compromising the case-based filtering that makes lexicase effective.
(def ^:const lexicase-prefer-smaller false)

;; ALPS (Age-Layered Population Structure) — used by evolve-term-alps only.
;; Layer i allows individuals up to age (alps-age-gap * (i+1)); the last layer is unlimited.
(def ^:const alps-n-layers 5)
(def ^:const alps-age-gap 10)

;;; Individual record

(defrecord Individual [term size errors total-error age])

;;; Operator table
;;
;; An operator-table map has shape {:sz n :tables {sym int-array}}, where:
;;   :sz     — domain size (number of elements; same for all operators in an algebra)
;;   :tables — map from operator symbol to a flat row-major int array of size sz*sz
;;
;; Use make-op to construct; use combine-ops to merge two algebras sharing the same domain.

(defn make-op
  "Converts one or more [symbol nested-vector-table] pairs into an operator-table map.
   All tables must have the same domain size.
   Example (single operator):  (make-op '* [[0 1] [1 0]])
   Example (two operators):    (make-op '* [[0 1] [1 0]]  'f [[1 0] [0 1]])"
  [& sym-table-pairs]
  (let [pairs (partition 2 sym-table-pairs)
        sz    (count (first (second (first pairs))))
        tables (into {}
                     (map (fn [[sym table]]
                            [sym (let [arr (int-array (* sz sz))]
                                   (doseq [r (range sz) c (range sz)]
                                     (aset arr (+ (* r sz) c)
                                           (int (nth (nth table r) c))))
                                   arr)])
                          pairs))]
    {:sz sz :tables tables}))

(defn combine-ops
  "Merges multiple operator-table maps (must share the same domain size)."
  [& ops]
  {:sz     (:sz (first ops))
   :tables (apply merge (map :tables ops))})

(defn- op-symbols [op] (vec (keys (:tables op))))

;;; Core term operations

(defn eval-term
  "Returns the value to which term evaluates using the operator-table map and bindings.
   Compound terms are (op-sym left right); operator lookup uses a primitive int array
   for maximum throughput."
  [term op bindings]
  (cond
    (number? term) term
    (symbol? term) (bindings term)
    :else (let [sym       (first term)
                ^ints arr (get (:tables op) sym)
                sz        (int (:sz op))
                left      (int (eval-term (nth term 1) op bindings))
                right     (int (eval-term (nth term 2) op bindings))]
            (aget arr (+ (* left sz) right)))))

(defn term-size
  "Returns the number of operators and variables in the term."
  [term]
  (if (seq? term)
    (inc (reduce + (map term-size (rest term))))
    1))

(defn term-behavior
  "Returns a vector of [[x y z] value] pairs for all input combinations."
  [term op]
  (let [sz (:sz op)]
    (vec (for [x (range sz) y (range sz) z (range sz)]
           [[x y z] (eval-term term op {'x x 'y y 'z z})]))))

;;; Error functions
;;; Each returns a vector: 0 where the term satisfies the identity, 1 otherwise.
;;; Single-variable terms receive a large penalty to steer away from trivial solutions.

(defn- symbol-penalty [op]
  (let [sz (:sz op)] (vec (repeat (* sz sz sz) 99999))))

(defn discriminator-errors
  "j(x,x,z)=z  and  j(x,y,x)=x"
  [term op]
  (if (symbol? term)
    (symbol-penalty op)
    (mapv (fn [[[x y z] output]]
            (if (== x y)
              (if (== output z) 0 1)
              (if (== output x) 0 1)))
          (term-behavior term op))))

(defn malcev-errors
  "j(x,x,y)=y  and  j(x,y,y)=x"
  [term op]
  (if (symbol? term)
    (symbol-penalty op)
    (mapv (fn [[[x y z] output]]
            (cond
              (== x y) (if (== output z) 0 1)
              (== y z) (if (== output x) 0 1)
              :else 0))
          (term-behavior term op))))

(defn majority-errors
  "j(x,x,y)=j(x,y,x)=j(y,x,x)=x"
  [term op]
  (if (symbol? term)
    (symbol-penalty op)
    (mapv (fn [[[x y z] output]]
            (cond
              (or (== x y) (== x z)) (if (== output x) 0 1)
              (== y z)               (if (== output y) 0 1)
              :else 0))
          (term-behavior term op))))

(defn pixley-errors
  "j(x,x,y)=y,  j(x,y,y)=x,  j(x,y,x)=x"
  [term op]
  (if (symbol? term)
    (symbol-penalty op)
    (mapv (fn [[[x y z] output]]
            (cond
              (== x y) (if (== output z) 0 1)
              (== y z) (if (== output x) 0 1)
              (== x z) (if (== output x) 0 1)
              :else 0))
          (term-behavior term op))))

;;; Term generation (Sean Luke's PTC1)

(defn ptc1-term
  "Returns a random term generated using Sean Luke's PTC1 with probability p of
   choosing a nonterminal over a terminal, maximum depth, and a vector of operator
   symbols to choose from (enables multi-operator algebras).
   See http://cs.gmu.edu/~sean/papers/treecreation.pdf."
  [p max-depth op-syms]
  (if (or (<= max-depth 0) (< (rand) (- 1.0 p)))
    (rand-nth '[x y z])
    (let [sym (rand-nth op-syms)]
      (list sym
            (ptc1-term p (dec max-depth) op-syms)
            (ptc1-term p (dec max-depth) op-syms)))))

(defn random-term
  "Returns a random term using PTC1 with the given expected size, max depth,
   and operator symbol vector."
  [expected-size max-depth op-syms]
  (ptc1-term (/ (- 1 (/ 1.0 expected-size)) 2) max-depth op-syms))

;;; Tree manipulation

(defn subterm-at-point
  "Returns the subterm at the given depth-first index."
  [term index]
  (loop [z (zip/seq-zip term) i index]
    (if (zero? i)
      (zip/node z)
      (if (seq? (zip/node z))
        (recur (zip/next (zip/next z)) (dec i))
        (recur (zip/next z) (dec i))))))

(defn insert-subterm-at-point
  "Returns a copy of term with the subterm at depth-first index replaced by new-subterm."
  [term index new-subterm]
  (loop [z (zip/seq-zip term) i index]
    (if (zero? i)
      (zip/root (zip/replace z new-subterm))
      (if (seq? (zip/node z))
        (recur (zip/next (zip/next z)) (dec i))
        (recur (zip/next z) (dec i))))))

(defn internals-leaves
  "Returns [internals leaves] — index vectors of internal and leaf nodes."
  [term]
  (let [points (term-size term)]
    (loop [z (zip/seq-zip term) i 0 internals [] leaves []]
      (if (>= i points)
        [internals leaves]
        (if (seq? (zip/node z))
          (recur (zip/next (zip/next z)) (inc i) (conj internals i) leaves)
          (recur (zip/next z) (inc i) internals (conj leaves i)))))))

(defn modification-point
  "Returns the index of a point within term to be modified."
  [term]
  (if (seq? term)
    (if internal-node-bias
      (let [[internals leaves] (internals-leaves term)]
        (if (< (rand) 0.9) (rand-nth internals) (rand-nth leaves)))
      (rand-int (term-size term)))
    0))

;;; Individual construction

(defn- make-individual
  "Constructs an Individual by evaluating term against error-fn and op.
   age defaults to 0; pass explicitly for ALPS."
  ([term error-fn op]
   (make-individual term error-fn op 0))
  ([term error-fn op age]
   (let [errors (error-fn term op)]
     (->Individual term (term-size term) errors (reduce + errors) age))))

;;; Genetic operators

(defn mutate
  "Returns a mutated version of the given individual.
   The child's age is one more than the parent's."
  [ind error-fn op]
  (let [syms     (op-symbols op)
        new-term (insert-subterm-at-point
                   (:term ind)
                   (modification-point (:term ind))
                   (random-term mutation-new-subterm-expected-size
                                mutation-new-subterm-max-depth
                                syms))]
    (if (> (term-size new-term) max-size)
      ind
      (let [candidate (make-individual new-term error-fn op (inc (:age ind)))]
        (if (or (< (:total-error candidate) (:total-error ind))
                (> (rand) persistence-probability))
          candidate
          ind)))))

(defn crossover
  "Returns a new individual produced by size-fair subtree crossover (Langdon 2000).
   Picks a random point in ind1's term, then selects a donor subtree from ind2 whose
   size falls within [s/2, 2s] of the replaced subtree. This breaks the bloat ratchet
   where ordinary crossover preferentially donates large subtrees into large parents.
   Falls back to a random point in ind2 if no size-fair point is found in 10 attempts.
   The child's age is one more than the older parent's."
  [ind1 ind2 error-fn op]
  (if-not (and (seq? (:term ind1)) (seq? (:term ind2)))
    ind1
    (let [point1     (modification-point (:term ind1))
          s-replaced (term-size (subterm-at-point (:term ind1) point1))
          point2     (or (some (fn [_]
                                 (let [p (rand-int (:size ind2))
                                       s (term-size (subterm-at-point (:term ind2) p))]
                                   (when (and (>= s (max 1 (quot s-replaced 2)))
                                              (<= s (* 2 s-replaced)))
                                     p)))
                               (range 10))
                         (rand-int (:size ind2)))
          new-term   (insert-subterm-at-point (:term ind1) point1
                                              (subterm-at-point (:term ind2) point2))
          child-age  (inc (max (:age ind1) (:age ind2)))]
      (if (> (term-size new-term) max-size)
        ind1
        (let [candidate (make-individual new-term error-fn op child-age)]
          (if (or (< (:total-error candidate) (:total-error ind1))
                  (> (rand) persistence-probability))
            candidate
            ind1))))))

;;; Epsilon computations (for :epsilon-lexicase mode)

(defn- stat-median [coll]
  (let [sorted (sort coll)
        n      (count sorted)
        mid    (quot n 2)]
    (if (odd? n)
      (double (nth sorted mid))
      (/ (+ (nth sorted (dec mid)) (nth sorted mid)) 2.0))))

(defn- mad-epsilon
  "Auto epsilon via Median Absolute Deviation — Helmuth & Spector 2014."
  [case-errors]
  (let [med (stat-median case-errors)]
    (stat-median (mapv #(Math/abs (- (double %) med)) case-errors))))

(defn- min-variance-epsilon
  "Auto epsilon via minimum-variance partition — Ding et al. 2024."
  [case-errors]
  (let [sorted (vec (sort case-errors))
        n      (count sorted)]
    (if (< n 2)
      0.0
      (let [unique      (distinct sorted)
            mean-sq-dev (fn [grp]
                          (if (empty? grp) 0.0
                            (let [m (/ (reduce + grp) (count grp))]
                              (/ (reduce + (mapv #(let [d (- % m)] (* d d)) grp))
                                 (count grp)))))
            [best-t _]  (reduce
                          (fn [[best-t best-var] t]
                            (let [below (filterv #(<= % t) sorted)
                                  above (filterv #(> % t) sorted)]
                              (if (or (empty? below) (empty? above))
                                [best-t best-var]
                                (let [pooled (+ (* (/ (count below) n) (mean-sq-dev below))
                                               (* (/ (count above) n) (mean-sq-dev above)))]
                                  (if (< pooled best-var) [t pooled] [best-t best-var])))))
                          [0.0 Double/MAX_VALUE]
                          (butlast unique))]
        (- best-t (first sorted))))))

(def ^:private epsilon-fn
  (case epsilon-method
    :mad          mad-epsilon
    :min-variance min-variance-epsilon))

;;; Down-sampling

(defn- case-challenge-scores
  "Scores each case by the fraction of the population that fails to achieve the minimum
   error — higher score means the case challenges more individuals."
  [population n-cases]
  (mapv (fn [c]
          (let [errs    (mapv #(nth (:errors %) c) population)
                min-err (apply min errs)
                n-elite (count (filterv #(== % min-err) errs))]
            (- 1.0 (/ n-elite (count population)))))
        (range n-cases)))

(defn- weighted-sample-without-replacement [k weights]
  (loop [avail  (vec (range (count weights)))
         wts    (vec weights)
         result []]
    (if (or (= (count result) k) (empty? avail))
      result
      (let [total (reduce + wts)
            r     (* (rand) total)
            idx   (loop [i 0 acc 0.0]
                    (let [acc' (+ acc (nth wts i))]
                      (if (or (>= acc' r) (= i (dec (count avail))))
                        i
                        (recur (inc i) acc'))))]
        (recur (into (subvec avail 0 idx) (subvec avail (inc idx)))
               (into (subvec wts 0 idx)  (subvec wts (inc idx)))
               (conj result (nth avail idx)))))))

(defn- sample-cases
  "Returns the set of case indices active for this generation."
  [n-cases population]
  (if-not use-down-sampling
    (vec (range n-cases))
    (let [k (max 1 (int (* down-sample-rate n-cases)))]
      (if use-informed-down-sampling
        (let [scores  (case-challenge-scores population n-cases)
              weights (mapv #(+ 0.01 %) scores)]
          (weighted-sample-without-replacement k weights))
        (vec (take k (shuffle (range n-cases))))))))

;;; Selection

(defn- better [ind1 ind2]
  (let [e1 (:total-error ind1) e2 (:total-error ind2)]
    (cond
      (< e1 e2) ind1
      (< e2 e1) ind2
      (< (:size ind1) (:size ind2)) ind1  ; size tiebreak discourages bloat
      :else ind2)))

(defn select-individual
  "Returns an individual selected from the population using the configured selector."
  [population active-cases]
  (case selector
    :tournament
    (reduce better (repeatedly tournament-size #(rand-nth population)))

    (:lexicase :epsilon-lexicase)
    (let [use-eps (= selector :epsilon-lexicase)]
      (loop [survivors population
             cases     (shuffle active-cases)]
        (if (or (empty? cases) (empty? (rest survivors)))
          (if lexicase-prefer-smaller
            (apply min-key :size survivors)
            (rand-nth survivors))
          (let [c         (first cases)
                errs      (mapv #(nth (:errors %) c) survivors)
                min-err   (apply min errs)
                eps       (if use-eps (epsilon-fn errs) 0.0)
                threshold (+ min-err eps)]
            (recur (filterv #(<= (nth (:errors %) c) threshold) survivors)
                   (rest cases))))))

    :dalex
    (let [weights (mapv (fn [c]
                          (let [errs (mapv #(nth (:errors %) c) population)
                                mean (/ (reduce + errs) (count errs))]
                            (+ 0.01 (Math/sqrt
                                      (/ (reduce + (mapv #(let [d (- % mean)] (* d d)) errs))
                                         (count errs))))))
                        active-cases)
          score   (fn [ind]
                    (reduce + (map-indexed (fn [i c] (* (nth weights i) (nth (:errors ind) c)))
                                           active-cases)))]
      (reduce (fn [best c] (if (< (score c) (score best)) c best))
              (repeatedly tournament-size #(rand-nth population))))))

;;; Population management

(defn make-child
  "Returns a new individual produced from the population by a genetic operation.
   Operator probabilities:  5% macro-mutation (replace entire term),
                           25% crossover,  70% subtree mutation.
   Macro-mutation is the only operator that can escape a structural local optimum
   by discarding the parent's tree entirely and starting fresh."
  [population active-cases error-fn op]
  (let [r (rand)]
    (cond
      (< r 0.05) ; macro-mutation: replace entire term with a fresh random one
      (make-individual (random-term mutation-new-subterm-expected-size
                                    mutation-new-subterm-max-depth
                                    (op-symbols op))
                       error-fn op)
      (< r 0.30) ; crossover
      (crossover (select-individual population active-cases)
                 (select-individual population active-cases)
                 error-fn op)
      :else       ; subtree mutation
      (mutate (select-individual population active-cases) error-fn op))))

(defn- novel-individual
  "Generates a random individual whose error vector is not in existing-behaviors.
   Tries up to 10 times before accepting any individual (novelty best-effort)."
  [existing-behaviors error-fn op]
  (let [syms (op-symbols op)]
    (loop [attempts 0]
      (let [ind (make-individual
                  (random-term mutation-new-subterm-expected-size
                               mutation-new-subterm-max-depth
                               syms)
                  error-fn op)]
        (if (or (>= attempts 10) (not (contains? existing-behaviors (:errors ind))))
          ind
          (recur (inc attempts)))))))

(defn- fill-to-size
  "Pads population to population-size with behaviorally novel random individuals.
   Each injected individual is generated fresh and checked against existing error
   vectors to maximise behavioral diversity (novelty injection)."
  [population population-size error-fn op]
  (let [n-fill (- population-size (count population))]
    (if (<= n-fill 0)
      (vec (take population-size population))
      (let [existing (set (map :errors population))]
        (into (vec population)
              (pmap (fn [_] (novel-individual existing error-fn op))
                    (range n-fill)))))))

(defn- deduplicate-population
  "Groups population by error vector, keeps the most compact term per unique behavior,
   then fills remaining slots with novel fresh individuals."
  [population population-size error-fn op]
  (let [unique (->> (group-by :errors population)
                    vals
                    (mapv #(apply min-key :size %)))]
    (fill-to-size unique population-size error-fn op)))

(defn- restart-population
  "Replaces fraction of the population with fresh novel individuals, retaining
   the best (1 - fraction) × population-size individuals. At fraction=0.999
   only the single best individual survives, giving a near-complete clean slate."
  [population population-size error-fn op fraction]
  (let [n-keep    (max 1 (int (* (- 1.0 fraction) population-size)))
        survivors (vec (take n-keep (sort-by :total-error population)))]
    (fill-to-size survivors population-size error-fn op)))

(defn step-forward
  "Produces the next generation:
   1. Preserves the top elitism-count individuals (elitism).
   2. Generates children in parallel using the configured genetic operators.
   3. Optionally deduplicates by error vector and injects novel individuals."
  [population population-size error-fn op]
  (let [n-cases  (count (:errors (first population)))
        active   (sample-cases n-cases population)
        elite    (vec (take elitism-count (sort-by :total-error population)))
        children (vec (pmap (fn [_] (make-child population active error-fn op))
                            (range (- population-size elitism-count))))
        next-pop (into elite children)]
    (if deduplicate-behaviors
      (deduplicate-population next-pop population-size error-fn op)
      next-pop)))

;;; Main evolutionary loop

(defn evolve-term
  "Runs a GP system to find a term satisfying the given error function and operator table.
   Automatically restarts when no improvement is detected for stagnation-threshold generations."
  [error-fn op population-size max-generations expected-initial-size max-initial-depth]
  (let [start (System/nanoTime)
        syms  (op-symbols op)]
    (loop [generation  0
           population  (vec (pmap (fn [_]
                                    (make-individual
                                      (random-term expected-initial-size max-initial-depth syms)
                                      error-fn op))
                                  (range population-size)))
           stagnation  0
           prev-best   Long/MAX_VALUE
           n-restarts  0]   ; consecutive restarts without error improvement
      (let [best        (reduce better population)
            current-err (:total-error best)
            improved?   (< current-err prev-best)
            stagnation' (if improved? 0 (inc stagnation))
            n-restarts' (if improved? 0 n-restarts)
            [population stagnation' n-restarts']
            (if (>= stagnation' stagnation-threshold)
              (let [fraction (nth restart-fractions
                                  (min n-restarts' (dec (count restart-fractions))))
                    n-keep   (max 1 (int (* (- 1.0 fraction) population-size)))]
                (printf "  [Restart %d: keeping %d/%d (%.0f%% fresh)]\n"
                        (inc n-restarts') n-keep population-size (* 100.0 fraction))
                [(restart-population population population-size error-fn op fraction)
                 0
                 (inc n-restarts')])
              [population stagnation' n-restarts'])
            success (zero? current-err)]
        (when (or success (zero? (mod generation 10)))
          (let [n-unique (count (distinct (map :errors population)))]
            (printf "\nGeneration: %d  Best error: %d  Size: %d  Avg size: %.1f  Unique: %d/%d\nTerm: %s\n"
                    generation current-err (:size best)
                    (/ (double (reduce + (map :size population))) (count population))
                    n-unique (count population)
                    (pr-str (:term best)))
            (flush)))
        (if success
          (do (println "Success!")
              {:success true  :generation generation :nanoseconds (- (System/nanoTime) start)})
          (if (>= generation max-generations)
            (do (println "Failure.")
                {:success false :generation generation :nanoseconds (- (System/nanoTime) start)})
            (recur (inc generation)
                   (step-forward population population-size error-fn op)
                   stagnation'
                   (min current-err prev-best)
                   n-restarts')))))))

;;; ALPS — Age-Layered Population Structure (Hornby 2006)
;;
;; Maintains alps-n-layers sub-populations ("layers").
;; Layer i accepts individuals up to age (alps-age-gap * (i+1)); the last layer is unlimited.
;; Each generation:
;;   1. All individual ages increment by 1.
;;   2. Individuals that have aged out of layer i are offered to layer i+1; accepted only if
;;      better than the worst individual currently there (or there is a free slot).
;;   3. Each layer breeds using parents from itself and all lower layers, ensuring genetic
;;      material flows upward but not downward.
;;   4. Layer 0 is always topped up with fresh age-0 individuals, keeping the bottom layer
;;      young and continuously introducing new genetic material.
;;
;; This prevents old high-fitness individuals from permanently crowding out exploration.

(defn evolve-term-alps
  "Runs ALPS GP to find a term satisfying error-fn on op.
   population-size is distributed evenly across alps-n-layers layers."
  [error-fn op population-size max-generations expected-initial-size max-initial-depth]
  (let [start      (System/nanoTime)
        syms       (op-symbols op)
        layer-size (max 2 (quot population-size alps-n-layers))
        age-limit  (fn [i]
                     (if (= i (dec alps-n-layers))
                       Integer/MAX_VALUE
                       (* alps-age-gap (inc i))))
        make-layer (fn [n age]
                     (vec (pmap (fn [_]
                                  (make-individual
                                    (random-term expected-initial-size max-initial-depth syms)
                                    error-fn op age))
                                (range n))))]

    (loop [generation 0
           layers     (vec (repeatedly alps-n-layers #(make-layer layer-size 0)))]

      (let [all  (reduce into [] layers)
            best (reduce better all)]

        (when (or (zero? (:total-error best)) (zero? (mod generation 10)))
          (printf "\n[ALPS Gen %d] Best error: %d  Layers: %s  Mean ages: %s\nTerm: %s\n"
                  generation
                  (:total-error best)
                  (mapv count layers)
                  (mapv #(if (empty? %) "—"
                           (format "%.0f" (/ (double (reduce + (map :age %))) (count %))))
                        layers)
                  (pr-str (:term best)))
          (flush))

        (if (zero? (:total-error best))
          {:success true  :generation generation :nanoseconds (- (System/nanoTime) start)}
          (if (>= generation max-generations)
            {:success false :generation generation :nanoseconds (- (System/nanoTime) start)}

            (let [;; Step 1: age everyone by 1
                  aged (mapv (fn [layer] (mapv #(update % :age inc) layer)) layers)

                  ;; Step 2: promote aged-out individuals to the next layer if they're better
                  ;; than the worst occupant (or the layer has a free slot)
                  promoted
                  (reduce
                    (fn [ls i]
                      (if (= i (dec alps-n-layers))
                        ls
                        (let [lim    (age-limit i)
                              {stay  false
                               going true} (group-by #(> (:age %) lim) (nth ls i))
                              stay   (vec (or stay []))
                              going  (vec (or going []))
                              next-l (nth ls (inc i))
                              new-next
                              (reduce (fn [nl mover]
                                        (cond
                                          (< (count nl) layer-size)
                                          (conj nl mover)
                                          :else
                                          (let [worst (reduce (fn [a b] (if (> (:total-error a) (:total-error b)) a b)) nl)]
                                            (if (< (:total-error mover) (:total-error worst))
                                              (conj (filterv #(not= % worst) nl) mover)
                                              nl))))
                                      next-l going)]
                          (-> ls (assoc i stay) (assoc (inc i) (vec new-next))))))
                    aged
                    (range alps-n-layers))

                  ;; Step 3: breed each layer from itself and all lower layers
                  n-cases (count (:errors (first all)))
                  bred
                  (vec (pmap
                         (fn [i]
                           (let [eligible (reduce into [] (take (inc i) promoted))
                                 eligible (if (seq eligible) eligible (make-layer layer-size 0))
                                 active   (sample-cases n-cases eligible)
                                 current  (nth promoted i)
                                 n-need   (- layer-size (count current))]
                             (if (<= n-need 0)
                               (vec (take layer-size (sort-by :total-error current)))
                               (into current
                                     (repeatedly n-need
                                                 #(make-child eligible active error-fn op))))))
                         (range alps-n-layers)))

                  ;; Step 4: top up layer 0 with fresh age-0 individuals
                  fresh-n  (max 1 (quot layer-size 5))
                  layer0   (->> (concat (make-layer fresh-n 0) (nth bred 0))
                                (sort-by :total-error)
                                (take layer-size)
                                vec)]

              (recur (inc generation) (assoc bred 0 layer0)))))))))

;;; Algebra definitions

(def a1 (make-op '* [[2 1 2] [1 0 0] [0 0 1]]))
(def a2 (make-op '* [[2 0 2] [1 0 2] [1 2 1]]))
(def a3 (make-op '* [[1 0 1] [1 2 0] [0 0 0]]))
(def a4 (make-op '* [[1 0 1] [0 2 0] [0 1 0]]))
(def a5 (make-op '* [[1 0 2] [1 2 0] [0 1 0]]))

; #1176            #2428
; *  0 1 2          *  0 1 2
;  0 0 0 2           0 1 0 0
;  1 0 2 1           1 0 2 1
;  2 2 1 0           2 0 1 1

(def n1176 (make-op '* [[0 0 2] [0 2 1] [2 1 0]]))
(def n2428 (make-op '* [[1 0 0] [0 2 1] [0 1 1]]))

; #2895
; *  0 1 2
;  0 1 0 2
;  1 0 0 1
;  2 2 1 0

(def n2895 (make-op '* [[1 0 2] [0 0 1] [2 1 0]]))

(def b1 (make-op '* [[1 3 1 0] [3 2 0 1] [0 1 3 1] [1 0 2 0]]))

;; Example multi-operator algebra: pass to evolve-term like any other op map.
;; (def two-op-example (make-op '* [[0 1 2] [1 2 0] [2 0 1]]
;;                               'f [[2 1 0] [1 0 2] [0 2 1]]))

;;; Entry point

(defn -main [& args]
  (let [alps? (= (first args) "--alps")]
    (doseq [_ (range 7)]
      (println
        (if alps?
          (evolve-term-alps majority-errors b1 1000 2500 10 30)
          (evolve-term      majority-errors b1 1000 2500 10 30)))))
  (System/exit 0))
