(ns AIMath.core
  (:require 
    [clojure.zip :as zip]))

;; parameters
(def internal-node-bias false)
(def tournament-size 7)
(def persistence-probability 0.9) ; 0 -> standard GP, 1 -> require improvement

(def max-size 1000)

(def mutation-new-subterm-expected-size 10)  
(def mutation-new-subterm-max-depth 10) 

(def use-lexicase-selection true)

(def single-thread-mode (atom false))

;;;;;
;; backtrace abbreviation, to ease debugging
(defn bt []
  (.printStackTrace *e))

;; individuals in the population are stored as structs
(defstruct individual :term :size :errors :total-error)

(defn rand-elt
  "Returns a random element of the given list."
  [lst]
  (nth lst (rand-int (count lst))))

(defn eval-term 
  "Returns the value to which the given term evaluates, using the
   provide operator and bindings."
  [term op bindings]
  (cond 
    (number? term) term
    (symbol? term) (term bindings)
    :else (let [leftval (eval-term (nth term 1) op bindings)
                rightval (eval-term (nth term 2) op bindings)]
            (nth (nth op leftval) rightval))))

(defn term-size
  "Returns the size of the term in points, where each operator
   and each variable counts as a point."
  [term]
  (if (seq? term)
    (inc (reduce + (map term-size (rest term))))
    1))

(defn term-behavior 
  "Returns a list of all behaviors of the term (using the given
   operator), where each behavior is a list of the form (bindings value),
   where bindings is a three-element list specifying values for x, y, and
   z, and value is the term in the context of those bindings."
  [term op]
  (let [sz (count op)]
    (for [x (range sz)
          y (range sz)
          z (range sz)]
      (list
        (list x y z)
        (eval-term term op {'x x 'y y 'z z})))))

(defn discriminator-errors
  "Returns a sequence with a 1 for each binding pattern for which the the given term does
   not behave as a discriminator, and a 0 for each pattern for which it does."
  [term op]
  (if (symbol? term) ;; hack to avoid single var terms
    (for [_ (range (let [sz (count op)] (* sz sz sz)))] 99999)
    (let [behavior (term-behavior term op)]
      (for [b behavior]
        (let [[x y z] (first b) output (second b)]
          (if (== x y)
            (if (== output z) 0 1)
            (if (== output x) 0 1)))))))

(defn malcev-errors
  "Returns a sequence with a 1 for each binding pattern for which the given term does
   not behave as a malcev term, and a 0 for each pattern for which it does."
  [term op]
  (if (symbol? term) ;; hack to avoid single var terms
    (for [_ (range (let [sz (count op)] (* sz sz sz)))] 99999)
    (let [behavior (term-behavior term op)]
      (for [b behavior]
        (let [[x y z] (first b) output (second b)]
          (if (== x y)
            (if (== output z) 0 1)
            (if (== y z)
              (if (== output x) 0 1)
              0)))))))

(defn majority-errors
  "Returns a sequence with a 1 for each binding pattern for which the given term does
   not behave as a majority term, and a 0 for each pattern for which it does."
  [term op]
  (if (symbol? term) ;; hack to avoid single var terms
    (for [_ (range (let [sz (count op)] (* sz sz sz)))] 99999)
    (let [behavior (term-behavior term op)]
      (for [[a b] behavior]
        (let [[x y z] a output b]
          (if (or (== x y) (== x z))
            (if (== output x) 0 1)
            (if (== y z)
              (if (== output y) 0 1)
              0)))))))


;j(x,x,y) = j(y,x,x) = j(x,y,x) = x
;if first two equal, answer x
;if second and third equal answer y
;if first and third equal answer x
;if any two equal, answer that value

(defn pixley-errors
  "Returns a sequence with a 1 for each binding pattern for which the given term does
   not behave as a pixley term, and a 0 for each pattern for which it does."
  [term op]
  (if (symbol? term) ;; hack to avoid single var terms
    (for [_ (range (let [sz (count op)] (* sz sz sz)))] 99999)
    (let [behavior (term-behavior term op)]
      (for [[a b] behavior]
        (let [[x y z] a output b]
          (if (== x y)
            (if (== output z) 0 1)
            (if (== y z)
              (if (== output x) 0 1)
              (if (== x z)
                (if (== output x) 0 1)
                0))))))))
                
;
          

(defn ptc1-term
  [p max-depth]
  "Returns a random term generated using Sean Luke's PTC1 with the given
   probability of choosing a nonterminal over a terminal (p) and maximum depth.
   See http://cs.gmu.edu/~sean/papers/treecreation.pdf."
  (if (or (<= max-depth 0) (< (rand) (- 1.0 p)))
    (rand-elt '(x y z))
    (list '*
          (ptc1-term p (- max-depth 1))
          (ptc1-term p (- max-depth 1)))))

(defn random-term
  "Returns a random term generated using Sean Luke's PTC1 with the given
   expected-size and max depth. http://cs.gmu.edu/~sean/papers/treecreation.pdf.
   Note that the calculation of computing p, the probability of choosing a 
   nonterminal over a terminal, is simplified because of the special case
   of our binary expressions with only a single operator."
  [expected-size max-depth]
  (let [p (/ (- 1 (/ 1 expected-size)) 2)]
    ;(println "p = " p)
    (ptc1-term p max-depth)))

;(println (/ (reduce + (doall (map term-size (take 1000 (repeatedly #(random-term 5 100)))))) 1000.0))
;(println (/ (reduce + (doall (map term-size (take 1000 (repeatedly #(random-term 50 100)))))) 1000.0))
;(println (/ (reduce + (doall (map term-size (take 1000 (repeatedly #(random-term 500 100)))))) 1000.0))

(defn subterm-at-point 
  "Returns a subterm of term indexed by the index in a depth first traversal."
  [term index]
  (let [zipper (zip/seq-zip term)]
    (loop [z zipper i index]
      (if (zero? i)
        (zip/node z)
        (if (seq? (zip/node z))
          (recur (zip/next (zip/next z)) (dec i))
          (recur (zip/next z) (dec i)))))))

(defn insert-subterm-at-point 
  "Returns a copy of term with the subterm formerly indexed by
   the index (in a depth-first traversal) replaced by new-subterm."
  [term index new-subterm]
  (let [zipper (zip/seq-zip term)]
    (loop [z zipper i index]
      (if (zero? i)
        (zip/root (zip/replace z new-subterm))
        (if (seq? (zip/node z))
          (recur (zip/next (zip/next z)) (dec i))
          (recur (zip/next z) (dec i)))))))

(defn internals-leaves 
  "Returns two lists: a list of the indices of internal nodes and a list of indices of 
   leaves."
  [term]
  (let [zipper (zip/seq-zip term) points (term-size term)]
    (loop [z zipper i 0 internals () leaves ()]
      (if (>= i points)
        (list internals leaves) 
        (if (seq? (zip/node z))
          (recur (zip/next (zip/next z)) (inc i) (cons i internals) leaves)
          (recur (zip/next z) (inc i) internals (cons i leaves)))))))

(defn modification-point
  "Returns the index of a point within term to be modified, biasing the selection toward
   internal nodes if internal-node-bias is true."
  [term]
  (if (seq? term)
    (if internal-node-bias
      (let [il (internals-leaves term)]
        (if (< (rand) 0.9)
          (rand-elt (first il))
          (rand-elt (second il))))
      (rand-int (term-size term)))
    0))

(defn mutate
  "Returns a new individual that is a mutated version of the given individual."
  [i error-function op]
  (let [term (insert-subterm-at-point (:term i) 
                                      (modification-point (:term i))
                                      (random-term mutation-new-subterm-expected-size 
                                                   mutation-new-subterm-max-depth))
        sz (term-size term)]
    (if (> sz max-size)
      i
      (let [ers (error-function term op)
            er (reduce + ers)] 
        (if (or (< er (:total-error i))
                (> (rand) persistence-probability))
          (struct-map individual :term term :size sz :errors ers :total-error er)
          i)))))

;; standard GP crossover
#_(defn crossover
  "Returns a new individual produced by crossover from the given individuals."
  [individual1 individual2 error-function op]
  (let [term (insert-subterm-at-point (:term individual1)
                                      (modification-point (:term individual1))
                                      (subterm-at-point (:term individual2) (rand-int (:size individual2))))
        sz (term-size term)]
    (if (> sz max-size)
      individual1
      (let [ers (error-function term op)
            er (reduce + ers)] 
        (if (or (< er (:total-error individual1))
                (> (rand) persistence-probability))
          (struct-map individual :term term :size sz :errors ers :total-error er)
          individual1)))))

;; root swap crossover (David's idea)
#_(defn crossover
  "Returns a new individual produced by crossover from the given individuals."
  [individual1 individual2 error-function op]
  ;; both parents must have nontrivial terms or we fail to individual1
  (if (not (and (seq? (:term individual1))
                (seq? (:term individual2))))
    individual1
    (let [term (list '* (nth (:term individual1) 2) (nth (:term individual2) 1))
          sz (term-size term)]
      (if (> sz max-size)
        individual1
        (let [ers (error-function term op)
              er (reduce + ers)] 
          (if (or (< er (:total-error individual1))
                  (> (rand) persistence-probability))
            (struct-map individual :term term :size sz :errors ers :total-error er)
            individual1))))))

;; root crossover (mod of David's idea)
(defn crossover
  "Returns a new individual produced by crossover from the given individuals."
  [individual1 individual2 error-function op]
  ;; both parents must have nontrivial terms or we fail to individual1
  (if (not (and (seq? (:term individual1))
                (seq? (:term individual2))))
    individual1
    (let [term (list '* (nth (:term individual1) 1) (nth (:term individual2) 2))
          sz (term-size term)]
      (if (> sz max-size)
        individual1
        (let [ers (error-function term op)
              er (reduce + ers)] 
          (if (or (< er (:total-error individual1))
                  (> (rand) persistence-probability))
            (struct-map individual :term term :size sz :errors ers :total-error er)
            individual1))))))

(defn better
  "Returns the better of the two given individuals."
  [individual1 individual2]
  (cond 
    (< (:total-error individual1) (:total-error individual2)) individual1
    (< (:total-error individual2) (:total-error individual1)) individual2
    ;(< (:size individual1) (:size individual2)) individual1
    :else individual2))

(defn select-individual
  "Returns an individual selected from the population via tournament selection."
  [population]
  (if (= use-lexicase-selection false)
    (let [popsize (count population) 
          tournament-set (take tournament-size (repeatedly #(nth population (rand-int popsize))))]
      (reduce better tournament-set))
    (loop [survivors population
           cases (shuffle (range (count (:errors (first population)))))]
      (if (or (empty? cases)
              (empty? (rest survivors)))
        (rand-nth survivors)
        (let [min-err-for-case (apply min (map #(nth % (first cases))
                                               (map #(:errors %) survivors)))]
          (recur (filter #(= (nth (:errors %) (first cases)) min-err-for-case)
                         survivors)
                 (rest cases)))))))


;;;;;;;;;;;;
;;; from clojush
#_(defn lexicase-selection
  "Returns an individual that does the best on a randomly selected set of fitness cases"
  [pop]
  (loop [survivors pop
         cases (shuffle (range (count (:errors (first pop)))))]
    (if (or (empty? cases)
            (empty? (rest survivors)))
      (lrand-nth survivors)
      (let [min-err-for-case (apply min (map #(nth % (first cases))
                                             (map #(:errors %) survivors)))]
        (recur (filter #(= (nth (:errors %) (first cases)) min-err-for-case)
                       survivors)
               (rest cases))))))
;;;;

(defn make-child
  "Returns a new individual produced from the given population by a genetic operation."
  [population error-function op _]
  (let [genetic-op (rand)]
    (cond 
      (< genetic-op 0.5) (crossover (select-individual population)
                                    (select-individual population) error-function op)
      (< genetic-op 1.0) (mutate (select-individual population) error-function op)
      :else (select-individual population))))

(defn pmapall
  "Like pmap but: 1) coll should be finite, 2) the returned sequence
   will not be lazy, 3) calls to f may occur in any order, to maximize
   multicore processor utilization, and 4) takes only one coll so far."
  [f coll]
  (if @single-thread-mode
    (map f coll)
    (let [agents (map #(agent % :error-handler (fn [agnt except] (println except))) coll)]
      (dorun (map #(send % f) agents))
      (apply await agents)
      (doall (map deref agents)))))

(defn step-forward
  "Returns a new population produced from the given population by producing an
   equivalent number of children."

  [population population-size error-function operator]
  (vec (doall (pmapall #(make-child population error-function operator %) (range population-size)))))

(defn evolve-term
  "Runs a genetic programming system to find a term for the algebra defined
   by the given operator."
  [error-function operator population-size max-generations 
   expected-size-of-initial-terms max-depth-for-initial-terms]
  (let [start-time (System/nanoTime)]
    (loop [generation 0
           population (vec ;; initial, evaluated population
                           (doall (pmapall (fn [_]
                                             (let [term (random-term expected-size-of-initial-terms
                                                                     max-depth-for-initial-terms)
                                                   ers (error-function term operator)] 
                                               ;; initial terms may exceed max-size, but not children  
                                               (struct-map individual 
                                                           :term term 
                                                           :size (term-size term) 
                                                           :errors ers
                                                           :total-error (reduce + ers))))
                                           (range population-size))))]
      (let [best (reduce better population)]
        (printf "\nGeneration: %s\nBest error: %s\nTerm: %s\nPoints: %s\nAverage points: %s\n" 
                generation (:total-error best) (apply list (:term best)) (:size best)
                (/ (reduce + (map :size population)) (float (count population))))
        (flush)
        (if (zero? (:total-error best))
          (do (println "Success!") 
              {:success true :generation generation :nanoseconds (- (System/nanoTime) start-time)})
          (if (>= generation max-generations)
            (do (println "Failure!")
                {:success false :generation generation :nanoseconds (- (System/nanoTime) start-time)})
            (recur (inc generation) 
                   (step-forward population population-size error-function operator))))))))

(def a1 '((2 1 2)
          (1 0 0)
          (0 0 1)))

(def a2 '((2 0 2)
          (1 0 2)
          (1 2 1)))

(def a3 '((1 0 1)
          (1 2 0)
          (0 0 0)))

(def a4 '((1 0 1)
          (0 2 0)
          (0 1 0)))

(def a5 '((1 0 2)
          (1 2 0)
          (0 1 0)))


; #1176            #2428
;*   0 1 2          *   0 1 2
; 0  0 0 2           0  1 0 0 
; 1  0 2 1           1  0 2 1
; 2  2 1 0           2  0 1 1

(def n1176 '((0 0 2)
             (0 2 1)
             (2 1 0)))

(def n2428 '((1 0 0)
             (0 2 1)
             (0 1 1)))


; #2895
; *  0 1 2
; 0  1 0 2
; 1  0 0 1
; 2  2 1 0

(def n2895
  '((1 0 2)
    (0 0 1)
    (2 1 0)))

(def b1
  '((1 3 1 0)
    (3 2 0 1)
    (0 1 3 1)
    (1 0 2 0)))
  

;run some tests with lexicase on or off, tournament size 2, 4, 7, 10; different algebras a1, a2, etc

;
;(evolve-term discriminator-error a1 100000 1000 50 20)

;(evolve-term pixley-errors a1 100000 1000 50 20)

;(evolve-term pixley-errors b1 1000 1000 50 20)

#_(defn -main 
  [& args]
  ;(evolve-term malcev-errors n2895 1000 100 50 20)
  #_(loop [i 0 results []]
    (if (>= i 20)
      (do (println "\nRESULTS:")
          (doseq [r results] (println r)))
      (recur (inc i) (conj results (evolve-term discriminator-errors n2895 1000 100 50 20)))))
  
  (let [a1-malcev
        (loop [i 0 results []]
          (if (>= i 20)
            results
            (recur (inc i) (conj results (evolve-term malcev-errors a1 1000 100 50 20)))))
        a2-malcev
        (loop [i 0 results []]
          (if (>= i 20)
            results
            (recur (inc i) (conj results (evolve-term malcev-errors a2 1000 100 50 20)))))
        a3-malcev
        (loop [i 0 results []]
          (if (>= i 20)
            results
            (recur (inc i) (conj results (evolve-term malcev-errors a3 1000 100 50 20)))))
        a4-malcev
        (loop [i 0 results []]
          (if (>= i 20)
            results
            (recur (inc i) (conj results (evolve-term malcev-errors a4 1000 100 50 20)))))
        a5-malcev
        (loop [i 0 results []]
          (if (>= i 20)
            results
            (recur (inc i) (conj results (evolve-term malcev-errors a5 1000 100 50 20)))))
        n1176-malcev
        (loop [i 0 results []]
          (if (>= i 20)
            results
            (recur (inc i) (conj results (evolve-term malcev-errors n1176 1000 100 50 20)))))
        n2428-malcev
        (loop [i 0 results []]
          (if (>= i 20)
            results
            (recur (inc i) (conj results (evolve-term malcev-errors n2428 1000 100 50 20)))))
        n2895-malcev
        (loop [i 0 results []]
          (if (>= i 20)
            results
            (recur (inc i) (conj results (evolve-term malcev-errors n2895 1000 100 50 20)))))]
    (println "\n\nA1 malcev:")
    (doseq [r a1-malcev] (println r))
    (println "\n\nA2 malcev:")
    (doseq [r a2-malcev] (println r))
    (println "\n\nA3 malcev:")
    (doseq [r a3-malcev] (println r))  
    (println "\n\nA4 malcev:")
    (doseq [r a4-malcev] (println r))  
    (println "\n\nA5 malcev:")
    (doseq [r a5-malcev] (println r))  
    (println "\n\n#1176 malcev:")
    (doseq [r n1176-malcev] (println r))
    (println "\n\n#2428 malcev:")
    (doseq [r n2428-malcev] (println r))
    (println "\n\n#2895 malcev:")
    (doseq [r n2895-malcev] (println r)))
  (System/exit 0)
  )


(evolve-term majority-errors b1 1000 2500 10 30) 
(evolve-term majority-errors b1 1000 2500 10 30) 
(evolve-term majority-errors b1 1000 2500 10 30) 
(evolve-term majority-errors b1 1000 2500 10 30) 
(evolve-term majority-errors b1 1000 2500 10 30) 
(evolve-term majority-errors b1 1000 2500 10 30) 
(evolve-term majority-errors b1 1000 2500 10 30)

