(ns organon.syllogistic
  (:require [clojure.set :as se]
            [clojure.core.match :refer [match]]))

;; This reasoner takes a proposition C and a database D and attempts to show whether C may
;; be derived from D.
;;
;; Let imm(C) be the set of propositions derivied through immediate inference from C,
;; including C. Therefore, if for some c in imm(C), c in D, then we have found that C may
;; be derived from D. Otherwise, we must find two propositions a and b such that C can be
;; inferred syllogistically from a and b and where a in imm(A) and b in imm(B) for some A
;; and B in D. If so such a and b exist in D, then a and b may be propositions themselves
;; derivable from D and thus the process repeats.
;;
;; This process, as stated, introduces a few problems:
;;
;; 1. imm(X) requires an extra computational step that adds exponential overhead
;;
;; 2. an exponential forking condition, viz., that for each proposition for which premises
;;    cannot be found in the database, the reasoner forks two processes, each of which
;;    attempt to find two further propositions
;;
;; 3. if no solutions exist in the database, then the reasoner will fail to terminate
;;
;;

(def figure-moods
  {1
   [[:A :A :A]
    [:E :A :E]
    [:A :I :I]
    [:E :I :O]]
   2
   [[:E :A :E]
    [:A :E :E]
    [:E :I :O]
    [:A :O :O]]
   3
   [[:A :A :I]
    [:I :A :I]
    [:A :I :I]
    [:E :A :O]
    [:O :A :O]
    [:E :I :O]]
   4
   [[:A :A :I]
    [:A :E :E]
    [:I :A :I]
    [:E :A :O]
    [:E :I :O]]})

(def figure-term-posns
  {1 [{:subject :middle-term :predicate :major-term}
      {:subject :minor-term :predicate :middle-term}]
   2 [{:subject :major-term :predicate :middle-term}
      {:subject :minor-term :predicate :middle-term}]
   3 [{:subject :middle-term :predicate :major-term}
      {:subject :middle-term :predicate :minor-term}]
   4 [{:subject :major-term :predicate :middle-term}
      {:subject :middle-term :predicate :minor-term}]})

;;
;; Indexes and indexing
;;
(defn insert-mood
  [m mood]
  (if (> (count mood) 1)
    (assoc m (first mood)
           (insert-mood (get m (first mood))
                        (rest mood)))
    (first mood)))

(defn index-figures
  [figs & {:keys [reversed?] :or {reversed? false}}]
  (letfn [(prep [acc fig-num moods]
            (reduce #(if reversed?
                       (->> %2 (cons fig-num) reverse (insert-mood %1))
                       (insert-mood %1 (conj %2 fig-num)))
                    acc
                    moods))]
    (reduce-kv prep {} figs)))

(def figure-index (index-figures figure-moods))
(def reverse-figure-index (index-figures figure-moods :reversed? true))

(def database {})

;;
;; Propositional transformations
;;

;; A proposition is of the form:
;;     {:form <form> :subject <term> :predicate <term>}

(defn negate-term
  [t]
  (when (t :sign)
    (->> t
         :sign
         {:pos :neg
          :neg :pos}
         (assoc t :sign))))

(defn negate-subject
  [p]
  (when (->> p :subject :sign)
    (->> p
         :subject
         negate-term
         (assoc p :subject))))

(defn negate-predicate
  [p]
  (when (->> p :predicate :sign)
    (->> p
         :predicate
         negate-term
         (assoc p :predicate))))

(defn swap-terms
  [p]
  (when (and (p :subject) (p :predicate))
    (assoc p
           :subject   (p :predicate)
           :predicate (p :subject))))

(defn trans-form
  [p m]
  (->> p
       :form
       m
       (assoc p :form)))

(defn contradict
  [p]
  (trans-form p {:A :O
                 :E :I
                 :I :E
                 :O :A}))

(defn contrary
  [p]
  (trans-form p {:A :E
                 :E :A}))

(defn subcontrary
  [p]
  (trans-form p {:I :O
                 :O :I}))

(defn subaltern
  [p]
  (trans-form p {:A :I
                 :E :O
                 :I :A
                 :O :E}))

(defn converse
  [p]
  (-> p
      (trans-form {:A :I
                   :E :E
                   :I :I})
      swap-terms))

(defn observe
  [p]
  (-> p
      (trans-form {:A :E
                   :E :A
                   :I :O
                   :O :I})
      negate-predicate))

(defn contrapos
  [p]
  (-> p
      (trans-form {:A :E
                   :E :I
                   :O :I})
      negate-predicate
      swap-terms))

(defn inverse
  [p]
  (-> p
      (trans-form {:A :O
                   :E :I})
      negate-subject))

;;
;; Syllogistic transformations
;;

;; A syllogism has the form:
;;     {:premises #{<proposition> <proposition>}
;;      :conclusion <proposition>}

(defn major-term
  [s]
  (-> s
      :conclusion
      :predicate))

(defn minor-term
  [s]
  (-> s
      :conclusion
      :subject))

(defn middle-term
  [s]
  (->> :premises
       s
       (map #(-> % (dissoc :form) vals))
       (map set)
       se/intersection))

(defn mood
  [s]
  (let [m (conj (->> :premises s (mapv :form))
                (-> s :conclusion :form))]
    (if (get-in figure-index m)
      m
      (let [[p q c] m]
        [q p c]))))

(defn figure
  [s]
  (get-in figure-index (mood s)))

;;
;; Display
;;
(defn str-p
  [p & {:keys [:neg-copula?] :or {neg-copula? true}}]
  (letfn [(str-term [t make-neg?]
            (str (if (and (= (t :sign) :neg) make-neg?)
                   (format "non-%s" (-> t :term name))
                   (-> t :term name))))
          (str-copula [pr make-neg?]
            (if (and (= (pr :sign) :neg) make-neg?)
              "is not"
              "is"))]
    (format ({:A "every %s %s %s"
              :E "no %s %s %s"
              :I "some %s %s %s"
              :O "some %s %s %s"} (p :form))
            (str-term (p :subject) true)
            (str-copula (p :predicate) neg-copula?)
            (if (= (p :form) :O)
              (str-term (p :predicate) neg-copula?)
              (str-term (p :predicate) (not neg-copula?))))))

;;
;; Inference
;;
(defn infer
  [p q]
  (letfn [(conc-form [p q]
            (-> :form p figure-index (q :form)))]
    (let [r1 (conc-form p q)
          r2 (conc-form q p)
          final (cond r1 [p q r1] [q p r2])]
      (when final
        (let [[pf qf [c fignum]] final
              [p1 p2] (figure-term-posns fignum)
              {st1 :subject pt1 :predicate} p1
              {st2 :subject pt2 :predicate} p2]
          (match [st1 pt1
                  st2 pt2]
                 ;; Fig. 1
                 [_ :major-term
                  :minor-term _]
                 {:form form :subject (qf :subject) :predicate (pf :predicate)}

                 ;; Fig. 2
                 [:major-term _
                  :minor-term _]
                 {:form form :subject (qf :subject) :predicate (pf :subject)}

                 ;; Fig. 3
                 [_ :major-term
                  _ :minor-term]
                 {:form form :subject (qf :predicate) :predicate (pf :predicate)}

                 ;; Fig. 4
                 [:major-term _
                  _ :minor-term]
                 {:form form :subject (qf :predicate) :predicate (pf :subject)}

                 :else nil))))))
