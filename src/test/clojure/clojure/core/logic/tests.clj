(ns clojure.core.logic.tests
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols]
        [clojure.core.logic :exclude [is] :as l]
        clojure.test)
  (:require [clojure.core.logic.fd :as fd])
  (:require [clojure.core.logic.unifier :as u])
  (:require [clojure.pprint :as pp]
            [clojure.walk]))

;; =============================================================================
;; unify

;; -----------------------------------------------------------------------------
;; nil

(deftest unify-nil-object-1
  (is (= (unify empty-s nil 1) nil)))

(deftest unify-nil-lvar-1
  (let [x (lvar 'x)
        os (ext-no-check empty-s x nil)]
    (is (= (unify empty-s nil x) os))))

(deftest unify-nil-lseq-1
  (let [x (lvar 'x)]
    (is (= (unify empty-s nil (lcons 1 x)) nil))))

(deftest unify-nil-map-1
  (let [x (lvar 'x)]
    (is (= (unify empty-s nil {}) nil))))

;; -----------------------------------------------------------------------------
;; object

(deftest unify-object-nil-1
  (is (= (unify empty-s 1 nil))))

(deftest unify-object-object-1
  (is (= (unify empty-s 1 1) empty-s)))

(deftest unify-object-object-2
  (is (= (unify empty-s :foo :foo) empty-s)))

(deftest unify-object-object-3
  (is (= (unify empty-s 'foo 'foo) empty-s)))

(deftest unify-object-object-4
  (is (= (unify empty-s "foo" "foo") empty-s)))

(deftest unify-object-object-5
  (is (= (unify empty-s 1 2) nil)))

(deftest unify-object-object-6
  (is (= (unify empty-s 2 1) nil)))

(deftest unify-object-object-7
  (is (= (unify empty-s :foo :bar) nil)))

(deftest unify-object-object-8
  (is (= (unify empty-s 'foo 'bar) nil)))

(deftest unify-object-object-9
  (is (= (unify empty-s "foo" "bar") nil)))

(deftest unify-object-lvar-1
  (let [x (lvar 'x)
        os (ext-no-check empty-s x 1)]
    (is (= (unify empty-s 1 x) os))))

(deftest unify-object-lcons-1
  (let [x (lvar 'x)]
    (is (= (unify empty-s 1 (lcons 1 'x)) nil))))

(deftest unify-object-seq-1
  (is (= (unify empty-s 1 '()) nil)))

(deftest unify-object-seq-2
  (is (= (unify empty-s 1 '[]) nil)))

(deftest unify-object-map-1
  (is (= (unify empty-s 1 {}) nil)))

;; -----------------------------------------------------------------------------
;; lvar

(deftest unify-lvar-object-1
  (let [x (lvar 'x)
        os (ext-no-check empty-s x 1)]
    (is (= (unify empty-s x 1) os))))

(deftest unify-lvar-lvar-1
  (let [x (lvar 'x)
        y (lvar 'y)
        os (ext-no-check empty-s x y)]
    (is (= (unify empty-s x y) os))))

(deftest unify-lvar-lcons-1
  (let [x (lvar 'x)
        y (lvar 'y)
        l (lcons 1 y)
        os (ext-no-check empty-s x l)]
    (is (= (unify empty-s x l) os))))

(deftest unify-lvar-seq-1
  (let [x (lvar 'x)
        os (ext-no-check empty-s x [])]
    (is (= (unify empty-s x []) os))))

(deftest unify-lvar-seq-2
  (let [x (lvar 'x)
        os (ext-no-check empty-s x [1 2 3])]
    (is (= (unify empty-s x [1 2 3]) os))))

(deftest unify-lvar-seq-3
  (let [x (lvar 'x)
        os (ext-no-check empty-s x '())]
    (is (= (unify empty-s x '()) os))))

(deftest unify-lvar-seq-4
  (let [x (lvar 'x)
        os (ext-no-check empty-s x '(1 2 3))]
    (is (= (unify empty-s x '(1 2 3)) os))))

(deftest unify-lvar-map-1
  (let [x (lvar 'x)
        os (ext-no-check empty-s x {})]
    (is (= (unify empty-s x {}) os))))

(deftest unify-lvar-map-2
  (let [x (lvar 'x)
        os (ext-no-check empty-s x {1 2 3 4})]
    (is (= (unify empty-s x {1 2 3 4}) os))))

;; -----------------------------------------------------------------------------
;; lcons

(deftest unify-lcons-object-1
  (let [x (lvar 'x)]
    (is (= (unify empty-s (lcons 1 x) 1) nil))))

(deftest unify-lcons-lvar-1
  (let [x (lvar 'x)
        y (lvar 'y)
        l (lcons 1 y)
        os (ext-no-check empty-s x l)]
    (is (= (unify empty-s l x) os))))

(deftest unify-lcons-lcons-1
  (let [x (lvar 'x)
        y (lvar 'y)
        lc1 (lcons 1 x)
        lc2 (lcons 1 y)
        os (ext-no-check empty-s x y)]
    (is (= (unify empty-s lc1 lc2) os))))

(deftest unify-lcons-lcons-2
  (let [x (lvar 'x)
        y (lvar 'y)
        z (lvar 'z)
        lc1 (lcons 1 (lcons 2 x))
        lc2 (lcons 1 (lcons z y))
        os (-> empty-s
               (ext-no-check x y)
               (ext-no-check z 2))]
    (is (= (unify empty-s lc1 lc2) os))))

(deftest unify-lcons-lcons-3
  (let [x (lvar 'x)
        y (lvar 'y)
        lc1 (lcons 1 (lcons 2 x))
        lc2 (lcons 1 (lcons 2 (lcons 3 y)))
        os (ext-no-check empty-s x (lcons 3 y))]
    (is (= (unify empty-s lc1 lc2) os))))

(deftest unify-lcons-lcons-4
  (let [x (lvar 'x)
        y (lvar 'y)
        lc1 (lcons 1 (lcons 2 x))
        lc2 (lcons 1 (lcons 3 (lcons 4 y)))]
    (is (= (unify empty-s lc1 lc2) nil))))

(deftest unify-lcons-lcons-5
  (let [x (lvar 'x)
        y (lvar 'y)
        lc2 (lcons 1 (lcons 2 x))
        lc1 (lcons 1 (lcons 3 (lcons 4 y)))]
    (is (= (unify empty-s lc1 lc2) nil))))

(deftest unify-lcons-lcons-6
  (let [x (lvar 'x)
        y (lvar 'y)
        lc1 (lcons 1 (lcons 2 x))
        lc2 (lcons 1 (lcons 2 y))
        os (ext-no-check empty-s x y)]
    (is (= (unify empty-s lc1 lc2) os))))

(deftest unify-lcons-seq-1
  (let [x (lvar 'x)
        lc1 (lcons 1 (lcons 2 x))
        l1 '(1 2 3 4)
        os (ext-no-check empty-s x '(3 4))]
    (is (= (unify empty-s lc1 l1) os))))

(deftest unify-lcons-seq-2
  (let [x (lvar 'x)
        y (lvar 'y)
        lc1 (lcons 1 (lcons y (lcons 3 x)))
        l1 '(1 2 3 4)
        os (-> empty-s
               (ext-no-check x '(4))
               (ext-no-check y 2))]
    (is (= (unify empty-s lc1 l1) os))))

(deftest unify-lcons-seq-3
  (let [x (lvar 'x)
        lc1 (lcons 1 (lcons 2 (lcons 3 x)))
        l1 '(1 2 3)
        os (ext-no-check empty-s x '())]
    (is (= (unify empty-s lc1 l1) os))))

(deftest unify-lcons-seq-4
  (let [x (lvar 'x)
        lc1 (lcons 1 (lcons 3 x))
        l1 '(1 2 3 4)]
    (is (= (unify empty-s lc1 l1) nil))))

(deftest unify-lcons-seq-5
  (let [x (lvar 'x)
        lc1 (lcons 1 (lcons 2 x))
        l1 '(1 3 4 5)]
    (is (= (unify empty-s lc1 l1) nil))))

(deftest unify-lcons-map-1
  (is (= (unify empty-s (lcons 1 (lvar 'x)) {}) nil)))

;; -----------------------------------------------------------------------------
;; seq

(deftest unify-seq-object-1
  (is (= (unify empty-s '() 1) nil)))

(deftest unify-seq-object-2
  (is (= (unify empty-s [] 1) nil)))

(deftest unify-seq-lvar-1
  (let [x (lvar 'x)
        os (ext-no-check empty-s x [])]
    (is (= (unify empty-s [] x) os))))

(deftest unify-seq-lcons-1
  (let [x (lvar 'x)
        lc1 (lcons 1 (lcons 2 x))
        l1 '(1 2 3 4)
        os (ext-no-check empty-s x '(3 4))]
    (is (= (unify empty-s l1 lc1) os))))

(deftest unify-seq-seq-1
  (is (= (unify empty-s [1 2 3] [1 2 3]) empty-s)))

(deftest unify-seq-seq-2
  (is (= (unify empty-s '(1 2 3) [1 2 3]) empty-s)))

(deftest unify-seq-seq-3
  (is (= (unify empty-s '(1 2 3) '(1 2 3)) empty-s)))

(deftest unify-seq-seq-4
  (let [x (lvar 'x)
        os (ext-no-check empty-s x 2)]
    (is (= (unify empty-s `(1 ~x 3) `(1 2 3)) os))))

(deftest unify-seq-seq-5
  (is (= (unify empty-s [1 2] [1 2 3]) nil)))

(deftest unify-seq-seq-6
  (is (= (unify empty-s '(1 2) [1 2 3]) nil)))

(deftest unify-seq-seq-7
  (is (= (unify empty-s [1 2 3] [3 2 1]) nil)))

(deftest unify-seq-seq-8
  (is (= (unify empty-s '() '()) empty-s)))

(deftest unify-seq-seq-9
  (is (= (unify empty-s '() '(1)) nil)))

(deftest unify-seq-seq-10
  (is (= (unify empty-s '(1) '()) nil)))

(deftest unify-seq-seq-11
  (is (= (unify empty-s [[1 2]] [[1 2]]) empty-s)))

(deftest unify-seq-seq-12
  (is (= (unify empty-s [[1 2]] [[2 1]]) nil)))

(deftest unify-seq-seq-13
  (let [x (lvar 'x)
        os (ext-no-check empty-s x 1)]
    (is (= (unify empty-s [[x 2]] [[1 2]]) os))))

(deftest unify-seq-seq-14
  (let [x (lvar 'x)
        os (ext-no-check empty-s x [1 2])]
    (is (= (unify empty-s [x] [[1 2]]) os))))

(deftest unify-seq-seq-15
  (let [x (lvar 'x) y (lvar 'y)
        u (lvar 'u) v (lvar 'v)
        os (-> empty-s
               (ext-no-check x 'b)
               (ext-no-check y 'a))]
    (is (= (unify empty-s ['a x] [y 'b]) os))))

(deftest unify-seq-map-1
  (is (= (unify empty-s [] {}) nil)))

(deftest unify-seq-map-2
  (is (= (unify empty-s '() {}) nil)))

;; -----------------------------------------------------------------------------
;; map

(deftest unify-map-object-1
  (is (= (unify empty-s {} 1) nil)))

(deftest unify-map-lvar-1
  (let [x (lvar 'x)
        os (ext-no-check empty-s x {})]
    (is (= (unify empty-s {} x) os))))

(deftest unify-map-lcons-1
  (let [x (lvar 'x)]
    (is (= (unify empty-s {} (lcons 1 x)) nil))))

(deftest unify-map-seq-1
  (is (= (unify empty-s {} '()) nil)))

(deftest unify-map-map-1
  (is (= (unify empty-s {} {}) empty-s)))

(deftest unify-map-map-2
  (is (= (unify empty-s {1 2 3 4} {1 2 3 4}) empty-s)))

(deftest unify-map-map-3
  (is (= (unify empty-s {1 2} {1 2 3 4}) nil)))

(deftest unify-map-map-4
  (let [x (lvar 'x)
        m1 {1 2 3 4}
        m2 {1 2 3 x}
        os (ext-no-check empty-s x 4)]
    (is (= (unify empty-s m1 m2) os))))

(deftest unify-map-map-5
  (let [x (lvar 'x)
        m1 {1 2 3 4}
        m2 {1 4 3 x}]
    (is (= (unify empty-s m1 m2) nil))))

(defstruct foo-struct :a :b)

(deftest unify-struct-map-1
  (let [x (lvar 'x)
        m1 (struct-map foo-struct :a 1 :b 2)
        m2 (struct-map foo-struct :a 1 :b x)
        os (ext-no-check empty-s x 2)]
    (is (= (unify empty-s m1 m2) os))))

(deftest unify-struct-map-2
  (let [x (lvar 'x)
        m1 (struct-map foo-struct :a 1 :b 2)
        m2 (struct-map foo-struct :a 1 :b 3)]
    (is (= (unify empty-s m1 m2) nil))))

;; =============================================================================
;; walk

(deftest test-basic-walk
  (is (= (let [x  (lvar 'x)
               y  (lvar 'y)
               ss (to-s [[x 5] [y x]])]
           (walk ss y))
         5)))

(deftest test-deep-walk
  (is (= (let [[x y z c b a :as s] (map lvar '[x y z c b a])
               ss (to-s [[x 5] [y x] [z y] [c z] [b c] [a b]])]
           (walk ss a))
         5)))

;; =============================================================================
;; reify

(deftest test-reify-lvar-name
  (is (= (let [x  (lvar 'x)
               y  (lvar 'y)]
           (reify-lvar-name (to-s [[x 5] [y x]])))
         '_2)))

;; =============================================================================
;; walk*

(deftest test-walk*
  (is (= (let [x  (lvar 'x)
               y  (lvar 'y)]
           (walk* (to-s [[x 5] [y x]]) `(~x ~y)))
         '(5 5))))

;; =============================================================================
;; run and unify

(deftest test-basic-unify
  (is (= (run* [q]
               (== true q))
         '(true))))

(deftest test-basic-unify-2
  (is (= (run* [q]
               (fresh [x y]
                      (== [x y] [1 5])
                      (== [x y] q)))
         [[1 5]])))

(deftest test-basic-unify-3
  (is (=  (run* [q]
                (fresh [x y]
                       (== [x y] q)))
          '[[_0 _1]])))

;; =============================================================================
;; fail

(deftest test-basic-failure
  (is (= (run* [q]
               fail
               (== true q))
         [])))

;; =============================================================================
;; Basic

(deftest test-all
  (is (= (run* [q]
               (all
                (== 1 1)
                (== q true)))
         '(true))))

;; =============================================================================
;; TRS

(defn pairo [p]
  (fresh [a d]
         (== (lcons a d) p)))

(defn twino [p]
  (fresh [x]
         (conso x x p)))

(defn listo [l]
  (conde
   [(emptyo l) s#]
   [(pairo l)
    (fresh [d]
           (resto l d)
           (listo d))]))

(defn flatteno [s out]
  (conde
   [(emptyo s) (== '() out)]
   [(pairo s)
    (fresh [a d res-a res-d]
           (conso a d s)
           (flatteno a res-a)
           (flatteno d res-d)
           (appendo res-a res-d out))]
   [(conso s '() out)]))

;; =============================================================================
;; conde

(deftest test-basic-conde
  (is (=  (into #{}
                (run* [x]
                      (conde
                       [(== x 'olive) succeed]
                       [succeed succeed]
                       [(== x 'oil) succeed])))
          (into #{}
                '[olive _0 oil]))))

(deftest test-basic-conde-2
  (is (= (into #{}
               (run* [r]
                     (fresh [x y]
                            (conde
                             [(== 'split x) (== 'pea y)]
                             [(== 'navy x) (== 'bean y)])
                            (== (cons x (cons y ())) r))))
         (into #{}
               '[(split pea) (navy bean)]))))

(defn teacupo [x]
  (conde
   [(== 'tea x) s#]
   [(== 'cup x) s#]))

(deftest test-basic-conde-e-3
  (is (= (into #{}
               (run* [r]
                     (fresh [x y]
                            (conde
                             [(teacupo x) (== true y) s#]
                             [(== false x) (== true y)])
                            (== (cons x (cons y ())) r))))
         (into #{} '((false true) (tea true) (cup true))))))

;; =============================================================================
;; conso

(deftest test-conso
  (is (= (run* [q]
               (fresh [a d]
                      (conso a d '())))
         ())))

(deftest test-conso-1
  (let [a (lvar 'a)
        d (lvar 'd)]
    (is (= (run* [q]
                 (conso a d q))
           [(lcons a d)]))))

(deftest test-conso-2
  (is (= (run* [q]
               (== [q] nil))
         [])))

(deftest test-conso-3
  (is (=
       (run* [q]
             (conso 'a nil q))
       '[(a)])))

(deftest test-conso-4
  (is (= (run* [q]
               (conso 'a '(d) q))
         '[(a d)])))

(deftest test-conso-empty-list
  (is (= (run* [q]
               (conso 'a q '(a)))
         '[()])))

(deftest test-conso-5
  (is (= (run* [q]
               (conso q '(b c) '(a b c)))
         '[a])))

;; =============================================================================
;; firsto

(deftest test-firsto
  (is (= (run* [q]
               (firsto q '(1 2)))
         (list (lcons '(1 2) (lvar 'x))))))

;; =============================================================================
;; resto

(deftest test-resto
  (is (= (run* [q]
               (resto q '(1 2)))
         '[(_0 1 2)])))

(deftest test-resto-2
  (is (= (run* [q]
               (resto q [1 2]))
         '[(_0 1 2)])))

(deftest test-resto-3
  (is (= (run* [q]
               (resto [1 2] q))
         '[(2)])))

(deftest test-resto-4
  (is (= (run* [q]
               (resto [1 2 3 4 5 6 7 8] q))
         '[(2 3 4 5 6 7 8)])))

;; =============================================================================
;; flatteno

(deftest test-flatteno
  (is (= (into #{}
               (run* [x]
                     (flatteno '[[a b] c] x)))
         (into #{}
               '(([[a b] c]) ([a b] (c)) ([a b] c) ([a b] c ())
                             (a (b) (c)) (a (b) c) (a (b) c ()) (a b (c))
                             (a b () (c)) (a b c) (a b c ()) (a b () c)
                             (a b () c ()))))))

;; =============================================================================
;; membero

(deftest membero-1
  (is (= (run* [q]
               (all
                (== q [(lvar)])
                (membero ['foo (lvar)] q)
                (membero [(lvar) 'bar] q)))
         '([[foo bar]]))))

(deftest membero-2
  (is (= (into #{}
               (run* [q]
                     (membero q [1 2 3])))
         #{1 2 3})))

(deftest membero-3
  ;; Note that membero only returns a single value in this case. The
  ;; old membero, defined without disequality constraints, would have
  ;; returned (1 1 1 1 1).
  (is (= (run* [q]
               (member1o q [1 1 1 1 1]))
         '(1))))

;; -----------------------------------------------------------------------------
;; rembero

(deftest rembero-1
  (is (= (run 1 [q]
              (rembero 'b '(a b c b d) q))
         '((a c b d)))))

;; -----------------------------------------------------------------------------
;; conde clause count

(defn digit-1 [x]
  (conde
   [(== 0 x)]))

(defn digit-4 [x]
  (conde
   [(== 0 x)]
   [(== 1 x)]
   [(== 2 x)]
   [(== 3 x)]))

(deftest test-conde-1-clause
  (is (= (run* [q]
               (fresh [x y]
                      (digit-1 x)
                      (digit-1 y)
                      (== q [x y])))
         '([0 0]))))

(deftest test-conde-4-clauses
  (is (= (into #{}
               (run* [q]
                     (fresh [x y]
                            (digit-4 x)
                            (digit-4 y)
                            (== q [x y]))))
         (into #{}
               '([0 0] [0 1] [0 2] [1 0] [0 3] [1 1] [1 2] [2 0]
                       [1 3] [2 1] [3 0] [2 2] [3 1] [2 3] [3 2] [3 3])))))

;; -----------------------------------------------------------------------------
;; anyo

(defn anyo [q]
  (conde
   [q s#]
   [(anyo q)]))

(deftest test-anyo-1
  (is (= (run 1 [q]
              (anyo s#)
              (== true q))
         (list true))))

(deftest test-anyo-2
  (is (= (run 5 [q]
              (anyo s#)
              (== true q))
         (list true true true true true))))

;; -----------------------------------------------------------------------------
;; divergence

(def f1 (fresh [] f1))

(deftest test-divergence-1
  (is (= '(_0)
         (run 1 [q]
              (conde
               [f1]
               [(== false false)]))
         (run 1 [q]
              (or* [f1 (== false false)])))))

(deftest test-divergence-2
  (is (= '(_0)
         (run 1 [q]
              (conde
               [f1 (== false false)]
               [(== false false)]))
         (run 1 [q]
              (or* [(and* [f1 (== false false)]) (== false false)])))))

(def f2
  (fresh []
         (conde
          [f2 (conde
               [f2]
               [(== false false)])]
          [(== false false)])))

(def f2-function
  (fresh []
         (or* [(and* [f2 (or* [f2 (== false false)])])
               (== false false)])))

(deftest test-divergence-3
  (is (= (run 5 [q] f2)
         (run 5 [q] f2-function)
         '(_0 _0 _0 _0 _0))))

;; -----------------------------------------------------------------------------
;; conda (soft-cut)

(deftest test-conda-1
  (is (= (run* [x]
               (conda
                [(== 'olive x) s#]
                [(== 'oil x) s#]
                [u#]))
         '(olive))))

(deftest test-conda-2
  (is (= (run* [x]
               (conda
                [(== 'virgin x) u#]
                [(== 'olive x) s#]
                [(== 'oil x) s#]
                [u#]))
         '())))

(deftest test-conda-3
  (is (= (run* [x]
               (fresh (x y)
                      (== 'split x)
                      (== 'pea y)
                      (conda
                       [(== 'split x) (== x y)]
                       [s#]))
               (== true x))
         '())))

(deftest test-conda-4
  (is (= (run* [x]
               (fresh (x y)
                      (== 'split x)
                      (== 'pea y)
                      (conda
                       [(== x y) (== 'split x)]
                       [s#]))
               (== true x))
         '(true))))

(defn not-pastao [x]
  (conda
   [(== 'pasta x) u#]
   [s#]))

(deftest test-conda-5
  (is (= (run* [x]
               (conda
                [(not-pastao x)]
                [(== 'spaghetti x)]))
         '(spaghetti))))

;; -----------------------------------------------------------------------------
;; condu (committed-choice)

(comment
  (defn onceo [g]
    (condu
     (g s#)))

  (deftest test-condu-1
    (is (= (run* [x]
                 (onceo (teacupo x)))
           '(tea)))))

(deftest test-condu-2
  (is (= (into #{}
               (run* [r]
                     (conde
                      [(teacupo r) s#]
                      [(== false r) s#])))
         (into #{}
               '(false tea cup)))))

(deftest test-condu-3
  (is (= (into #{}
               (run* [r]
                     (conda
                      [(teacupo r) s#]
                      [(== false r) s#])))
         (into #{} '(tea cup)))))

;; -----------------------------------------------------------------------------
;; copy-term

(deftest test-copy-term-1
  (is (= (run* [q]
               (fresh [a b]
                      (copy-term a b)
                      (== q [a b])))
         '([_0 _1])))
  (is (= (run* [q]
               (fresh [a b]
                      (copy-term `(~a) `(~b))
                      (== q [a b])))
         '([_0 _1])))
  (is (= (run* [q]
               (fresh [a b]
                      (copy-term [a] [b])
                      (== q [a b])))
         '([_0 _1])))
  (is (= (run* [q]
               (fresh [a b c]
                      (copy-term [a] c)
                      (== [b] c)
                      (== q [a b])))
         '([_0 _1])))
  (is (= (run* [q]
               (fresh [a b c d]
                      (== c 1)
                      (copy-term [a c] [b d])
                      (== q [a b d])))
         '([_0 _1 1]))))

;; -----------------------------------------------------------------------------
;; disequality

(deftest test-disequality-1
  (is (= (run* [q]
               (fresh [x]
                      (!= x 1)
                      (== q x)))
         '((_0 :- (!= (_0 1)))))))

(deftest test-disequality-2
  (is (= (run* [q]
               (fresh [x]
                      (== q x)
                      (!= x 1)))
         '((_0 :- (!= (_0 1)))))))

(deftest test-disequality-3
  (is (= (run* [q]
               (fresh [x]
                      (!= x 1)
                      (== x 1)
                      (== q x)))
         ())))

(deftest test-disequality-4
  (is (= (run* [q]
               (fresh [x]
                      (== x 1)
                      (!= x 1)
                      (== q x)))
         ())))

(deftest test-disequality-5
  (is (= (run* [q]
               (fresh [x y]
                      (!= x y)
                      (== x 1)
                      (== y 1)
                      (== q x)))
         ())))

(deftest test-disequality-6
  (is (= (run* [q]
               (fresh [x y]
                      (== x 1)
                      (== y 1)
                      (!= x y)
                      (== q x)))
         ())))

(deftest test-disequality-7
  (is (= (run* [q]
               (fresh [x y]
                      (== x 1)
                      (!= x y)
                      (== y 2)
                      (== q x)))
         '(1))))

(deftest test-disequality-8
  (is (= (run* [q]
               (fresh [x y]
                      (!= [x 2] [y 1])
                      (== x 1)
                      (== y 3)
                      (== q [x y])))
         '([1 3]))))

(deftest test-disequality-9
  (is (= (run* [q]
               (fresh [x y]
                      (== x 1)
                      (== y 3)
                      (!= [x 2] [y 1])
                      (== q [x y])))
         '([1 3]))))

(deftest test-disequality-10
  (is (= (run* [q]
               (fresh [x y]
                      (!= [x 2] [1 y])
                      (== x 1)
                      (== y 2)
                      (== q [x y])))
         ())))

(deftest test-disequality-11
  (is (= (run* [q]
               (fresh [x y]
                      (== x 1)
                      (== y 2)
                      (!= [x 2] [1 y])
                      (== q [x y])))
         ())))

(deftest test-disequality-12
  (is (= (run* [q]
               (fresh [x y z]
                      (!= x y)
                      (== y z)
                      (== x z)
                      (== q x)))
         ())))

(deftest test-disequality-13
  (is (= (run* [q]
               (fresh [x y z]
                      (== y z)
                      (== x z)
                      (!= x y)
                      (== q x)))
         ())))

(deftest test-disequality-14
  (is (= (run* [q]
               (fresh [x y z]
                      (== z y)
                      (== x z)
                      (!= x y)
                      (== q x)))
         ())))

(deftest test-disequality-15
  (is (= (run* [q]
               (fresh [x y]
                      (== q [x y])
                      (!= x 1)
                      (!= y 2)))
         '(([_0 _1] :- (!= (_1 2)) (!= (_0 1)))))))

(deftest test-disequality-16
  (is (= (run* [q]
               (fresh [x y z]
                      (== y [z])
                      (!= [z] x)
                      (== z 'foo)
                      (== x ['foo])))
         '())))

;; the following test is subject to ordering
;; issues due to 1.7 changes, just commenting out for now
#_(deftest test-disequality-17
    (is (= (run* [q]
                 (fresh [x y]
                        (!= [1 x] [y 2])
                        (== q [x y])))
           '(([_0 _1] :- (!= (_1 1) (_0 2))))))
    (is (= (run* [q]
                 (fresh [x y]
                        (!= [x 1] [2 y])))
           '((_0 :- (!= (_1 2) (_2 1)))))))

(deftest test-logic-95-disequality-1
  (is (= (run* [q]
               (fresh [x y w z]
                      (!= x y)
                      (!= w z)
                      (== z y)
                      (== x 'foo)
                      (== y 'foo)))
         ())))

(deftest test-logic-95-disequality-2
  (is (= (run* [q]
               (fresh [x y w z]
                      (!= x [y])
                      (== x ['foo])
                      (== y 'foo)))
         ())))

(deftest test-logic-96-disequality-1
  (is (= (run* [q]
               (fresh [x y z]
                      (!= x [y])
                      (== x [z])
                      (== y 'foo)
                      (== z 'bar)))
         '(_0))))

(deftest test-logic-100-disequality-1
  (is (= (run* [q]
               (fresh [a b]
                      (== q [a b])
                      (!= a q)
                      (== a 1)))
         '([1 _0]))))

(deftest test-logic-100-disequality-2
  (is (= (run* [q]
               (fresh [a b]
                      (!= a q)
                      (== q [a b])))
         '([_0 _1])))
  (is (= (run* [q]
               (fresh [a b]
                      (== q [a b])
                      (!= a q)))
         '([_0 _1]))))

(deftest test-logic-100-disequality-3
  (is (= (run* [q]
               (fresh [x y w z]
                      (== x [1 w])
                      (== y [2 z])
                      (!= x y)))
         '(_0)))
  (is (= (run* [q]
               (fresh [x y w z]
                      (!= x y)
                      (== x [1 w])
                      (== y [2 z])))
         '(_0))))

(deftest test-logic-119-disequality-1
  (is (= (run* [q]
               (!= {1 2 3 4} 'foo))
         '(_0))))

(deftest test-logic-160-disequality
  (is (= (run* [q]
               (fresh [a d]
                      (!= (lcons a d) '(2))
                      (== (lcons a d) '(2))))
         ()))
  (is (= (run* [q]
               (fresh [a d]
                      (!= (lcons a d) '(2))
                      (== a 2)
                      (== d ())))
         ())))

;; -----------------------------------------------------------------------------
;; tabled

(defne arco [x y]
  ([:a :b])
  ([:b :a])
  ([:b :d]))

(def patho
  (tabled [x y]
          (conde
           [(arco x y)]
           [(fresh [z]
                   (arco x z)
                   (patho z y))])))

(deftest test-tabled-1
  (is (= (into #{} (run* [q] (patho :a q)))
         (into #{} '(:b :a :d)))))

(defne arco-2 [x y]
  ([1 2])
  ([1 4])
  ([1 3])
  ([2 3])
  ([2 5])
  ([3 4])
  ([3 5])
  ([4 5]))

(def patho-2
  (tabled [x y]
          (conde
           [(arco-2 x y)]
           [(fresh [z]
                   (arco-2 x z)
                   (patho-2 z y))])))

(deftest test-tabled-2
  (let [r (set (run* [q] (patho-2 1 q)))]
    (is (and (= (count r) 4)
             (= r #{2 3 4 5})))))

;; -----------------------------------------------------------------------------
;; nil in collection

(deftest test-nil-in-coll-1
  (is (= (run* [q]
               (== q [nil]))
         '([nil]))))

(deftest test-nil-in-coll-2
  (is (= (run* [q]
               (== q [1 nil]))
         '([1 nil]))))

(deftest test-nil-in-coll-3
  (is (= (run* [q]
               (== q [nil 1]))
         '([nil 1]))))

(deftest test-nil-in-coll-4
  (is (= (run* [q]
               (== q '(nil)))
         '((nil)))))

(deftest test-nil-in-coll-5
  (is (= (run* [q]
               (== q {:foo nil}))
         '({:foo nil}))))

(deftest test-nil-in-coll-6
  (is (= (run* [q]
               (== q {nil :foo}))
         '({nil :foo}))))

;; -----------------------------------------------------------------------------
;; Unifier

(deftest test-unifier-1
  (is (= (u/unify ['(?x ?y) '(1 2)])
         '(1 2))))

(deftest test-unifier-2
  (is (= (u/unify ['(?x ?y 3) '(1 2 ?z)])
         '(1 2 3))))

(deftest test-unifier-3
  (is (= (u/unify ['[(?x . ?y) 3] [[1 2] 3]])
         '[(1 2) 3])))

(deftest test-unifier-4
  (is (= (u/unify ['(?x . ?y) '(1 . ?z)])
         (lcons 1 '?z))))

(deftest test-unifier-5
  (is (= (u/unify ['(?x 2 . ?y) '(1 2 3 4 5)])
         '(1 2 3 4 5))))

(deftest test-unifier-6
  (is (= (u/unify ['(?x 2 . ?y) '(1 9 3 4 5)])
         nil)))

(deftest test-unifier-7
  (is (= (u/unify ['(?x 2 . ?y) '(1 9 3 4 5)])
         nil)))

(deftest test-unifier-8 ;;nested maps
  (is (= (u/unify ['{:a {:b ?b}} {:a {:b 1}}])
         {:a {:b 1}})))

(deftest test-unifier-9 ;;nested vectors
  (is (= (u/unify ['[?a [?b ?c] :d] [:a [:b :c] :d]])
         [:a [:b :c] :d])))

(deftest test-unifier-10 ;;nested seqs
  (is (= (u/unify ['(?a (?b ?c) :d) '(:a (:b :c) :d)])
         '(:a (:b :c) :d))))

(deftest test-unifier-11 ;;all together now
  (is (= (u/unify ['{:a [?b (?c [?d {:e ?e}])]} {:a [:b '(:c [:d {:e :e}])]}])
         {:a [:b '(:c [:d {:e :e}])]})))

(deftest test-unifier-12
  (is (= (u/unify '[?x 1]) 1)))

;; -----------------------------------------------------------------------------
;; custom var reification

(deftest test-reify-vars-false
  (is (= (-run {:reify-vars false} [q]
               (fresh [x]
                      (== q x)))
         '(x))))

(deftest test-custom-var-reifier-1
  (let [x (lvar 'x)]
    (is (= (-run {:reify-vars (fn [v rs] rs)} [q]
                 (== q x))
           `(~x)))))

;; -----------------------------------------------------------------------------
;; Unifier with constraints

(defnc evenc [x]
  (even? x))

(deftest test-unifier-constraints-1 ;;One var
  (is (= (u/unify {:when {'?a evenc}} ['{:a ?a} {:a 2}])
         {:a 2}))
  (is (= (u/unify {:when {'?a evenc}} ['{:a ?a} {:a 1}])
         nil)))

(deftest test-unifier-constraints-2 ;;Two vars
  (is (= (u/unify {:when {'?a evenc '?b evenc}} ['{:a ?a :b ?b} {:a 2 :b 2}])
         {:a 2 :b 2}))
  (is (= (u/unify {:when {'?a evenc '?b evenc}} ['{:a ?a :b ?b} {:a 1 :b 2}])
         nil)))

(deftest test-unifier-constraints-3
  (is (= (u/unify {:when {'#{?a ?b} evenc}} ['{:a ?a :b ?b} {:a 2 :b 2}])
         {:a 2 :b 2}))
  (is (= (u/unify {:when {'#{?a ?b} evenc}} ['{:a ?a :b ?b} {:a 1 :b 2}])
         nil)))

(defnc div3c [x]
  (zero? (mod x 3)))

(deftest test-unifier-constraints-4
  (is (= (u/unify {:when {'#{?a ?b} [evenc div3c]}} ['{:a ?a :b ?b} {:a 6 :b 12}])
         {:a 6 :b 12}))
  (is (= (u/unify {:when {'#{?a ?b} [evenc div3c]}} ['{:a ?a :b ?b} {:a 2 :b 6}])
         nil)))

(defnc complexc [a b]
  (and (even? a) (zero? (mod b 3))))

(deftest test-unifier-constraints-5
  (is (= (u/unify {:when {'[?a ?b] complexc}} ['{:a ?a :b ?b} {:a 2 :b 3}])
         {:a 2 :b 3}))
  (is (= (u/unify {:when {'[?a ?b] complexc}} ['{:a ?a :b ?b} {:a 2 :b 4}])
         nil)))

(deftest test-unifier-as-1
  (is (= (u/unify {:as '{?x (?y ?z)}} ['?x '(1 2)])))
  (is (= (u/unify {:as '{?x (?y ?z)}} ['(?x) '((1 2))])))
  (is (= (u/unify {:as '{?x (?y ?y)}} '[[?y ?x] [1 (1 1)]])
         '[1 (1 1)])))

;;Anonymous constraints
(deftest test-unifier-anon-constraints-3 ;;One var
  (is (= (u/unify {:when {'?a (fnc [x] (even? x))}} ['{:a ?a} {:a 2}])
         {:a 2}))
  (is (= (u/unify {:when {'?a (fnc [x] (even? x))}} ['{:a ?a} {:a 1}])
         nil)))

(deftest test-binding-map-1
  (is (= (u/unifier ['(?x ?y) '(1 2)])
         '{?x 1 ?y 2})))

(deftest test-binding-map-2
  (is (= (u/unifier ['(?x ?y 3) '(1 2 ?z)])
         '{?x 1 ?y 2 ?z 3})))

(deftest test-binding-map-3
  (is (= (u/unifier ['[(?x . ?y) 3] [[1 2] 3]])
         '{?x 1 ?y (2)})))

(deftest test-binding-map-4
  (is (= (u/unifier ['(?x . ?y) '(1 . ?z)])
         '{?x 1, ?y ?z})))

(deftest test-binding-map-5
  (is (= (u/unifier ['(?x 2 . ?y) '(1 2 3 4 5)])
         '{?x 1 ?y (3 4 5)})))

(deftest test-binding-map-6
  (is (= (u/unifier ['(?x 2 . ?y) '(1 9 3 4 5)])
         nil)))

(deftest test-binding-map-7
  (is (= (u/unifier '[((?x ?y)) ((1 2))])
         '{?x 1 ?y 2})))

(deftest test-binding-map-constraints-1
  (is (= (u/unifier {:when {'?x evenc '?y div3c}} ['(?x ?y) '(2 6)])
         '{?x 2 ?y 6}))
  (is (= (u/unifier {:when {'?x div3c '? evenc}} ['(?x ?y) '(2 6)])
         nil))
  (is (= (u/unifier {:when {'[?x ?y] complexc}} ['(?x ?y) '(2 6)])
         '{?x 2 ?y 6}))
  (is (= (u/unifier {:when {'#{?x ?y} [evenc div3c]}} ['(?x ?y) '(6 12)])
         '{?x 6 ?y 12}))
  (is (= (u/unifier {:when {'#{?x ?y} [evenc div3c]}} ['(?x ?y) '(14 12)])
         nil)))

(deftest test-binding-map-as-1
  (is (= (u/unifier {:as {'?x '(?y ?z)}} '[(?x) ((1 2))])
         '{?x (1 2) ?y 1 ?z 2})))

;; -----------------------------------------------------------------------------
;; Occurs Check

(deftest test-occurs-check-1
  (is (= (run* [q]
               (== q [q]))
         ())))

;; -----------------------------------------------------------------------------
;; Unifications that should fail

(deftest test-unify-fail-1
  (is (= (run* [p] (fresh [a b] (== b ()) (== '(0 1) (lcons a b)) (== p [a b])))
         ())))

(deftest test-unify-fail-2
  (is (= (run* [p] (fresh [a b] (== b '(1)) (== '(0) (lcons a b)) (== p [a b])))
         ())))

(deftest test-unify-fail-3
  (is (= (run* [p] (fresh [a b c d] (== () b) (== '(1) d) (== (lcons a b) (lcons c d)) (== p [a b c d])))
         ())))

;; -----------------------------------------------------------------------------
;; Pattern Matching

(defne pm1 [x y]
  ([:foo :bar]))

(defne pm2 [x y]
  ([_ x]))

(defne pm3 [x y]
  ([_ 'x]))

(defne pm4 [x y]
  ([[h . t] t]))

(defn -test-pm [test-msg rel1 rel2 rel3]
  (testing test-msg
    (is (= (run* [q] (fresh [x y] (== q [x y]) (rel1 x y))) '([:foo :bar])))
    (is (= (run* [q] (fresh [x y] (rel2 x y) (== x y))) '(_0)))
    (is (= (run* [q] (rel3 '(1 2) q)) '((2))))))

(deftest test-pm
  (-test-pm "pattern matching with defne relations" pm1 pm2 pm4))

(deftest test-pm-anonymous
  (-test-pm "pattern matching with anonymous fne relations"
            (fne [x y] ([:foo :bar]))
            (fne [x y] ([_ x]))
            (fne [x y] ([[h . t] t]))))

(deftest test-pm-anonymous-tabled
  (-test-pm "pattern matching with tabled anonymous fne relations"
            (fne [x y] :tabled ([:foo :bar]))
            (fne [x y] :tabled ([_ x]))
            (fne [x y] :tabled ([[h . t] t]))))

(defne form->ast1 [form ast]
  (['(fn ~args . ~body) {:op :fn :args args :body body}]))

(defne form->ast2 [form ast]
  (['(fn [~f . ~rest] . ~body) {:op :fn :f f :rest rest :body body}]))

(deftest test-code-match-1
  (is (= (run* [q]
               (form->ast1 '(fn [x y] (+ x y)) q))
         '({:op :fn :args [x y] :body ((+ x y))})))
  (is (= (run* [q]
               (form->ast2 '(fn [x y] (+ x y)) q))
         '({:op :fn :f x :rest (y) :body ((+ x y))}))))

;; -----------------------------------------------------------------------------
;; Pattern matching functions preserve metadata

(defne ^:tabled dummy
  "Docstring"
  [x l]
  ([_ [x . tail]])
  ([_ [head . tail]]
   (membero x tail)))

(deftest test-metadata-defne
  (is (= (-> #'dummy meta :tabled)
         true))
  (is (= (-> #'dummy meta :doc)
         "Docstring")))

(defn locals-membero [x l]
  (matche [l]
          ([[x . tail]])
          ([[head . tail]]
           (locals-membero x tail))))

(deftest test-matche-with-locals
  (is (= [true] (run* [q]
                      (locals-membero 'foo  [1 2 3 4 5 'foo])
                      (== q true))))
  (is (= [] (run* [q]
                  (locals-membero 'foo  [1 2 3 4 5])
                  (== true q)))))

;; -----------------------------------------------------------------------------
;; Pattern matching inline expression support

;; REMOVED - fn application no longer supported in patterns, list syntax is
;; much more useful when used for matching Clojure source - David

;; (defn s [n] (llist n []))

;; (def zero 0)
;; (def one (s zero))
;; (def two (s one))
;; (def three (s two))
;; (def four (s three))
;; (def five (s four))
;; (def six  (s five))

;; (defn natural-number [x]
;;   (matche [x]
;;     ([zero])
;;     ([(s y)] (natural-number y))))

;; (deftest test-matche-with-expr
;;   (is (= (run* [q] (natural-number one))
;;          '(_0 _0))))

;; -----------------------------------------------------------------------------
;; Pattern matching other data structures

(defne match-map [m o]
  ([{:foo {:bar o}} _]))

(defn test-defne-map []
  (is (= (run* [q]
               (match-map {:foo {:bar 1}} q))
         '(1))))

;; -----------------------------------------------------------------------------
;; Tickets

(deftest test-31-unifier-associative
  (is (= (u/unify ['{:a ?x} '{:a ?y} '{:a 5}])
         {:a 5}))
  (is (= (u/unify ['{:a ?x} '{:a 5} '{:a ?y}])
         {:a 5})))

(deftest test-34-unify-with-metadata
  (is (run* [q]
            (== q (quote ^:haz-meta-daytuhs (form form form))))
      '((^:haz-meta-daytuhs (form form form)))))

(deftest test-42-multiple-run-parameters
  (is (= '[[3 _0 [3 _0]]]
         (run* [x y z]
               (== z [x y])
               (== [x] [3])))))

(deftest test-49-partial-map-unification
  (is (= [1]
         (run* [q]
               (fresh [x]
                      (== {:a 1 :b 2} (partial-map {:a x}))
                      (== q x)))))
  (is (= [1]
         (run* [q]
               (fresh [x]
                      (== (partial-map {:a x}) {:a 1 :b 2})
                      (== q x))))))

(deftest test-73-partial-map-unification
  (is (= (run* [q]
               (fresh [a]
                      (== {:x 1} (partial-map {:a a}))))
         '()))
  (is (= (run* [q]
               (== {:a 1} (partial-map {:a q})))
         '(1))))

(deftest test-75-map-sum-maps-lcons
  (is (= (into #{}
               (run* [q]
                     (fresh [x]
                            (fd/in x (fd/interval 1 3))
                            (== q {:foo x}))))
         (into #{} '({:foo 1} {:foo 2} {:foo 3}))))
  (is (= (into #{}
               (run* [q]
                     (fresh [x y]
                            (fd/in x (fd/interval 1 3))
                            (== q (lcons x y)))))
         (into #{} [(lcons 1 '_0) (lcons 2 '_0) (lcons 3 '_0)]))))

(deftest test-82-nil-lcons-tail
  (is (= (run 1 [q]
              (fresh [a b c]
                     (conso a b c)
                     (== b nil)
                     (== `(~a) c)))
         '(_0))))

(deftest test-85-alias
  (is (= (run* [q]
               (fresh [x y]
                      (predc y even? `even?)
                      (predc x odd? `odd)
                      (== x y)
                      (== x 1)
                      (== q [x y])))
         ())))

(deftest test-77-alias
  (is (= (run 1 [r a b x]
              (== r [a b])
              (fd/in a b x (fd/domain 1 2))
              (fd/< a b)
              (firsto r x))
         '([[1 2] 1 2 1]))))

(deftest test-90-<-diverge
  (is (= (run 1 [a b c d]
              (fd/in a b c d (fd/interval 0 4))
              (fd/< a b)
              (fd/< c d)
              (fd/< d a))
         '([2 3 0 1]))))

(deftest test-103-<=-diverge
  (is (= (into #{}
               (run 2 [a b s p]
                    (fd/in a b (fd/interval 2 99))
                    (fd/>= a b)
                    (fd/+ a b s)
                    (fd/* a b p)))
         (into #{} '([2 2 4 4] [3 2 5 6])))))

(defrecord RecordTest [a b]
  IUninitialized
  (-uninitialized [_]
    (RecordTest. nil nil)))

(deftest test-53-lossy-records
  (is (= (run* [q]
               (== q (RecordTest. 1 2)))
         (list #clojure.core.logic.tests.RecordTest{:a 1, :b 2}))))

(deftest test-111-conda-regression
  (is (= (run* [x]
               (conda
                [succeed
                 (project [x] succeed)
                 (project [x] succeed)]))
         '(_0))))

(deftest test-115-singleton-doms
  (is (= (run* [q]
               (fd/in q (fd/interval 3 3)))
         '(3))))

(def patho-112
  (tabled
   [graph start end]
   (conde
    [(== start end)]
    [(fresh [?via ?vias]
            (project [start graph]
                     (== ?vias  ((:successors graph) start)))
            (membero ?via ?vias)
            (patho-112 graph ?via end))])))

(defn solve-goals [graph curr end goals]
  (all
   (project [goals]
      ;;when there are no more goals we are done
            (conde [(== true
                        (empty? goals))
                    (== curr end)]
        ;;there are still goals left
        ;;solve the first and recursive call
                   [(== false (empty? goals))
                    (fresh [goal tail via]
                           (== goal (first goals))
                           (== tail (rest goals))
                           (project [goal]
                                    (goal graph curr via)
                                    (solve-goals graph via end tail)))]))))

(def foo :foo)
(def bar :bar)
(def baz :baz)
(def quux :quux)

(defn to-node [node]
  (cond
    (= node foo)
    (seq (list bar))
    (= node bar)
    (seq (list baz))
    (= node baz)
    (seq (list quux))))

(def graph {:successors to-node})

(defn test-1 []
  (run* [?result]
        (fresh [?start ?end]
               (== ?start foo)
               (== ?end quux)
               (solve-goals graph ?start ?end
                            (seq (list patho-112
                                       (fn [graph current next]
                                         (all
                                          (== ?result current)
                   ;;(trace-lvars "current" current)
                                          (== current next)))
                                       patho-112))))))

(deftest test-112-tabling
  (is (= (test-1)
         '(:foo :bar :baz :quux))))

(defne lefto
  "x appears to the left of y in collection l."
  [x y l]
  ([_ _ [x . tail]] (membero y tail))
  ([_ _ [_ . tail]] (lefto x y tail)))

(defn rule-1 [answers]
  (fresh [c1 r1 c2 r2]
         (membero [:landon (lvar) c1 r1] answers)
         (membero [:jason (lvar) c2 r2] answers)
         (conde
          [(== r1 7.5)
           (== c2 :mozzarella)]
          [(== r2 7.5)
           (== c1 :mozzarella)])))

(defn rule-2 [answers]
  (membero [(lvar) :fortune :blue-cheese (lvar)] answers))

(defn rule-3 [answers]
  (fresh [s1 s2]
         (== [(lvar) :vogue (lvar) (lvar)] s1)
         (== [(lvar) (lvar) :muenster (lvar)] s2)
         (membero s1 answers)
         (membero s2 answers)
         (!= s1 s2)))

(defn rule-4 [answers]
  (permuteo [[(lvar) :fortune (lvar) (lvar)]
             [:landon (lvar) (lvar) (lvar)]
             [(lvar) (lvar) (lvar) 5]
             [(lvar) (lvar) :mascarpone (lvar)]
             [(lvar) :vogue (lvar) (lvar)]]
            answers))

(defn rule-6 [answers]
  (fresh [r1 r2]
         (membero [(lvar) :cosmopolitan (lvar) r1] answers)
         (membero [(lvar) (lvar) :mascarpone r2] answers)
         (lefto r1 r2 [5 6 7 7.5 8.5])))

(defn rule-9 [answers]
  (fresh [r1 r2]
         (membero [(lvar) :time (lvar) r1] answers)
         (membero [:landon (lvar) (lvar) r2] answers)
         (lefto r1 r2 [5 6 7 7.5 8.5])))

(defn rule-0 [answers]
  (fresh [s]
         (== [:amaya (lvar) (lvar) (lvar)] s)
         (membero s answers)))

;; The following test has been disabled because it fails with the new
;; version of membero, but that isn't due to any defect in
;; membero. The test needs to be rewritten.

#_(deftest test-116-constraint-store-migrate
    (is (= (first
            (run 1 [answers]
                 (rule-0 answers)
                 (rule-1 answers)
                 (rule-2 answers)
                 (rule-3 answers)
                 (rule-4 answers)
                 (rule-6 answers)
                 (rule-9 answers)))
           '([:amaya :fortune :blue-cheese _0]
             [:landon :cosmopolitan :muenster 7.5]
             [:jason :vogue :mozzarella 5]
             [_1 :time :mascarpone 5]
             [_2 :vogue :mascarpone 8.5]))))

(deftest test-71-simple-unifier-reify-vars
  (is (= (u/unify '[(?x) (?x) (1)])
         '(1))))

(deftest test-36-unifier-behavior
  (is (= (u/unifier ['(?x ?y) '(?y ?x)])
         '{?x ?y})))

(deftest test-108-recursive-features
  (is (= (run* [x y]
               (featurec x {:foo {:bar y}})
               (== x {:foo {:bar 1}}))
         '([{:foo {:bar 1}} 1])))
  (is (= (run* [x y]
               (== x {:foo {:bar 1}})
               (featurec x {:foo {:bar y}}))
         '([{:foo {:bar 1}} 1])))
  (is (= (run* [x y]
               (featurec x {:foo {:bar y}})
               (== x {:foo {:bar 1 :woz 2}}))
         '([{:foo {:bar 1 :woz 2}} 1])))
  (is (= (run* [x y]
               (== x {:foo {:bar 1 :woz 2}})
               (featurec x {:foo {:bar y}}))
         '([{:foo {:bar 1 :woz 2}} 1])))
  (is (= (run* [x y]
               (== x {:foo {:baz 1}})
               (featurec x {:foo {:bar y}}))
         '()))
  (is (= (run* [x y]
               (featurec x {:foo {:bar y}})
               (== x {:foo {:baz 1}}))
         '())))

(deftest test-disjoint-logic-124
  (is (false? (fd/-disjoint?
               (fd/interval 2 4)
               (fd/multi-interval 1 (fd/interval 3 4)))))
  (is (false? (fd/-disjoint?
               (fd/multi-interval 1 (fd/interval 3 4))
               (fd/interval 2 4)))))

(deftest test-arch-friends-problem-logic-124
  (let [expected [{:wedges 2,
                   :flats 4,
                   :pumps 1,
                   :sandals 3,
                   :foot-farm 2,
                   :heels-in-a-hand-cart 4,
                   :shoe-palace 1,
                   :tootsies 3}]]
    (is (= expected
           (run* [q]
                 (fresh [wedges flats pumps sandals
                         ff hh sp tt pumps+1]
                        (fd/in wedges flats pumps sandals
                               ff hh sp tt pumps+1 (fd/interval 1 4))
                        (fd/distinct [wedges flats pumps sandals])
                        (fd/distinct [ff hh sp tt])
                        (fd/== flats hh)
                        (fd/+ pumps 1 pumps+1)
                        (fd/!= pumps+1 tt)
                        (fd/== ff 2)
                        (fd/+ sp 2 sandals)
                        (== q {:wedges wedges
                               :flats flats
                               :pumps pumps
                               :sandals sandals
                               :foot-farm ff
                               :heels-in-a-hand-cart hh
                               :shoe-palace sp
                               :tootsies tt})))))))

(deftest test-126-times-plus
  (is (= (set
          (run* [q]
                (fresh [x y p]
                       (fd/in x y (fd/interval 1 38))
                       (fd/* x y p)
                       (fd/+ p 2 40)
                       (== q [x y]))))
         #{[1 38] [38 1] [2 19] [19 2]})))

(deftest test-simplefd-in-last
  (is (= (run* [q]
               (fresh [x y z p0 p1]
                      (== q [x y])
                      (fd/+ x y 9)
                      (fd/* x 2 p0)
                      (fd/* y 4 p1)
                      (fd/+ p0 p1 24)
                      (fd/in x y z (fd/interval 0 9))))
         '([6 3]))))

(deftest test-logic-132-recursive-featurec
  (is (= (run* [x y]
               (featurec x {:a {:b 1}})
               (== y {:b 1})
               (== x {:a y}))
         '([{:a {:b 1}} {:b 1}])))
  (is (= (run* [x y]
               (featurec x {:a {:b 1}})
               (== x {:a y})
               (== y {:b 1}))
         '([{:a {:b 1}} {:b 1}])))
  (is (= (run* [x y]
               (== x {:a y})
               (== y {:b 1})
               (featurec x {:a {:b 1}}))
         '([{:a {:b 1}} {:b 1}]))))

(deftest test-137-oom
  (is (= (let [vs (repeatedly 20 l/lvar)]
           (first
            (run 1 [q]
                 (== q vs)
                 (everyg (fn [v] (fd/in v (fd/interval 1 2))) vs))))
         (take 20 (repeat 1))))
  (is (= (first
          (run 1 [q]
               (fresh [x1 x2 x3 x4 x5 x6 x7 x8 x9
                       x10 x11 x12 x13 x14 x15
                       x16 x17 x18 x19 x20]
                      (== q [x1 x2 x3 x4 x5 x6 x7 x8 x9
                             x10 x11 x12 x13 x14 x15
                             x16 x17 x18 x19 x20])
                      (fd/in x1 x2 x3 x4 x5 x6 x7 x8 x9
                             x10 x11 x12 x13 x14 x15
                             x16 x17 x18 x19 x20
                             (fd/interval 1 2)))))
         (take 20 (repeat 1)))))

(deftest test-145-partial-map
  (is (= (run* [x y]
               (== y {:baz "woz"})
               (== (partial-map {:foo x}) {:foo y}))
         '([{:baz "woz"} {:baz "woz"}]))))

;; =============================================================================
;; cKanren

(deftest test-pair
  (is (= (pair 1 2)
         (pair 1 2))))

(deftest test-dom-1
  (let [x (lvar 'x)
        s ((fd/dom x 1) empty-s)]
    (is (= (:s s) {x 1}))))

#_(deftest test-dom-2
    (let [x (lvar 'x)
          s ((fd/dom x (fd/interval 1 10)) empty-s)]
      (is (= (:ws s) {x (fd/interval 1 10)}))))

#_(deftest test-dom-3
    (let [x (lvar 'x)
          s ((composeg
              (fd/dom x (fd/interval 1 10))
              (fd/dom x (fd/interval 3 6))) empty-s)]
      (is (= (:ws s) {x (fd/interval 3 6)}))))

#_(deftest test-dom-4
    (let [x (lvar 'x)
          s ((composeg
              (fd/dom x (fd/interval 1 5))
              (fd/dom x (fd/interval 5 9))) empty-s)]
      (is (= (:s s) {x 5}))
      (is (= (:ws s) {}))))

(deftest test-keep-before-1
  (is (= (fd/-keep-before (fd/interval 1 10) 5)
         (fd/interval 1 4)))
  (is (= (fd/-keep-before (fd/interval 5 10) 5)
         nil))
  (is (= (fd/-keep-before (fd/interval 5 10) 6)
         5))
  (is (= (fd/-keep-before (fd/interval 5 10) 10)
         (fd/interval 5 9))))

(deftest test-drop-before-1
  (is (= (fd/-drop-before (fd/interval 5 10) 4)
         (fd/interval 5 10)))
  (is (= (fd/-drop-before (fd/interval 1 10) 5)
         (fd/interval 5 10)))
  (is (= (fd/-drop-before (fd/interval 5 10) 5)
         (fd/interval 5 10)))
  (is (= (fd/-drop-before (fd/interval 5 10) 6)
         (fd/interval 6 10)))
  (is (= (fd/-drop-before (fd/interval 5 10) 10)
         10))
  (is (= (fd/-drop-before (fd/interval 5 10) 11)
         nil)))

(deftest test-keep-before-2
  (is (= (fd/-keep-before 1 3)
         1))
  (is (= (fd/-keep-before 1 2)
         1))
  (is (= (fd/-keep-before 1 1)
         nil)))

(deftest test-drop-before-2
  (is (= (fd/-drop-before 1 3)
         nil))
  (is (= (fd/-drop-before 1 2)
         nil))
  (is (= (fd/-drop-before 1 1)
         1))
  (is (= (fd/-drop-before 1 0)
         1)))

(deftest test-drop-before-mi-1
  (is (= (fd/-drop-before (fd/multi-interval 2 4) (fd/-lb 3))
         4)))

(deftest test-keep-before-mi-2
  (is (= (fd/-keep-before (fd/multi-interval 2 4) (fd/-lb 3))
         2)))

(deftest test-singleton-interval
  (is (= (fd/interval 1 1) 1)))

(deftest test-interval-<
  (is (fd/interval-< (fd/interval 1 10) (fd/interval 11 20)))
  (is (fd/interval-< 1 (fd/interval 11 20))))

(deftest test-interval->
  (is (fd/interval-> (fd/interval 11 20) (fd/interval 1 10)))
  (is (fd/interval-> (fd/interval 11 20) 1)))

(deftest test-member?-ss-1
  (is (true? (fd/-member? 1 1))))

(deftest test-member?-ss-2
  (is (false? (fd/-member? 1 2))))

(deftest test-disjoint?-ss-1
  (is (false? (fd/-disjoint? 1 1))))

(deftest test-disjoint?-ss-2
  (is (true? (fd/-disjoint? 1 2))))

(deftest test-difference-ss-1
  (is (= (fd/-difference 1 1)
         nil)))

(deftest test-difference-ss-2
  (is (= (fd/-difference 1 2)
         1)))

(deftest test-intersection-ss-1
  (is (= (fd/-intersection 1 1)
         1)))

(deftest test-intersection-ss-2
  (is (= (fd/-intersection 1 2)
         nil)))

(deftest test-member?-is-1
  (is (true? (fd/-member? (fd/interval 1 10) 1))))

(deftest test-member?-si-1
  (is (true? (fd/-member? 1 (fd/interval 1 10)))))

(deftest test-disjoint?-is-1
  (is (true? (fd/-disjoint? (fd/interval 1 10) 11))))

(deftest test-disjoint?-si-1
  (is (true? (fd/-disjoint? 11 (fd/interval 1 10)))))

(deftest test-intersection-is-1
  (is (= (fd/-intersection (fd/interval 1 6) 1)
         1)))

(deftest test-intersection-si-1
  (is (= (fd/-intersection 1 (fd/interval 1 6))
         1)))

(deftest test-difference-is-1
  (let [mi (fd/-difference (fd/interval 1 10) 5)]
    (is (= (first (fd/-intervals mi)) (fd/interval 1 4)))
    (is (= (second (fd/-intervals mi)) (fd/interval 6 10)))))

(deftest test-difference-si-1
  (let [mi (fd/-difference 5 (fd/interval 1 10))]
    (is (= (first (fd/-intervals mi)) (fd/interval 1 4)))
    (is (= (second (fd/-intervals mi)) (fd/interval 6 10)))))

(deftest test-intersection-ii-1
  (is (= (fd/-intersection (fd/interval 1 6) (fd/interval 5 10))
         (fd/interval 5 6))))

(deftest test-intersection-ii-2
  (is (= (fd/-intersection (fd/interval 5 10) (fd/interval 1 6))
         (fd/interval 5 6))))

(deftest test-difference-ii-1
  (is (= (fd/-difference (fd/interval 1 6) (fd/interval 5 10))
         (fd/interval 1 4))))

(deftest test-difference-ii-2
  (is (= (fd/-difference (fd/interval 1 4) (fd/interval 5 10))
         (fd/interval 1 4))))

(deftest test-difference-ii-3
  (is (= (fd/-difference (fd/interval 5 10) (fd/interval 1 4))
         (fd/interval 5 10))))

(deftest test-difference-ii-4
  (is (= (fd/-difference (fd/interval 1 10) (fd/interval 1 10))
         nil)))

(deftest test-difference-ii-5
  (is (= (fd/-difference (fd/interval 2 9) (fd/interval 1 10))
         nil)))

(deftest test-disjoint?-ii-1
  (is (false? (fd/-disjoint? (fd/interval 1 6) (fd/interval 5 10))))
  (is (false? (fd/-disjoint? (fd/interval 5 10) (fd/interval 1 6))))
  (is (true? (fd/-disjoint? (fd/interval 1 6) (fd/interval 10 16))))
  (is (true? (fd/-disjoint? (fd/interval 10 16) (fd/interval 1 6)))))

(deftest test-member?-mimi-1
  (is (false? (fd/-member? 20 (fd/multi-interval (fd/interval 1 3) 5 (fd/interval 7 10)))))
  (is (false? (fd/-member? (fd/multi-interval (fd/interval 1 3) 5 (fd/interval 7 10)) 20))))

(deftest test-disjoint?-mimi-1
  (is (true? (fd/-disjoint? 20 (fd/multi-interval (fd/interval 1 3) 5 (fd/interval 7 10)))))
  (is (true? (fd/-disjoint? (fd/multi-interval (fd/interval 1 3) 5 (fd/interval 7 10)) 20)))
  (is (true? (fd/-disjoint? (fd/interval 20 30) (fd/multi-interval (fd/interval 1 3) 5 (fd/interval 7 10)))))
  (is (true? (fd/-disjoint? (fd/multi-interval (fd/interval 1 3) 5 (fd/interval 7 10)) (fd/interval 20 30)))))

(deftest test-equals-mi
  (let [mi0 (fd/multi-interval (fd/interval 1 4) (fd/interval 6 10))
        mi1 (fd/multi-interval (fd/interval 1 4) (fd/interval 6 10))]
    (is (= mi0 mi1))))

;; -----------------------------------------------------------------------------
;; MultiFd/IntervalFD Intersection

(deftest test-intersection-mimi-1
  (let [mi0 (fd/multi-interval (fd/interval 1 4) (fd/interval 6 10))
        mi1 (fd/multi-interval (fd/interval 9 13) (fd/interval 17 20))]
    (is (= (fd/-intersection mi0 mi1) (fd/interval 9 10)))
    (is (= (fd/-intersection mi1 mi0) (fd/interval 9 10)))))

(deftest test-intersection-mimi-2
  (let [mi0 (fd/multi-interval (fd/interval 1 4) (fd/interval 6 10))]
    (is (= (fd/-intersection mi0 7) 7))
    (is (= (fd/-intersection 7 mi0) 7))))

;; |-----|
;;   |-----|
(deftest test-intersection-mimi-3
  (let [mi0 (fd/multi-interval (fd/interval 1 4) (fd/interval 7 10))]
    (is (= (fd/-intersection mi0 (fd/interval 3 8))
           (fd/multi-interval (fd/interval 3 4) (fd/interval 7 8))))))

;; |-----|
;;  |---|
(deftest test-intersection-mimi-4
  (let [mi0 (fd/multi-interval (fd/interval 1 4) (fd/interval 7 10))
        mi1 (fd/multi-interval (fd/interval 2 3) (fd/interval 6 9))]
    (is (= (fd/-intersection mi0 mi1)
           (fd/multi-interval (fd/interval 2 3) (fd/interval 7 9))))))

;;   |-----|
;; |-----|
(deftest test-intersection-mimi-5
  (let [mi0 (fd/multi-interval (fd/interval 4 8) (fd/interval 12 16))
        mi1 (fd/multi-interval (fd/interval 1 5) (fd/interval 7 15))]
    (is (= (fd/-intersection mi0 mi1)
           (fd/multi-interval (fd/interval 4 5) (fd/interval 7 8) (fd/interval 12 15))))))

;;  |---|
;; |-----|
(deftest test-intersection-mimi-6
  (let [mi0 (fd/multi-interval (fd/interval 1 3) (fd/interval 5 6) (fd/interval 8 10))
        mi1 (fd/multi-interval (fd/interval 1 3) (fd/interval 4 7) (fd/interval 8 10))]
    (is (= (fd/-intersection mi0 mi1)
           (fd/multi-interval (fd/interval 1 3) (fd/interval 5 6) (fd/interval 8 10))))))

;; |---|  |---|
;; |-------|
(deftest test-intersection-mimi-7
  (let [mi0 (fd/multi-interval (fd/interval 1 4) (fd/interval 7 10))]
    (is (= (fd/-intersection mi0 (fd/interval 1 8))
           (fd/multi-interval (fd/interval 1 4) (fd/interval 7 8))))))

;; |--------| |--|
;; |---|  |-------|
(deftest test-intersection-mimi-8
  (let [mi0 (fd/multi-interval (fd/interval 1 7) (fd/interval 9 10))
        mi1 (fd/multi-interval (fd/interval 1 3) (fd/interval 6 11))]
    (is (= (fd/-intersection mi0 mi1)
           (fd/multi-interval (fd/interval 1 3) (fd/interval 6 7) (fd/interval 9 10))))))

;; -----------------------------------------------------------------------------
;; MultiFd/IntervalFD Fd/-Difference

;; |---| |---|
;;         |---| |---|
(deftest test-difference-mimi-1
  (let [mi0 (fd/multi-interval (fd/interval 1 4) (fd/interval 6 10))
        mi1 (fd/multi-interval (fd/interval 9 13) (fd/interval 17 20))]
    (is (= (fd/-difference mi0 mi1)
           (fd/multi-interval (fd/interval 1 4) (fd/interval 6 8))))))

;; |---|  |---|
;;         N
(deftest test-difference-mis-1
  (let [mi0 (fd/multi-interval (fd/interval 1 4) (fd/interval 7 10))]
    (is (= (fd/-difference mi0 8)
           (fd/multi-interval (fd/interval 1 4) 7 (fd/interval 9 10))))))

;;       N
;; |---|   |---|
(deftest test-difference-smi-2
  (let [mi0 (fd/multi-interval (fd/interval 1 4) (fd/interval 6 10))]
    (is (= (fd/-difference 5 mi0) 5))))

;; |---|   |---|
;;   |-------|
;;
;;   |-------|
;; |---|   |---|
(deftest test-difference-mii-1
  (let [mi0 (fd/multi-interval (fd/interval 1 4) (fd/interval 7 10))]
    (is (= (fd/-difference mi0 (fd/interval 3 8))
           (fd/multi-interval (fd/interval 1 2) (fd/interval 9 10))))
    (is (= (fd/-difference (fd/interval 3 8) mi0)
           (fd/interval 5 6)))))

;; |---|  |---|
;; |-------| |----|
(deftest test-difference-mimi-2
  (let [mi0 (fd/multi-interval (fd/interval 1 4) (fd/interval 7 10))
        mi1 (fd/multi-interval (fd/interval 1 8) (fd/interval 10 13))]
    (is (= (fd/-difference mi0 mi1) 9))))

;;  |----| |-------|
;; |----|    |---|
(deftest test-difference-mimi-3
  (let [mi0 (fd/multi-interval (fd/interval 3 6) (fd/interval 9 15))
        mi1 (fd/multi-interval (fd/interval 1 4) (fd/interval 10 12))]
    (is (= (fd/-difference mi0 mi1)
           (fd/multi-interval (fd/interval 5 6) 9 (fd/interval 13 15))))))

;;   |---|     |---|
;; |-----| |-|
(deftest test-difference-mimi-4
  (let [mi0 (fd/multi-interval (fd/interval 3 6) (fd/interval 15 20))
        mi1 (fd/multi-interval (fd/interval 1 6) (fd/interval 10 13))]
    (is (= (fd/-difference mi0 mi1)
           (fd/interval 15 20)))))

(deftest test-fd-1
  (let [d (fd/domain 1 2 3)]
    (is (= (fd/-lb d) 1))
    (is (= (fd/-ub d) 3))))

(deftest test-normalize-intervals-1
  (let [d (fd/domain 1 2 3)]
    (is (= (fd/normalize-intervals (fd/-intervals d))
           [(fd/interval 1 3)]))))

(deftest test-normalize-intervals-2
  (let [d (fd/multi-interval (fd/interval 1 4) 5 (fd/interval 6 10))]
    (is (= (fd/normalize-intervals (fd/-intervals d))
           [(fd/interval 1 10)]))))

(deftest test-dom-interval-and-number-1
  (is (= (run* [q]
               (fd/dom q (fd/interval 1 10))
               (== q 1))
         '(1)))
  (is (= (run* [q]
               (== q 1)
               (fd/dom q (fd/interval 1 10)))
         '(1))))

(deftest test-dom-interval-and-number-2
  (is (= (run* [q]
               (fd/dom q (fd/interval 1 10))
               (== q 11))
         '()))
  (is (= (run* [q]
               (== q 11)
               (fd/dom q (fd/interval 1 10)))
         '())))

(deftest test-dom-many-intervals-1
  (is (= (run* [q]
               (fd/dom q (fd/interval 1 100))
               (fd/dom q (fd/interval 30 60))
               (fd/dom q (fd/interval 50 55))
               (== q 51))
         '(51)))
  (is (= (run* [q]
               (fd/dom q (fd/interval 1 100))
               (fd/dom q (fd/interval 30 60))
               (fd/dom q (fd/interval 50 55))
               (== q 56))
         '())))

(deftest test-process-dom-1
  (let [x (lvar 'x)
        s ((fd/process-dom x 1 1) empty-s)]
    (is (= (walk s x) 1))))

(deftest test-process-dom-2
  (let [x (lvar 'x)
        s ((fd/process-dom x (fd/interval 1 10) (fd/interval 1 10)) empty-s)]
    (is (= (fd/get-dom s x) (fd/interval 1 10)))))

(deftest test-process-dom-3
  (let [x (lvar 'x)
        s ((fd/dom x (fd/interval 1 10)) empty-s)]
    (is (= (fd/get-dom s x) (fd/interval 1 10)))))

(deftest test-in-1
  (let [x (lvar 'x)
        y (lvar 'y)
        f ((fd/in x y (fd/interval 1 10)) empty-s)
        s (f)]
    (is (= (fd/get-dom s x) (fd/interval 1 10)))
    (is (= (fd/get-dom s y) (fd/interval 1 10)))))

(deftest test-make-fdc-prim-1
  (let [u (lvar 'u)
        w (lvar 'w)
        c (fd/==c u w)
        c' (-step c empty-s)]
    (is (= (var-rands empty-s c)
           [u w]))
    (is (= (-rator c)
           'clojure.core.logic.fd/==))
    (is (not (-runnable? c')))
    (is (not (-entailed? c')))))

(deftest test-make-fdc-prim-2
  (let [u (lvar 'u)
        v 1
        w (lvar 'w)
        c (fd/+c u v w)
        c' (-step c empty-s)]
    (is (= (var-rands empty-s c)
           [u w]))
    (is (= (-rator c)
           'clojure.core.logic.fd/+))
    (is (not (-runnable? c')))
    (is (not (-entailed? c')))))

(deftest test-entailed-1
  (let [c (fd/+c 1 2 3)
        c' (-step c empty-s)]
    (is (true? (-entailed? c')))))

(deftest test-make-fdc-1
  (let [u (lvar 'u)
        v 1
        w (lvar 'w)
        c (fd/+c u v w)
        c' (-step c empty-s)]
    (is (= (var-rands empty-s c)
           [u w]))
    (is (= (-rator c)
           `fd/+))
    (is (not (-runnable? c')))
    (is (not (-entailed? c')))))

(deftest test-addc-1
  (let [u (lvar 'u)
        v 1
        w (lvar 'w)
        c (fd/+c u v w)
        cs (addc (make-cs) empty-s c)
        sc (first (constraints-for cs empty-s u ::l/fd))]
    (is (= (id sc) 0))
    (is (= (count (:km cs)) 2))
    (is (= (count (:cm cs)) 1))))

(deftest test-addc-2
  (let [u (lvar 'u)
        v 1
        w (lvar 'w)
        c0 (fd/+c u v w)
        x (lvar 'x)
        c1 (fd/+c w v x)
        cs  (-> (make-cs)
                (addc empty-s c0)
                (addc empty-s c1))
        sc0 (get (:cm cs) 0)
        sc1 (get (:cm cs) 1)]
    (is (= (id sc0) 0))
    (is (= (id sc1) 1))
    (is (= (count (:km cs)) 3))
    (is (= (count (:cm cs)) 2))))

(deftest test-addcg
  (let [u (lvar 'u)
        v 1
        w (lvar 'w)
        c (fd/+c u v w)
        s ((addcg c) empty-s)]
    (is (= (count (:km (:cs s))) 2))
    (is (= (count (:cm (:cs s))) 1))))

(deftest test-purge-c
  (let [u (lvar 'u)
        v 1
        w (lvar 'w)
        c (fd/+c u v w)
        s ((addcg c) empty-s)
        c (first (constraints-for (:cs s) s u ::l/fd))
        s (-> s
              (ext-run-cs u 1)
              (ext-run-cs w 2))]
    (is (zero? (count (:km (:cs s)))))
    (is (zero? (count (:cm (:cs s)))))))

(deftest test-=fd-1
  (let [x (lvar 'x)
        y (lvar 'y)
        s ((composeg
            (fd/dom x (fd/interval 1 6))
            (fd/dom y (fd/interval 5 10))) empty-s)
        s ((fd/== x y) s)
        cs (:cs s)]
    (is (= 2 (count (:km (:cs s))))) ;; works
    (is (= 3 (count (:cm (:cs s)))))
    (is (= (fd/get-dom s x) (fd/interval 5 6)))
    (is (= (fd/get-dom s y) (fd/interval 5 6)))))

(deftest test-multi-interval-1
  (let [mi (fd/multi-interval (fd/interval 1 3) (fd/interval 7 10))]
    (is (= 1 (fd/-lb mi)))
    (is (= 10 (fd/-ub mi)))))

(deftest test-run-constraints*
  (is (= (run-constraints* [] [] ::l/subst) s#)))

(deftest test-drop-one-1
  (is (= (:s (fd/-drop-one (fd/domain 1 2 3)))
         #{2 3})))

(deftest test-drop-one-2
  (is (= (fd/-drop-one (fd/domain 1))
         nil)))

(deftest test-drop-one-3
  (is (= (fd/-drop-one 1)
         nil)))

(deftest test-drop-one-4
  (is (= (fd/-drop-one (fd/interval 1 10))
         (fd/interval 2 10))))

(deftest test-drop-one-5
  (is (= (fd/-drop-one (fd/interval 1 1))
         nil)))

(deftest test-drop-one-6
  (is (= (fd/-drop-one (fd/multi-interval (fd/interval 1 10) (fd/interval 15 20)))
         (fd/multi-interval (fd/interval 2 10) (fd/interval 15 20)))))

(deftest test-to-vals-1
  (is (= (fd/to-vals 1) '(1))))

(deftest test-to-vals-2
  (is (= (fd/to-vals (fd/domain 1 2 3)) '(1 2 3))))

(deftest test-to-vals-3
  (is (= (fd/to-vals (fd/interval 1 10))
         '(1 2 3 4 5 6 7 8 9 10))))

(deftest test-to-vals-4
  (is (= (fd/to-vals (fd/multi-interval (fd/interval 1 5) (fd/interval 7 10)))
         '(1 2 3 4 5 7 8 9 10))))

(deftest test-to-vals-5
  (is (= (fd/to-vals (fd/multi-interval (fd/interval 1 5) 7 (fd/interval 9 12)))
         '(1 2 3 4 5 7 9 10 11 12))))

(deftest test-map-sum-1
  (let [x (lvar 'x)
        s ((fd/dom x (fd/interval 1 10)) empty-s)]
    (is (= (take 10
                 (solutions s x
                            ((fd/map-sum (fn [v] (ext-run-csg x v)))
                             (fd/to-vals (fd/interval 1 10)))))
           '(1 2 3 4 5 6 7 8 9 10)))))

(deftest test-force-ans-1
  (let [x (lvar 'x)
        s ((fd/dom x (fd/interval 1 10)) empty-s)]
    (is (= (take 10
                 (solutions s x
                            (force-ans x)))
           '(1 2 3 4 5 6 7 8 9 10)))))

(deftest test-force-ans-2
  (let [x (lvar 'x)
        s ((fd/dom x (fd/interval 1 10)) empty-s)]
    (is (= (take 10
                 (solutions s x
                            (force-ans [x])))
           '(1 2 3 4 5 6 7 8 9 10)))))

(deftest test-force-ans-3
  (let [x (lvar 'x)
        s ((fd/dom x (fd/multi-interval (fd/interval 1 4) (fd/interval 6 10)))
           empty-s)]
    (is (= (take 10
                 (solutions s x
                            (force-ans x)))
           '(1 2 3 4 6 7 8 9 10)))))

(deftest test-verify-all-bound-1
  (let [x (lvar 'x)
        y (lvar 'y)
        s ((composeg
            (fd/dom x (fd/interval 1 10))
            (fd/dom y (fd/interval 1 10))) empty-s)]
    (is (nil? (verify-all-bound s [x y])))))

(deftest test-verify-all-bound-2
  (let [x (lvar 'x)
        y (lvar 'y)
        s ((fd/dom x (fd/interval 1 10)) empty-s)]
    (is (thrown? Exception (verify-all-bound s [x y])))))

(deftest test-enforce-constraints-1
  (let [x (lvar 'x)
        s ((fd/dom x (fd/interval 1 3)) empty-s)]
    (is (= (solutions s x
                      (enforce-constraints x))
           '(1 2 3)))))

(deftest test-reifyg-1
  (let [x (lvar 'x)
        y (lvar 'y)
        s ((composeg
            (fd/dom x (fd/interval 1 10))
            (fd/dom y (fd/interval 1 5))) empty-s)
        s ((fd/== x y) s)]
    (is (= (take* ((reifyg x) s))
           '(1 2 3 4 5)))))

(deftest test-process-interval-smaller-1
  (let [x (lvar 'x)
        s ((composeg
            (fd/dom x (fd/interval 1 10))
            (fd/dom x (fd/interval 2 10))) empty-s)]
    (is (= (fd/get-dom s x)
           (fd/interval 2 10)))))

(deftest test-boundary-interval-1
  (is (= (fd/-difference (fd/interval 1 10) 1)
         (fd/interval 2 10))))

(deftest test-boundary-interval-2
  (is (= (fd/-difference (fd/interval 1 10) 10)
         (fd/interval 1 9))))

(deftest test-process-imi-1
  (let [x (lvar 'x)
        s ((composeg
            (fd/dom x (fd/interval 2 10))
            (fd/dom x (fd/multi-interval (fd/interval 1 4) (fd/interval 6 10))))
           empty-s)]
    (is (= (fd/get-dom s x)
           (fd/multi-interval (fd/interval 2 4) (fd/interval 6 10))))))

;; -----------------------------------------------------------------------------
;; cKanren

(deftest test-root-var-1
  (let [x (lvar 'x)
        y (lvar 'y)
        s (-> empty-s
              (ext-no-check x 1)
              (ext-no-check y x))]
    (is (= (root-var s y) x))))

(deftest test-ckanren-1
  (is (= (into #{}
               (run* [q]
                     (fresh [x]
                            (fd/in x (fd/interval 1 3))
                            (== q x))))
         (into #{} '(1 2 3)))))

(deftest test-ckanren-2
  (is (= (into #{}
               (run* [q]
                     (fresh [x y z]
                            (fd/in x z (fd/interval 1 5))
                            (fd/in y (fd/interval 3 5))
                            (fd/+ x y z)
                            (== q [x y z]))))
         (into #{} '([1 3 4] [2 3 5] [1 4 5])))))

(deftest test-ckanren-3
  (is (= (into #{}
               (run* [q]
                     (fresh [x y]
                            (fd/in x y (fd/interval 1 3))
                            (fd/== x y)
                            (== q [x y]))))
         (into #{} '([1 1] [2 2] [3 3])))))

(deftest test-ckanren-4
  (is (true?
       (every? (fn [[x y]] (not= x y))
               (run* [q]
                     (fresh [x y]
                            (fd/in x y (fd/interval 1 10))
                            (fd/!= x y)
                            (== q [x y])))))))

(deftest test-ckanren-5
  (is (= (into #{}
               (run* [q]
                     (fresh [x y]
                            (fd/in x y (fd/interval 1 3))
                            (== x 2)
                            (fd/!= x y)
                            (== q [x y]))))
         (into #{} '([2 1] [2 3])))))

(deftest test-ckanren-6
  (is (= (run* [q]
               (fresh [x]
                      (fd/in x (fd/interval 1 3))
                      (fd/+ x 1 x)
                      (== q x)))
         '())))

(deftest test-ckanren-7
  (is (= (run* [q]
               (fresh [x]
                      (fd/in x (fd/interval 1 3))
                      (fd/+ x x x)))
         '())))

(deftest test-ckanren-8
  (is (= (into #{}
               (run* [q]
                     (fresh [x y]
                            (fd/in x y (fd/interval 1 3))
                            (fd/<= x y)
                            (== q [x y]))))
         (into #{} '([1 1] [1 2] [2 2] [1 3] [3 3] [2 3])))))

(deftest test-ckanren-9
  (is (= (into #{}
               (run* [q]
                     (fresh [x y]
                            (fd/in x y (fd/interval 1 3))
                            (fd/< x y)
                            (== q [x y]))))
         (into #{} '([1 2] [2 3] [1 3])))))

(defn subgoal [x]
  (fresh [y]
         (== y x)
         (fd/+ 1 y 3)))

(deftest test-ckanren-10
  (is (= (run* [q]
               (fresh [x]
                      (fd/in x (fd/interval 1 10))
                      (subgoal x)
                      (== q x)))
         '(2))))

(deftest test-list-sorted
  (is (true? (fd/list-sorted? < [1 2 3])))
  (is (true? (fd/list-sorted? < [1 3 5])))
  (is (false? (fd/list-sorted? < [1 1 3])))
  (is (false? (fd/list-sorted? < [1 5 4 1]))))

(deftest test-with-id
  (let [x (lvar 'x)
        y (lvar 'y)
        n* (sorted-set 1 3 5)
        c (with-id (fd/-distinctc x #{y} (conj n* 7)) 1)]
    (is (= (id c) 1))))

(deftest test-distinct
  (is (= (into #{}
               (run* [q]
                     (fresh [x y z]
                            (fd/in x y z (fd/interval 1 3))
                            (fd/distinct [x y z])
                            (== q [x y z]))))
         (into #{} '([1 2 3] [1 3 2] [2 1 3] [2 3 1] [3 1 2] [3 2 1])))))

(deftest test-=fd-2
  (is (= (into #{}
               (run* [q]
                     (fresh [a b]
                            (fd/in a b (fd/interval 1 3))
                            (fd/== a b)
                            (== q [a b]))))
         (into #{} '([1 1] [2 2] [3 3])))))

(deftest test-fd-!=-1
  (is (= (into #{}
               (run* [q]
                     (fresh [a b]
                            (fd/in a b (fd/interval 1 3))
                            (fd/!= a b)
                            (== q [a b]))))
         (into #{} '([1 2] [1 3] [2 1] [2 3] [3 1] [3 2])))))

(deftest test-fd-<-1
  (is (= (into #{}
               (run* [q]
                     (fresh [a b c]
                            (fd/in a b c (fd/interval 1 3))
                            (fd/< a b) (fd/< b c)
                            (== q [a b c]))))
         (into #{} '([1 2 3])))))

(deftest test-fd-<-2
  (is (= (into #{}
               (run* [q]
                     (fresh [x y z]
                            (fd/in x y z (fd/interval 1 10))
                            (fd/+ x y z)
                            (fd/< x y)
                            (== z 10)
                            (== q [x y z]))))
         (into #{} '([1 9 10] [2 8 10] [3 7 10] [4 6 10])))))

(deftest test-fd->-1
  (is (= (into #{}
               (run* [q]
                     (fresh [x y z]
                            (fd/in x y z (fd/interval 1 10))
                            (fd/+ x y z)
                            (fd/> x y)
                            (== z 10)
                            (== q [x y z]))))
         (into #{} '([6 4 10] [7 3 10] [8 2 10] [9 1 10])))))

(deftest test-fd-<=-1
  (is (= (run* [q]
               (fresh [x y]
                      (== x 3)
                      (fd/in y (fd/multi-interval 2 4))
                      (fd/<= x y)
                      (== q y)))
         '(4))))

(deftest test-fd->=-1
  (is (= (run* [q]
               (fresh [x y]
                      (== x 3)
                      (fd/in y (fd/multi-interval 2 4))
                      (fd/>= x y)
                      (== q y)))
         '(2))))

(deftest test-fd-*-1
  (is (= (into #{}
               (run* [q]
                     (fresh [n m]
                            (fd/in n m (fd/interval 1 10))
                            (fd/* n 2 m)
                            (== q [n m]))))
         (into #{} '([1 2] [2 4] [3 6] [4 8] [5 10])))))

(deftest test-fd-*-2
  (is (= (into #{}
               (run* [q]
                     (fresh [n m]
                            (fd/in n m (fd/interval 1 10))
                            (fd/* n m 10)
                            (== q [n m]))))
         (into #{} '([1 10] [2 5] [5 2] [10 1])))))

;; -----------------------------------------------------------------------------
;; CLP(Tree)

#_(deftest test-recover-vars
    (let [x (lvar 'x)
          y (lvar 'y)
          s (-> empty-s
                (ext-no-check x 1)
                (ext-no-check y 2))]
      (is (= (recover-vars (:l s))
             #{x y}))))

#_(deftest test-prefix-s
    (let [x (lvar 'x)
          y (lvar 'y)
          s empty-s
          sp (-> s
                 (ext-no-check x 1)
                 (ext-no-check y 2))
          p (prefix-s sp s)]
      (is (= p
             (list (pair y 2) (pair x 1))))
      (is (= (-> p meta :s) sp))))

#_(deftest test-prefix-subsumes?
    (let [x (lvar 'x)
          y (lvar 'y)
          z (lvar 'z)
          s empty-s
          sp (-> s
                 (ext-no-check x 1)
                 (ext-no-check y 2))
          p (prefix-s sp s)]
      (is (true? (prefix-subsumes? p (list (pair x 1)))))
      (is (true? (prefix-subsumes? p (list (pair y 2)))))
      (is (false? (prefix-subsumes? p (list (pair z 3)))))))

(deftest test-remc
  (let [x (lvar 'x)
        y (lvar 'y)
        z (lvar 'z)
        c (fd/+c x y z)
        cs (addc (make-cs) empty-s c)
        cp (get (:cm cs) 0)
        cs (remc cs empty-s cp)]
    (is (= (:km cs) {}))
    (is (= (:cm cs) {}))))

(deftest test-treec-id-1
  (let [x (lvar 'x)
        y (lvar 'y)
        c (with-id (!= x y) 0)]
    (is (zero? (id c)))))

(deftest test-tree-constraint?
  (let [x (lvar 'x)
        y (lvar 'y)
        c (!=c (list (pair x 1) (pair y 2)))
        cs (addc (make-cs) empty-s c)]
    (is (tree-constraint? ((:cm cs) 0)))
    (is (= (into #{} (keys (:km cs)))
           #{x y}))))

(deftest test-prefix-protocols
  (let [x (lvar 'x)
        y (lvar 'y)
        c (!=c (list (pair x 1) (pair y 2)))
        c (-with-prefix c (list (pair x 1)))]
    (is (= (-prefix c)
           (list (pair x 1))))))

(deftest test-!=-1
  (let [x (lvar 'x)
        y (lvar 'y)
        s ((!= x y) empty-s)]
    (is (= (-prefix ((:cm (:cs s)) 0)) {x y}))))

(deftest test-!=-2
  (let [x (lvar 'x)
        y (lvar 'y)
        s ((!= x y) empty-s)
        s ((== x y) s)]
    (is (= s nil))))

;; NOTE: we removed -relevant? protocol fn used for purging individual
;; vars from the constraint store. This may return but as a finer grained
;; protocol IRelevantLVar or some such

#_(deftest test-!=-3
    (let [x (lvar 'x)
          y (lvar 'y)
          s ((!= x y) empty-s)
          s ((== x 1) s)
          s ((== y 2) s)]
      (is (empty? (:cm (:cs s))))
      (is (empty? (:km (:cs s))))))

(deftest test-!=-4
  (let [x (lvar 'x)
        y (lvar 'y)
        s ((== x 1) empty-s)
        s ((== y 2) s)
        s ((!= x y) s)]
    (is (empty? (:cm (:cs s))))
    (is (empty? (:km (:cs s))))))

(deftest test-!=-5
  (let [x (lvar 'x)
        y (lvar 'y)
        s ((== x 1) empty-s)
        s ((!= x y) s)
        s ((== y 2) s)]
    (is (empty? (:cm (:cs s))))
    (is (empty? (:km (:cs s))))))

(deftest test-!=-6
  (let [x (lvar 'x)
        y (lvar 'y)
        s ((!= x 1) empty-s)]
    (is (= (-prefix ((:cm (:cs s)) 0)) {x 1}))))

#_(deftest test-normalize-store
    (let [x (lvar 'x)
          y (lvar 'y)
          c (!=c (list (pair x 1)))
          sc (!=c (list (pair x 1) (pair y 2)))
          cs (addc (make-cs) empty-s c)]))

(deftest test-multi-constraints-1
  (is (= (run* [q]
               (fresh [x y z]
                      (fd/in x y z (fd/interval 1 3))
                      (!= z 3)
                      (fd/+ x y z)
                      (== q [x y z])))
         '([1 1 2]))))

(deftest test--fd-1
  (is (= (run* [q]
               (fd/in q (fd/interval 1 10))
               (fd/- 4 q 1))
         '(3)))
  (is (= (run* [q]
               (fd/in q (fd/interval 1 10))
               (fd/- 4 2 q))
         '(2))))

(deftest test-quot-1
  (is (= (run* [q]
               (fd/in q (fd/interval 1 10))
               (fd/quot 4 2 q))
         '(2))))

;; =============================================================================
;; fd/eq

(deftest test-fd-eq-1
  (is (= (run* [q]
               (fresh [x y]
                      (fd/in x y (fd/interval 0 9))
                      (fd/eq
                       (= (+ x y) 9)
                       (= (+ (* x 2) (* y 4)) 24))
                      (== q [x y])))
         '([6 3]))))

(deftest test-fd-eq-2
  (is (= (run* [q]
               (fresh [s e n d m o r y]
                      (== q [s e n d m o r y])
                      (fd/in s e n d m o r y (fd/interval 0 9))
                      (fd/distinct [s e n d m o r y])
                      (fd/!= m 0) (fd/!= s 0)
                      (fd/eq
                       (= (+ (* 1000 s) (* 100 e) (* 10 n) d
                             (* 1000 m) (* 100 o) (* 10 r) e)
                          (+ (* 10000 m) (* 1000 o) (* 100 n) (* 10 e) y)))))
         '([9 5 6 7 1 0 8 2]))))

(deftest test-fd-eq-3
  (is (= (run* [q]
               (fresh [x y]
                      (fd/in x y (fd/interval 1 20))
                      (fd/eq
                       (= (+ x y) 11)
                       (= (- (* 3 x) y) 5))
                      (== q [x y])))
         '([4 7]))))

(deftest test-fd-distinct-1
  (is (= (run 1 [q]
              (fresh [x y]
                     (fd/distinct q)
                     (== q [x y])
                     (== x 1)
                     (== y 1)))
         ())))

(deftest test-logic-62-fd
  (is (= (run 1 [q]
              (fresh [x y a b]
                     (fd/distinct [x y])
                     (== [x y] [a b])
                     (== q [a b])
                     (== a 1)
                     (== b 1)))
         ()))
  (is (= (run 1 [q]
              (fresh [x y a b]
                     (== [x y] [a b])
                     (== q [a b])
                     (== a 1)
                     (== b 1)
                     (fd/distinct [x y])))
         ())))

(deftest test-distincto-1
  (is (= (run 1 [q]
              (fresh [x y a b]
                     (distincto q)
                     (== [x y] [a b])
                     (== q [a b])
                     (== x 1)
                     (== y 2)))
         '([1 2]))))

(deftest test-eq-vars-1
  (let [x0 (lvar 'x)
        x1 (with-meta x0 {:foo 'bar})
        s  (unify empty-s x0 x1)]
    (is (= s empty-s))))

(deftest test-logic-81-fd
  (is (= (run* [q]
               (fresh [x y]
                      (== q x)
                      (fd/distinct [q y])
                      (== y x)
                      (fd/in q x y (fd/interval 1 3))))
         ()))
  (is (= (run* [q]
               (fresh [x y z]
                      (== q x)
                      (== y z)
                      (fd/distinct [q y])
                      (fd/distinct [q x])
                      (== z q)
                      (fd/in q x y z (fd/interval 1 3))))
         ())))

;; =============================================================================
;; predc

(deftest test-predc-1
  (is (= (run* [q]
               (predc q number? `number?))
         '((_0 :- clojure.core/number?))))
  (is (= (run* [q]
               (predc q number? `number?)
               (== q 1))
         '(1)))
  (is (= (run* [q]
               (== q 1)
               (predc q number? `number?))
         '(1)))
  (is (= (run* [q]
               (predc q number? `number?)
               (== q "foo"))
         ()))
  (is (= (run* [q]
               (== q "foo")
               (predc q number? `number?))
         ()))
  (is (= (run* [q]
               (fresh [x]
                      (predc q number? `number?)
                      (== q x)
                      (== x "foo")))
         ()))
  (is (= (run* [q]
               (fresh [x]
                      (== q x)
                      (predc q number? `number?)
                      (== x "foo")))
         ())))

(deftest test-predc-sans-pform
  (is (= (run* [q]
               (predc q symbol?))
         (list (list '_0 ':- symbol?)))))

(deftest test-predc-custom-reify-1
  (is (= (run* [q]
               (predc q number? (fn [c v r a] `(~'num ~(walk* r (walk* a q))))))
         '((_0 :- (num _0)))))
  (is (= (run* [q]
               (fresh [x y]
                      (predc x number? (fn [c v r a] `(~'num ~(walk* r (walk* a x)))))
                      (== [x y] q)))
         '(([_0 _1] :- (num _0)))))
  (is (= (run* [q]
               (predc q number? (fn [c v r a] nil)))
         '(_0))))

;; =============================================================================
;; Real cKanren programs

(defn not-adjacento [x y]
  (fresh [f]
         (fd/in f (fd/interval 1 5))
         (conde
          [(fd/+ x f y) (fd/< 1 f)]
          [(fd/+ y f x) (fd/< 1 f)])))

(defn dinesmanfd []
  (run* [baker cooper fletcher miller smith :as vs]
        (fd/distinct vs)
        (everyg #(fd/in % (fd/interval 1 5)) vs)
        (fd/!= baker 5) (fd/!= cooper 1)
        (fd/!= fletcher 5) (fd/!= fletcher 1)
        (fd/< cooper miller)
        (not-adjacento smith fletcher)
        (not-adjacento fletcher cooper)))

(deftest test-dinesmandfd
  (is (= (dinesmanfd) '([3 2 4 5 1]))))

(defne subchecko [w sl r o n]
  ([_ () _ _ _]
   (fresh [hr]
          (fd/in hr (fd/interval 1 n))
          (matche [r o]
                  ([[hr . _] [w . r]] (fd/+ hr 1 w))
                  ([() [w . r]]))))
  ([_ [hsl . rsl] _ _ _]
   (fresh [w-hsl w+hsl o0 o1 nw]
          (fd/in hsl w-hsl w+hsl (fd/interval 1 n))
          (fd/+ hsl w-hsl w) (fd/+ hsl w w+hsl)
          (subchecko w-hsl rsl r  o0 n)
          (subchecko w     rsl o0 o1 n)
          (subchecko w+hsl rsl o1 o  n))))

(defne checko [ws sl r n]
  ([() _ [a . _] a])
  ([[w . wr] _ _ _]
   (fresh [nsl nr]
          (subchecko w sl r nr n)
          (conso w sl nsl)
          (checko wr nsl nr n))))

(defn matches [n]
  (run 1 [a b c d]
       (fd/in a b c d (fd/interval 1 n))
       (fd/distinct [a b c d])
       (== a 1)
       (fd/<= a b) (fd/<= b c) (fd/<= c d)
       (fd/eq (= (+ a b c d) n))
       (checko [a b c d] () () n)))

(deftest test-matches
  (is (= (matches 40) '([1 3 9 27]))))

(defn get-square [rows x y]
  (for [x (range x (+ x 3))
        y (range y (+ y 3))]
    (get-in rows [x y])))

(defn init [vars hints]
  (if (seq vars)
    (let [hint (first hints)]
      (all
       (if-not (zero? hint)
         (== (first vars) hint)
         succeed)
       (init (next vars) (next hints))))
    succeed))

(defn ->rows [xs]
  (->> xs (partition 9) (map vec) (into [])))

(defn ->cols [rows]
  (apply map vector rows))

(defn ->squares [rows]
  (for [x (range 0 9 3)
        y (range 0 9 3)]
    (get-square rows x y)))

(defn sudokufd [hints]
  (let [vars (repeatedly 81 lvar)
        rows (->rows vars)
        cols (->cols rows)
        sqs  (->squares rows)]
    (run-nc 1 [q]
            (== q vars)
            (distribute q ::l/ff)
            (everyg #(fd/in % (fd/domain 1 2 3 4 5 6 7 8 9)) vars)
            (init vars hints)
            (everyg fd/distinct rows)
            (everyg fd/distinct cols)
            (everyg fd/distinct sqs))))

(defn verify [vars]
  (let [rows (->rows vars)
        cols (->cols rows)
        sqs  (->squares rows)
        verify-group (fn [group]
                       (every? #(= (->> % (into #{}) count) 9)
                               group))]
    (and (verify-group rows)
         (verify-group cols)
         (verify-group sqs))))

(def easy0
  [0 0 3  0 2 0  6 0 0
   9 0 0  3 0 5  0 0 1
   0 0 1  8 0 6  4 0 0

   0 0 8  1 0 2  9 0 0
   7 0 0  0 0 0  0 0 8
   0 0 6  7 0 8  2 0 0

   0 0 2  6 0 9  5 0 0
   8 0 0  2 0 3  0 0 9
   0 0 5  0 1 0  3 0 0])

(deftest test-sudokufd
  (is (-> (sudokufd easy0) first verify)))

(defn safefd []
  (run* [c1 c2 c3 c4 c5 c6 c7 c8 c9 :as vs]
        (everyg #(fd/in % (fd/interval 1 9)) vs)
        (fd/distinct vs)
        (fd/eq
         (= (- c4 c6) c7)
         (= (* c1 c2 c3) (+ c8 c9))
         (< (+ c2 c3 c6) c8)
         (< c9 c8))
        (project [vs]
                 (everyg (fn [[v n]] (fd/!= v n))
                         (map vector vs (range 1 10))))))

(deftest test-safefd
  (is (= (safefd)
         '([4 3 1 8 9 2 6 7 5]))))

;; =============================================================================
;; Feature Constraints

(deftest test-featurec-1
  (is (= (run* [q]
               (featurec q {:foo 1}))
         '((_0 :- (clojure.core.logic/featurec _0 {:foo 1})))))
  (is (= (run* [q]
               (featurec q {:foo 1})
               (== q {:foo 1 :bar 2}))
         '({:foo 1 :bar 2})))
  (is (= (run* [q]
               (featurec q {:foo 1})
               (== q {:bar 2}))
         ()))
  (is (= (run* [q]
               (fresh [x]
                      (featurec x {:foo q})
                      (== x {:foo 1})))
         '(1))))

;; =============================================================================
;; Negation as failure

(deftest test-naf-1
  (is (= (into #{}
               (run* [q]
                     (membero q '(a b c))
                     (nafc == q 'b)))
         '#{a c}))
  (is (= (into #{}
               (run* [q]
                     (nafc == q 'b)
                     (membero q '(a b c))))
         '#{a c})))

(deftest test-naf-2
  (is (= (into #{}
               (run* [x y]
                     (fd/in x y (fd/interval 1 5))
                     (fd/< x y)
                     (nafc fd/+ x y 5)))
         (into #{}
               (for [x (range 1 6)
                     y (range 1 6)
                     :when (and (< x y)
                                (not (= (+ x y) 5)))]
                 [x y]))))
  (is (= (into #{}
               (run* [x y]
                     (nafc fd/+ x y 5)
                     (fd/< x y)
                     (fd/in x y (fd/interval 1 5))))
         (into #{}
               (for [x (range 1 6)
                     y (range 1 6)
                     :when (and (< x y)
                                (not (= (+ x y) 5)))]
                 [x y])))))

(deftest test-naf-3
  (is (= (into #{}
               (run* [q]
                     (fresh [x]
                            (membero q [:a x :c])
                            (nafc == q :b))))
         #{:a :c ['_0 :- ['clojure.core.logic/nafc == '_0 :b]]})))

(deftest test-naf-4
  (is (= (run* [q]
               (fresh [x]
                      (== x {:bar 1})
                      (nafc featurec x {:foo 1})))
         '(_0)))
  (is (= (run* [q]
               (fresh [x]
                      (== x {:foo 1})
                      (nafc featurec x {:foo 1})))
         '())))

(deftest test-naf-5
  (is (= (run* [q]
               (membero q '(:a :b :c :d))
               (nafc membero q '(:a :b :c)))
         '(:d)))
  (is (= (run* [q]
               (nafc membero q '(:a :b :c))
               (membero q '(:a :b :c :d)))
         '(:d))))

;; =============================================================================
;; Deep Constraints

(defn is-number? [x]
  (if-not (tree-term? x)
    (number? x)
    true))

(deftest test-treec-1
  (is (= (run* [q]
               (treec q #(predc % is-number?) 'is-number?)
               (fresh [x y]
                      (== q [x [2 3 y]])
                      (== x 1)))
         '(([1 [2 3 _0]] :- (clojure.core.logic/fixc _0 is-number?)))))
  (is (= (run* [q]
               (treec q #(predc % is-number?) 'is-number?)
               (fresh [x y]
                      (== q [x [2 3 y]])
                      (== x 1)
                      (== y 'foo)))
         ()))
  (is (= (run* [q]
               (treec q #(predc % is-number?) 'is-number?)
               (fresh [z]
                      (== q {:x {:y z}})))
         '(({:x {:y _0}} :- (clojure.core.logic/fixc _0 is-number?)))))
  (is (= (run* [q]
               (treec q #(predc % is-number?) 'is-number?)
               (fresh [z]
                      (== q {:x {:y z}})
                      (== z 1)))
         '({:x {:y 1}})))
  (is (= (run* [q]
               (treec q #(predc % is-number?) 'is-number?)
               (fresh [z]
                      (== q {:x {:y z}})
                      (== z 'foo)))
         ()))
  (is (= (run* [q]
               (treec q #(predc % is-number?) 'is-number?)
               (fresh [x]
                      (== q (llist 1 2 x))))
         [[(llist 1 2 '_0) ':- '(clojure.core.logic/fixc _0 is-number?)]]))
  (is (= (run* [q]
               (treec q #(predc % is-number?) 'is-number?)
               (fresh [x]
                      (== q (llist 1 2 x))
                      (== x '(3))))
         '((1 2 3))))
  (is (= (run* [q]
               (treec q #(predc % is-number?) 'is-number?)
               (fresh [x]
                      (== q (llist 1 2 x))
                      (== x '(foo))))
         ())))

(deftest test-treec-custom-reify-1
  (is (= (run* [q]
               (fresh [x]
                      (treec q #(predc % is-number?)
                             (fn [c _ v r a]
                               `(~'hashc ~v ~(-reify a x r))))))
         '((_0 :- (hashc _0 _1))))))

;; =============================================================================
;; Entanglement

(deftest test-entanglement-add-dom-1
  (let [x (lvar 'x)
        y (lvar 'y)
        s (-> empty-s
              (entangle x y)
              (add-dom x ::l/fd (fd/domain 1 2 3)))]
    (is (= (get-dom s y ::l/fd) (fd/domain 1 2 3)))))

(deftest test-entanglement-add-dom-2
  (let [x (lvar 'x)
        y (lvar 'y)
        s (-> empty-s
              (entangle x y)
              (add-dom y ::l/fd (fd/domain 1 2 3)))]
    (is (= (get-dom s x ::l/fd) (fd/domain 1 2 3)))))

(deftest test-entanglement-add-dom-3
  (let [x (lvar 'x)
        y (lvar 'y)
        z (lvar 'z)
        s (-> empty-s
              (entangle x y)
              (entangle y z)
              (add-dom x ::l/fd (fd/domain 1 2 3)))]
    (is (= (get-dom s z ::l/fd) (fd/domain 1 2 3)))))

(deftest test-entanglement-add-dom-one-root-1
  (let [x (lvar 'x)
        y (lvar 'y)
        z (lvar 'z)
        s (-> empty-s
              (entangle y x)
              (entangle z x)
              (add-dom x ::l/fd (fd/domain 1 2 3)))]
    (is (= (get-dom s y ::l/fd) (fd/domain 1 2 3)))
    (is (= (get-dom s z ::l/fd) (fd/domain 1 2 3)))))

(deftest test-entanglement-add-dom-one-root-2
  (let [x (lvar 'x)
        y (lvar 'y)
        z (lvar 'z)
        s (-> empty-s
              (entangle y x)
              (entangle z x)
              (add-dom y ::l/fd (fd/domain 1 2 3)))]
    (is (= (get-dom s x ::l/fd) (fd/domain 1 2 3)))
    (is (= (get-dom s z ::l/fd) (fd/domain 1 2 3)))))

(deftest test-entanglement-add-dom-one-root-3
  (let [x (lvar 'x)
        y (lvar 'y)
        z (lvar 'z)
        s (-> empty-s
              (entangle y x)
              (entangle z x)
              (add-dom z ::l/fd (fd/domain 1 2 3)))]
    (is (= (get-dom s x ::l/fd) (fd/domain 1 2 3)))
    (is (= (get-dom s y ::l/fd) (fd/domain 1 2 3)))))

(deftest test-entanglement-add-dom-4
  (let [x (lvar 'x)
        y (lvar 'y)
        z (lvar 'z)
        s (-> empty-s
              (entangle x y)
              (entangle y z)
              (add-dom z ::l/fd (fd/domain 1 2 3)))]
    (is (= (get-dom s x ::l/fd) (fd/domain 1 2 3)))))

(deftest test-entanglement-add-dom-root-var-1
  (let [x (lvar 'x)
        y (lvar 'y)
        z (lvar 'z)
        s (-> empty-s
              (unify x y)
              (entangle x z)
              (add-dom z ::l/fd (fd/domain 1 2 3)))]
    (is (= (get-dom s x ::l/fd) (fd/domain 1 2 3)))))

(deftest test-entanglement-add-dom-root-var-2
  (let [x (lvar 'x)
        y (lvar 'y)
        z (lvar 'z)
        s (-> empty-s
              (unify y x)
              (entangle x z)
              (add-dom z ::l/fd (fd/domain 1 2 3)))]
    (is (= (get-dom s x ::l/fd) (fd/domain 1 2 3)))))

(deftest test-entanglement-update-dom-1
  (let [x (lvar 'x)
        y (lvar 'y)
        s (-> empty-s
              (entangle x y)
              (update-dom x ::l/nom (fnil (fn [d] (conj d :foo)) #{})))]
    (is (= (get-dom s y ::l/nom) #{:foo}))))

(deftest test-entanglement-update-dom-2
  (let [x (lvar 'x)
        y (lvar 'y)
        s (-> empty-s
              (entangle x y)
              (update-dom y ::l/nom (fnil (fn [d] (conj d :foo)) #{})))]
    (is (= (get-dom s x ::l/nom) #{:foo}))))

(deftest test-entanglement-update-dom-3
  (let [x (lvar 'x)
        y (lvar 'y)
        z (lvar 'z)
        s (-> empty-s
              (entangle x y)
              (entangle y z)
              (update-dom x ::l/nom (fnil (fn [d] (conj d :foo)) #{})))]
    (is (= (get-dom s z ::l/nom) #{:foo}))))

(deftest test-entanglement-update-dom-4
  (let [x (lvar 'x)
        y (lvar 'y)
        z (lvar 'z)
        s (-> empty-s
              (entangle x y)
              (entangle y z)
              (update-dom z ::l/nom (fnil (fn [d] (conj d :foo)) #{})))]
    (is (= (get-dom s x ::l/nom) #{:foo}))))

(deftest test-entanglement-fd-in-1
  (let [x (lvar 'x)
        y (lvar 'y)
        s (-> empty-s (entangle x y))
        s (((fd/in x (fd/domain 1 2 3)) s))]
    (is (= (get-dom s x ::l/fd) (fd/domain 1 2 3)))))

;; =============================================================================
;; conjo

(deftest test-conjo-1
  (is (= (run* [p q]
               (conjo p 2 q)
               (== p [1]))
         '([[1] [1 2]])))
  (is (= (run* [p q]
               (== p [1])
               (conjo p 2 q))
         '([[1] [1 2]])))
  (is (= (run* [p q]
               (conjo p 2 q)
               (== q [1 2]))
         '([[1] [1 2]])))
  (is (= (run* [p q]
               (== q [1 2])
               (conjo p 2 q))
         '([[1] [1 2]])))
  (is (= (run* [p q]
               (== p {:foo :bar})
               (conjo p [:baz :woz] q))
         '([{:foo :bar} {:foo :bar :baz :woz}])))
  (is (= (run* [p q]
               (conjo p [:baz :woz] q)
               (== p {:foo :bar}))
         '([{:foo :bar} {:foo :bar :baz :woz}])))
  (is (= (set (run* [p q]
                    (conjo p [:baz :woz] q)
                    (== q {:foo :bar :baz :woz})))
         ;; p had no :baz, or had one that conj overwrote
         #{[{:foo :bar} {:foo :bar :baz :woz}]
           [{:foo :bar :baz '_0} {:foo :bar :baz :woz}]}))
  (is (= (set (run* [p q]
                    (== q {:foo :bar :baz :woz})
                    (conjo p [:baz :woz] q)))
         ;; p had no :baz, or had one that conj overwrote
         #{[{:foo :bar} {:foo :bar :baz :woz}]
           [{:foo :bar :baz '_0} {:foo :bar :baz :woz}]}))
  (is (= (run* [p q]
               (conjo p [:baz :woz] q)
               (== q {:foo :bar}))
         '()))
  (is (= (run* [p q]
               (== q {:foo :bar})
               (conjo p [:baz :woz] q))
         '()))
  ;; (is (= (run* [q]
  ;;          (conjo q [:baz :woz] {:foo :bar :baz :woz})
  ;;          (== q {:foo :bar :baz :woz}))
  ;;        '()))
  )

;; =============================================================================
;; Implementation Specific Tests - Subject To Change

(deftest test-attrs-1
  (let [x (lvar 'x)
        s (add-attr empty-s x :foo 'bar)]
    (is (= (get-attr s x :foo) 'bar))))

(deftest test-attrs-2
  (let [x (lvar 'x)
        s (ext-no-check empty-s x 1)
        s (add-attr s x :foo 'bar)
        s (add-attr s x :baz 'woz)]
    (is (= (get-attr s x :foo) 'bar))
    (is (= (get-attr s x :baz) 'woz))))

(deftest test-attrs-3
  (let [x (lvar 'x)
        s (ext-no-check empty-s x 1)
        s (add-attr s x :foo 'bar)
        s (add-attr s x :baz 'woz)
        s (rem-attr s x :foo)]
    (is (= (get-attr s x :foo) nil))))

(deftest test-root-1
  (let [x (lvar 'x)
        s (ext-no-check empty-s x 1)]
    (is (= (root-var s x) x))
    (is (= (root-val s x) 1))))

(deftest test-root-2
  (let [x (lvar 'x)
        s (add-attr empty-s x :foo 'bar)]
    (is (subst-val? (root-val s x)))))

(deftest test-root-3
  (let [x (lvar 'x)
        y (lvar 'y)
        s (-> empty-s
              (ext-no-check x 1)
              (ext-no-check y x))]
    (is (= (root-var s y) x))))

(deftest test-ext-run-cs-1
  (let [x (lvar 'x)
        s (ext-no-check empty-s x (subst-val ::l/unbound))
        s (add-attr s x ::l/fd (fd/domain 1 2 3))
        s (ext-run-cs s x 1)]
    (is (= (root-val s x) 1))
    (is (= (walk s x) 1))))

(deftest test-update-dom-1
  (let [x (lvar 'x)
        s (add-dom empty-s x ::nom '[(swap a b)])
        s (update-dom s x ::nom (fn [d] (conj d '(swap x y))))]
    (is (= (get-dom s x ::nom) '[(swap a b) (swap x y)]))))

(deftest test-update-dom-2
  (let [x (lvar 'x)
        s (update-dom empty-s x ::nom (fnil (fn [d] (conj d '(swap x y))) []))]
    (is (= (get-dom s x ::nom) '[(swap x y)]))))

;; LOGIC-161

(deftest test-logic-161
  (is
   (= (into {}
            (run* [q]
                  (fresh [a b]
                         (fd/in a b (fd/interval 0 10))
                         (fd/eq (= 4 (* (- a b) 2)))
                         (== q [a b]))))

      (into {}
            (run* [q]
                  (fresh [a b]
                         (fd/in a b (fd/interval 0 10))
                         (fd/eq (= 2 (- a b)))
                         (== q [a b])))))))

;; LOGIC-118

(deftest test-logic-118-prep-lvar-no-tail
  (let [[[xprepped]] (u/prep '([?x]))]
    (is (lvar? xprepped))))

(deftest test-logic-118-prep-lvar-with-tail
  (let [result (u/prep '([?x] . ?foo))
        [head] (lfirst result)]
    (is (lvar? head))))

;; =============================================================================
;; LMap - Relational Maps

(defn- lm
  "An open map as it appears in a reified answer."
  [entries rest]
  (clojure.core.logic.LMap. entries rest -1))

;; -----------------------------------------------------------------------------
;; lmapo

(deftest test-lmapo-destructure
  (is (= (run* [x r]
               (lmapo {:a 1 :b 2} {:a x} r))
         '([1 {:b 2}]))))

(deftest test-lmapo-build
  (is (= (run* [m]
               (lmapo m {:a 1} {:b 2}))
         '({:a 1 :b 2}))))

(deftest test-lmapo-open
  (is (= (run* [m]
               (fresh [r]
                      (lmapo m {:a 1} r)))
         [(lm {:a 1} '_0)])))

(deftest test-lmapo-key-missing
  (is (= (run* [x r]
               (lmapo {:b 2} {:a x} r))
         '())))

(deftest test-lmapo-rest-repeating-key-fails
  (is (= (run* [m]
               (fresh [r]
                      (lmapo m {:a 1} r)
                      (== r {:a 2})))
         '())))

(deftest test-lmapo-rest-repeating-key-nested-fails
  (is (= (run* [q]
               (fresh [m r]
                      (lmapo m {:a 1} r)
                      (== q [m])
                      (== r {:a 2})))
         '())))

(deftest test-lmapo-rest-closed-reifies-as-map
  (is (= (run* [m]
               (fresh [r]
                      (lmapo m {:a 1} r)
                      (== r {})))
         '({:a 1}))))

(deftest test-lmapo-unbound-key
  (is (= (run* [k x]
               (lmapo {:a 1} {k x} {}))
         '([:a 1])))
  (is (= (set (run* [k x]
                    (fresh [r]
                           (lmapo {:a 1 :b 2} {k x} r))))
         #{[:a 1] [:b 2]})))

(deftest test-lmapo-rest-under-conda
  (is (= (run* [q]
               (fresh [m r x]
                      (lmapo m {:a 1} r)
                      (== x [m])
                      (conda
                       [(== r {:a 2}) (== q :first)]
                       [(== q :second)])))
         '(:second))))

;; -----------------------------------------------------------------------------
;; unification of open maps

(deftest test-lmap-open-matches-larger-map
  (is (= (run* [r]
               (fresh [m]
                      (lmapo m {:a 1} r)
                      (== m {:a 1 :b 2})))
         '({:b 2}))))

(deftest test-lmap-open-key-missing-from-closed-fails
  (is (= (run* [m]
               (fresh [r x]
                      (lmapo m {:a 1 :c x} r)
                      (== m {:a 1 :b 2})))
         '())))

(deftest test-lmap-same-rest-different-keys-fail
  (is (= (run* [q]
               (fresh [m1 m2 r]
                      (lmapo m1 {:a 1} r)
                      (lmapo m2 {:b 2} r)
                      (== m1 m2)))
         '())))

(deftest test-lmap-two-open-share-rest
  (is (= (run* [m]
               (fresh [r1 r2]
                      (lmapo m {:a 1} r1)
                      (lmapo m {:b 2} r2)))
         [(lm {:a 1 :b 2} '_0)])))

(deftest test-lmap-two-open-then-closed
  (is (= (run* [m]
               (fresh [r1 r2]
                      (lmapo m {:a 1} r1)
                      (lmapo m {:b 2} r2)
                      (== r1 {:b 2})))
         '({:a 1 :b 2}))))

(deftest test-lmap-conflicting-values-fail
  (is (= (run* [m]
               (fresh [r1 r2]
                      (lmapo m {:a 1} r1)
                      (lmapo m {:a 2} r2)))
         '())))

(deftest test-lmap-nested-values-reified
  (is (= (run* [m]
               (fresh [x]
                      (geto m :a [x])
                      (== x 5)))
         [(lm {:a [5]} '_0)])))

(deftest test-lmap-featurec
  (is (= (run* [v]
               (fresh [m]
                      (geto m :a v)
                      (featurec m {:a 1})))
         '(1)))
  (is (= (run* [m]
               (geto m :a 1)
               (featurec m {:b 2}))
         [(lm {:a 1 :b 2} '_0)])))

(deftest test-lmap-disequality
  (is (= (run* [q]
               (fresh [m]
                      (geto m :a q)
                      (!= m {:a 1})
                      (== m {:a 1})))
         '()))
  (is (= (run* [q]
               (fresh [m]
                      (geto m :a q)
                      (!= m {:a 1})
                      (== m {:a 2})))
         '(2))))

;; -----------------------------------------------------------------------------
;; maps with unbound keys

(deftest test-map-unbound-key
  (is (= (run* [k]
               (== {k 1} {:a 1}))
         '(:a))))

(deftest test-map-unbound-keys-pair-up
  (is (= (run* [k1 k2]
               (== {k1 1 k2 2} {:a 1 :b 2}))
         '([:a :b])))
  (is (= (set (run* [k1 k2]
                    (== {k1 1 k2 1} {:a 1 :b 1})))
         #{[:a :b] [:b :a]})))

(deftest test-map-unbound-keys-stay-distinct
  (is (= (run* [k1 k2]
               (fresh [m]
                      (== m {k1 1 k2 2})))
         [`([~'_0 ~'_1] :- (distincto [~'_0 ~'_1]))]))
  (is (= (run* [m]
               (fresh [k1 k2]
                      (== m {k1 1 k2 2})
                      (== k1 :a)
                      (== k2 :a)))
         '()))
  ;; also when the map is not part of the answer
  (is (= (run* [q]
               (fresh [m k1 k2]
                      (== m {k1 1 k2 2})
                      (== k1 :a)
                      (== k2 :a)
                      (== q 5)))
         '())))

(deftest test-map-unbound-keys-collide-run-nc
  (is (= (run-nc* [m]
                  (fresh [k1 k2]
                         (== m {k1 1 k2 2})
                         (== k1 :a)
                         (== k2 :a)))
         '())))

(deftest test-map-unbound-key-disequality
  (is (= (run* [k]
               (!= {k 1} {:a 1})
               (== k :a))
         '()))
  (is (= (run* [k]
               (!= {k 1} {:a 1})
               (== k :b))
         '(:b))))

(deftest test-map-unbound-key-featurec
  (is (= (run* [k]
               (featurec {:a 1 :b 2} {k 2}))
         '(:b))))

(deftest test-map-unbound-key-geto
  (is (= (run* [v k]
               (geto {k 1} :a v))
         '([1 :a]))))

(deftest test-map-unbound-key-unifier
  (is (= (u/unify ['{?k 1} {:a 1}])
         '{:a 1})))

(deftest test-featurec-map-with-unbound-value
  (is (= (run* [v]
               (fresh [m]
                      (== m {:a v})
                      (featurec m {:a 1})))
         '(1))))

;; -----------------------------------------------------------------------------
;; lacks-keyo

(deftest test-lacks-keyo
  (is (= (run* [m]
               (lacks-keyo m :a)
               (== m {:a 1}))
         '()))
  (is (= (run* [m]
               (lacks-keyo m :a)
               (== m {:b 1}))
         '({:b 1})))
  (is (= (run* [m]
               (lacks-keyo m :a))
         [`(~'_0 :- (lacks-keyo ~'_0 :a))])))

(deftest test-lacks-keyo-key-bound-later
  (is (= (run* [q]
               (fresh [k]
                      (lacks-keyo {:a 1} k)
                      (== k :a)))
         '()))
  (is (= (run* [k]
               (fresh [m]
                      (lmapo m {:a 1} (lvar 'r))
                      (lacks-keyo m k)
                      (== k :a)))
         '())))

;; -----------------------------------------------------------------------------
;; geto

(deftest test-geto-forward
  (is (= (run* [v]
               (geto {:a 1 :b 2} :b v))
         '(2))))

(deftest test-geto-key-not-found
  (is (= (run* [v]
               (geto {:a 1 :b 2} :c v))
         '())))

(deftest test-geto-enumerate-keys
  (is (= (set (run* [k v]
                    (geto {:a 1 :b 2} k v)))
         #{[:a 1] [:b 2]})))

(deftest test-geto-find-key-by-value
  (is (= (set (run* [k]
                    (geto {:a 1 :b 2 :c 2} k 2)))
         #{:b :c})))

(deftest test-geto-constrain-unknown-map
  (is (= (run* [m]
               (geto m :name "Alice"))
         [(lm {:name "Alice"} '_0)])))

(deftest test-geto-adds-to-rest
  (is (= (run* [m]
               (fresh [r]
                      (lmapo m {:a 1} r)
                      (geto m :b 2)))
         [(lm {:a 1 :b 2} '_0)])))

(deftest test-geto-key-bound-later
  (is (= (run* [v]
               (fresh [k]
                      (geto {:a 1} k v)
                      (== k :a)))
         '(1)))
  (is (= (run* [m]
               (fresh [k]
                      (geto m k 1)
                      (== k :a)))
         [(lm {:a 1} '_0)])))

(deftest test-geto-map-bound-later
  (is (= (set (run* [k v]
                    (fresh [m]
                           (geto m k v)
                           (== m {:a 1 :b 2}))))
         #{[:a 1] [:b 2]})))

(deftest test-geto-conflicting-values
  (is (= (run* [m]
               (geto m :a 1)
               (geto m :a 2))
         '())))

(deftest test-geto-enumerate-open-map
  (let [answers (run* [k v]
                      (fresh [m]
                             (lmapo m {:a 1} (lvar 'r))
                             (geto m k v)))]
    ;; the known entry, and a pending answer for keys in the unknown rest
    (is (= (count answers) 2))
    (is (= (first answers) [:a 1]))))

;; -----------------------------------------------------------------------------
;; assoco

(deftest test-assoco-forward
  (is (= (run* [out]
               (assoco {:a 1} :b 2 out))
         '({:a 1, :b 2}))))

(deftest test-assoco-forward-overwrite
  (is (= (run* [out]
               (assoco {:a 1} :a 2 out))
         '({:a 2}))))

(deftest test-assoco-backward
  ;; m either lacked :b or had some other value there
  (is (= (set (run* [m v]
                    (assoco m :b v {:a 1 :b 2})))
         #{[{:a 1} 2] [{:a 1 :b '_0} 2]})))

(deftest test-assoco-query-what-added
  (is (= (run* [k v]
               (assoco {:a 1} k v {:a 1 :b 2}))
         '([:b 2]))))

(deftest test-assoco-query-what-changed
  (is (= (run* [k v]
               (assoco {:a 1 :b 1} k v {:a 1 :b 2}))
         '([:b 2]))))

(deftest test-assoco-key-not-in-output
  (is (= (run* [m v]
               (assoco m :c v {:a 1 :b 2}))
         '())))

(deftest test-assoco-both-unknown
  (is (= (set (run* [m out]
                    (assoco m :x 10 out)))
         #{['_0 (lm {:x 10} '_0)]
           [(lm {:x '_0} '_1) (lm {:x 10} '_1)]})))

(deftest test-assoco-overwrite-bound-later
  (is (= (run* [out]
               (fresh [m]
                      (assoco m :x 10 out)
                      (== m {:x 1})))
         '({:x 10}))))

(deftest test-assoco-key-bound-later
  (is (= (set (run* [out]
                    (fresh [k]
                           (assoco {:a 1} k 2 out)
                           (== k :b))))
         #{{:a 1 :b 2}})))

(deftest test-assoco-unbound-key
  ;; k is either a new key or :a
  (is (= (set (run* [out]
                    (fresh [k]
                           (assoco {:a 1} k 2 out))))
         #{`({:a 1 ~'_0 2} :- (lacks-keyo {:a 1} ~'_0))
           {:a 2}})))

;; -----------------------------------------------------------------------------
;; dissoco

(deftest test-dissoco-forward
  (is (= (run* [out]
               (dissoco {:a 1 :b 2 :c 3} :b out))
         '({:a 1, :c 3}))))

(deftest test-dissoco-nonexistent-key
  (is (= (run* [out]
               (dissoco {:a 1 :b 2} :x out))
         '({:a 1, :b 2}))))

(deftest test-dissoco-backward
  ;; m either had :b or did not
  (is (= (set (run* [m]
                    (dissoco m :b {:a 1})))
         #{{:a 1} {:a 1 :b '_0}})))

(deftest test-dissoco-query-removed-key
  (is (= (run* [k]
               (dissoco {:a 1 :b 2 :c 3} k {:a 1 :c 3}))
         '(:b))))

(deftest test-dissoco-query-key-not-present
  ;; any key m lacks
  (is (= (run* [k]
               (dissoco {:a 1} k {:a 1}))
         [`(~'_0 :- (lacks-keyo {:a 1} ~'_0))])))

(deftest test-dissoco-key-in-rest
  (is (= (run* [out]
               (fresh [m r]
                      (lmapo m {:a 1} r)
                      (dissoco m :b out)
                      (== r {:b 2})))
         '({:a 1}))))

(deftest test-dissoco-chain
  (is (= (run* [out]
               (fresh [tmp]
                      (dissoco {:a 1 :b 2} :b tmp)
                      (assoco tmp :c 3 out)))
         '({:a 1, :c 3}))))

;; -----------------------------------------------------------------------------
;; mergeo

(deftest test-mergeo-forward
  (is (= (run* [out]
               (mergeo {:a 1 :b 2} {:c 3 :d 4} out))
         '({:a 1, :b 2, :c 3, :d 4}))))

(deftest test-mergeo-overlap
  (is (= (run* [out]
               (mergeo {:a 1 :b 2} {:b 99 :c 3} out))
         '({:a 1, :b 99, :c 3}))))

(deftest test-mergeo-find-m1
  (is (= (set (run* [m1]
                    (mergeo m1 {:b 2} {:a 1 :b 2})))
         #{{:a 1} {:a 1 :b '_0}})))

(deftest test-mergeo-find-m2
  (is (= (set (run* [m2]
                    (mergeo {:a 1 :b 2} m2 {:a 1 :b 99 :c 3})))
         #{{:a 1 :b 99 :c 3} {:b 99 :c 3}})))

(deftest test-mergeo-split
  (is (= (set (run* [m1 m2]
                    (mergeo m1 m2 {:a 1})))
         #{[{:a 1} {}] [{} {:a 1}] [{:a '_0} {:a 1}]}))
  ;; each key is in m1 only, m2 only, or both
  (is (= (count (run* [m1 m2]
                      (mergeo m1 m2 {:a 1 :b 2})))
         9)))

(deftest test-mergeo-empty
  (is (= (run* [out]
               (mergeo {} {:a 1} out))
         '({:a 1}))))

(deftest test-mergeo-chain
  (is (= (run* [out]
               (fresh [tmp]
                      (mergeo {:a 1} {:b 2} tmp)
                      (mergeo tmp {:c 3} out)))
         '({:a 1, :b 2, :c 3}))))

(deftest test-mergeo-unbound-key
  (is (= (set (run* [out]
                    (fresh [k]
                           (mergeo {:a 1} {k 2} out))))
         #{`({:a 1 ~'_0 2} :- (lacks-keyo {:a 1} ~'_0))
           {:a 2}})))

;; -----------------------------------------------------------------------------
;; keyso

(deftest test-keyso-one-answer
  ;; the keys of a map are a set: one answer, not every order
  (is (= (run* [ks] (keyso {:a 1 :b 2} ks)) '(#{:a :b})))
  (is (= (run* [ks] (keyso {:a 1 :b 2 :c 3 :d 4 :e 5 :f 6 :g 7 :h 8 :i 9 :j 10} ks))
         [#{:a :b :c :d :e :f :g :h :i :j}])))

(deftest test-keyso-empty-map
  (is (= (run* [ks] (keyso {} ks)) '(#{}))))

(deftest test-keyso-given-set
  (is (= (run* [q] (keyso {:a 1 :b 2} #{:b :a}) (== q true)) '(true)))
  (is (= (run* [q] (keyso {:a 1 :b 2} #{:a}) (== q true)) '())))

(deftest test-keyso-not-a-set
  ;; a vector of keys is not the key set, as (= #{:a} [:a]) is false
  (is (= (run* [q] (keyso {:a 1} [:a]) (== q true)) '()))
  (is (= (run* [m] (keyso m [:a])) '())))

(deftest test-keyso-backward
  ;; which value is _0 depends on set order
  (let [ms (run* [m] (keyso m #{:x :y}))]
    (is (= 1 (count ms)))
    (is (= #{:x :y} (set (keys (first ms)))))
    (is (= '#{_0 _1} (set (vals (first ms)))))))

(deftest test-keyso-closes-open-map
  (is (= (run* [m] (geto m :a 1) (keyso m #{:a :b})) '({:a 1 :b _0}))))

(deftest test-keyso-unknown-keys
  ;; unknown keys pair up with the map's keys
  (is (= (set (run* [x y] (keyso {:a 1 :b 2} #{x y}))) #{[:a :b] [:b :a]}))
  (is (= (run* [x] (keyso {x 1 :b 2} #{:a :b})) '(:a))))

(deftest test-keyso-waits
  (is (= (run* [ks] (fresh [m] (keyso m ks) (== m {:a 1}))) '(#{:a})))
  (is (= (run* [m] (fresh [ks] (keyso m ks) (== ks #{:a}))) '({:a _0}))))

(deftest test-keyso-with-containso
  (is (= (run* [q] (fresh [ks] (keyso {:a 1 :b 2} ks) (containso ks :a) (== q true)))
         '(true))))

;; -----------------------------------------------------------------------------
;; valso

(deftest test-valso-every-order
  (is (= (set (run* [vs]
                    (valso {:a 1 :b 2} vs)))
         #{[1 2] [2 1]})))

(deftest test-valso-repeated-value
  (is (= (run* [vs]
               (valso {:a 1 :b 1} vs))
         '((1 1)))))

(deftest test-valso-empty-map
  (is (= (run* [vs]
               (valso {} vs))
         '(()))))

(deftest test-valso-given-order
  (is (= (run* [q]
               (valso {:a 1 :b 2} [2 1])
               (== q true))
         '(true))))

(deftest test-valso-backward
  ;; two entries with those values, under two distinct unknown keys
  (let [[answer & more] (run* [m] (valso m [10 20]))]
    (is (empty? more))
    (is (= (set (vals (first answer))) #{10 20}))
    (is (= (count (first answer)) 2))))

(deftest test-valso-closes-open-map
  (is (= (run* [m]
               (geto m :a 1)
               (valso m [1]))
         '({:a 1}))))

;; -----------------------------------------------------------------------------
;; selectso

(deftest test-selectso-forward
  (is (= (run* [out]
               (selectso {:a 1 :b 2 :c 3 :d 4} [:a :c] out))
         '({:a 1, :c 3}))))

(deftest test-selectso-missing-keys
  (is (= (run* [out]
               (selectso {:a 1 :b 2} [:a :x :y] out))
         '({:a 1}))))

(deftest test-selectso-repeated-key
  (is (= (run* [out]
               (selectso {:a 1 :b 2} [:a :a] out))
         '({:a 1}))))

(deftest test-selectso-query-keys
  ;; infinitely many: out's keys in any order and repeated, plus absent keys
  (is (= (run 4 [ks]
              (selectso {:a 1 :b 2} ks {:a 1}))
         [[:a]
          `((~'_0 :a) :- (lacks-keyo {:a 1 :b 2} ~'_0))
          `((:a ~'_0) :- (lacks-keyo {:a 1 :b 2} ~'_0))
          [:a :a]])))

(deftest test-selectso-backward
  (is (= (run* [m]
               (selectso m [:x :y] {:x 10 :y 20}))
         [(lm {:x 10 :y 20} '_0)])))

(deftest test-selectso-backward-unselected-key-absent
  (is (= (run* [m]
               (selectso m [:a :b] {:a 1}))
         [`(~(lm {:a 1} '_0) :- (lacks-keyo ~'_0 :b))]))
  (is (= (run* [m]
               (selectso m [:a :b] {:a 1})
               (== m {:a 1 :b 2}))
         '())))

(deftest test-selectso-empty
  (is (= (run* [out]
               (selectso {:a 1 :b 2} [] out))
         '({}))))

(deftest test-selectso-chain-with-mergeo
  (is (= (run* [out]
               (fresh [selected]
                      (selectso {:a 1 :b 2 :c 3} [:a :b] selected)
                      (mergeo selected {:d 4} out)))
         '({:a 1, :b 2, :d 4}))))

;; -----------------------------------------------------------------------------
;; Integration tests

(deftest test-lmap-geto-assoco-integration
  (is (= (run* [result]
               (fresh [v tmp]
                      (geto {:a 1 :b 2} :a v)
                      (assoco {:x 10} :y v result)))
         '({:x 10, :y 1}))))

(deftest test-lmap-full-pipeline
  (is (= (run* [out]
               (fresh [selected merged]
                      (selectso {:a 1 :b 2 :c 3} [:a :b] selected)
                      (dissoco selected :b merged)
                      (assoco merged :d 4 out)))
         '({:a 1, :d 4}))))

(deftest test-lmap-goal-order-independent
  (let [goals (fn [m k v out]
                [(geto m k v)
                 (dissoco m k out)
                 (== m {:a 1 :b 2})
                 (== k :a)])
        run-in-order (fn [order]
                       (run* [q]
                             (fresh [m k v out]
                                    (let [gs (goals m k v out)]
                                      (and* (map gs order)))
                                    (== q [v out]))))]
    (doseq [order [[0 1 2 3] [2 3 0 1] [3 0 1 2] [1 0 3 2]]]
      (is (= (run-in-order order) '([1 {:b 2}]))))))

(deftest test-lmap-tabled
  (let [entryo (tabled [m k v] (geto m k v))]
    (is (= (set (run* [k v]
                      (entryo {:a 1 :b 2} k v)))
           #{[:a 1] [:b 2]}))))

(deftest test-lmap-tabled-open-map-keeps-rest-constraint
  (let [opento (tabled [m] (fresh [r] (lmapo m {:a 1} r)))]
    ;; the second call reuses copies of the first call's answers
    (is (= (run* [r]
                 (fresh [m0 m]
                        (opento m0)
                        (opento m)
                        (lmapo m {:a 1} r)
                        (== r {:a 2})))
           '()))))

(deftest test-lmap-copy-term-keeps-rest-constraint
  (is (= (run* [r]
               (fresh [m c]
                      (lmapo m {:a 1} (lvar 'r0))
                      (copy-term m c)
                      (lmapo c {:a 1} r)
                      (== r {:a 2})))
         '())))

;; -----------------------------------------------------------------------------
;; LMap cases from the literature (row unification, feature logic, set
;; unification)

(deftest test-lmap-same-rest-fails
  ;; {:a 1 | r} and {:b 2 | r} would each need r to hold the other's key
  (is (= (run* [r]
               (fresh [m1 m2]
                      (lmapo m1 {:a 1} r)
                      (lmapo m2 {:b 2} r)
                      (== m1 m2)))
         '())))

(deftest test-lmap-ground-keys-unify-without-branching
  (is (= (run* [q]
               (fresh [m1 m2 r1 r2]
                      (lmapo m1 {:a 1} r1)
                      (lmapo m2 {:b 2} r2)
                      (== m1 m2)
                      (== q m1)))
         [(lm {:a 1 :b 2} '_0)])))

(deftest test-lmap-var-keys-each-pairing-once
  (let [answers (run* [a b c] (== {a 1 b 1 c 1} {:x 1 :y 1 :z 1}))]
    (is (= (count answers) 6))
    (is (= (count (set answers)) 6))))

(deftest test-lmap-disequality-var-key
  (is (= (run* [k] (!= {k 1} {:a 1}) (== k :a)) '()))
  (is (= (run* [k] (!= {k 1} {:a 1}) (== k :b)) '(:b))))

;; =============================================================================
;; LVec - relational vectors

(defn- lv
  "An LVec as it appears in a reified answer."
  [front mid back]
  (clojure.core.logic.LVec. front mid back -1))

;; -----------------------------------------------------------------------------
;; ntho

(deftest test-ntho-forward
  (is (= (run* [x] (ntho [1 2 3] 1 x)) '(2)))
  (is (= (run* [x] (ntho '(1 2 3) 2 x)) '(3)))
  (is (= (run* [x] (ntho [1 2 3] 3 x)) '())))

(deftest test-ntho-positions
  (is (= (run* [i] (ntho [1 2 3 2] i 2)) '(1 3))))

(deftest test-ntho-open
  (is (= (run* [v] (ntho v 2 :x))
         [(lv '[_0 _1 :x] '_2 [])]))
  (is (= (run 3 [i v] (ntho v i :x))
         [[0 (lv [:x] '_0 [])]
          [1 (lv '[_0 :x] '_1 [])]
          [2 (lv '[_0 _1 :x] '_2 [])]])))

(deftest test-ntho-builds-vector
  (is (= (run* [q]
               (fresh [v]
                      (ntho v 0 :a)
                      (ntho v 2 :c)
                      (counto v 3)
                      (== q v)))
         '([:a _0 :c]))))

(deftest test-ntho-large
  (is (= (run* [i] (ntho (vec (range 2000)) i 1999)) '(1999))))

;; -----------------------------------------------------------------------------
;; counto

(deftest test-counto
  (is (= (run* [n] (counto [1 2 3] n)) '(3)))
  (is (= (run* [n] (counto {:a 1} n)) '(1)))
  (is (= (run* [q] (fresh [v] (ntho v 1 :x) (counto v 2) (== q v)))
         '([_0 :x])))
  (is (= (run 3 [v n] (ntho v 0 :a) (counto v n))
         '([[:a] 1] [[:a _0] 2] [[:a _0 _1] 3]))))

(deftest test-counto-fd
  (is (= (run* [v n]
               (fd/in n (fd/interval 1 2))
               (counto v n)
               (ntho v 0 :a))
         '([[:a] 1] [[:a _0] 2]))))

(deftest test-counto-open-map
  (is (= (run* [m] (geto m :a 1) (counto m 1)) '({:a 1}))))

;; -----------------------------------------------------------------------------
;; conjo, peeko, popo

(deftest test-conjo-vector-list
  (is (= (run* [out] (conjo [1 2] 3 out)) '([1 2 3])))
  (is (= (run* [out] (conjo '(1 2) 3 out)) '((3 1 2))))
  (is (= (run* [v] (conjo v 3 [1 2 3])) '([1 2])))
  (is (= (run* [out] (conjo [] 1 2 out)) '([1 2]))))

(deftest test-peeko-popo
  (is (= (run* [x] (peeko [1 2 3] x)) '(3)))
  (is (= (run* [x] (peeko '(1 2 3) x)) '(1)))
  (is (= (run* [out] (popo [1 2 3] out)) '([1 2])))
  (is (= (run* [out] (popo '(1 2 3) out)) '((2 3))))
  (is (= (run* [out] (popo [] out)) '())))

(deftest test-peeko-open
  (is (= (run* [q]
               (fresh [v]
                      (ntho v 0 :a)
                      (peeko v :z)
                      (counto v 3)
                      (== q v)))
         '([:a _0 :z]))))

;; -----------------------------------------------------------------------------
;; concato and subveco

(deftest test-concato
  (is (= (run* [out] (concato [1 2] [3] out)) '([1 2 3])))
  (is (= (run* [a b] (concato a b [1 2 3]))
         '([[] [1 2 3]] [[1] [2 3]] [[1 2] [3]] [[1 2 3] []]))))

(deftest test-concato-open
  (is (= (run 3 [a b] (concato a b (lvar)))
         '([[] []] [[_0] _1] [[] [_0]]))))

(deftest test-concato-overlap
  ;; x, then [3 4], is [1 2], then y
  (is (= (run* [x y]
               (fresh [a]
                      (concato x [3 4] a)
                      (concato [1 2] y a)))
         [[(lv [1 2] '_0 []) (lv [] '_0 [3 4])]]))
  (is (= (run* [x y]
               (fresh [a]
                      (counto x 1)
                      (concato x [3 4] a)
                      (concato [1 2] y a)))
         '())))

(deftest test-concato-lengths-fail-early
  ;; |a| = |x| + 1 = |b| and |a| = |b| + 1
  (is (= (run* [q]
               (fresh [x a b]
                      (concato x [1] a)
                      (concato [1] x b)
                      (concato b [2] a)
                      (== q 1)))
         '())))

(deftest test-subveco
  (is (= (run* [out] (subveco [1 2 3 4 5] 1 3 out)) '([2 3])))
  (is (= (run* [s e] (subveco [1 2 3] s e [2 3])) '([1 3]))))

;; -----------------------------------------------------------------------------
;; geto and assoco on vectors

(deftest test-geto-vector
  (is (= (run* [x] (geto [1 2 3] 2 x)) '(3)))
  (is (= (run* [x] (geto [1 2 3] 5 x)) '()))
  (is (= (run* [x] (geto [1 2 3] :a x)) '())))

(deftest test-geto-map-or-vector
  ;; an index into a collection of unknown kind
  (is (= (run* [m] (geto m 0 1))
         [(lm {0 1} '_0) (lv [1] '_0 [])]))
  (is (= (run* [m] (geto m :a 1))
         [(lm {:a 1} '_0)])))

(deftest test-geto-nested
  (is (= (run* [x]
               (fresh [u e]
                      (geto {:users [{:name "a"} {:name "b"}]} :users u)
                      (geto u 1 e)
                      (geto e :name x)))
         '("b"))))

(deftest test-assoco-vector
  (is (= (run* [out] (assoco [1 2 3] 1 :x out)) '([1 :x 3])))
  (is (= (run* [out] (assoco [1 2 3] 3 :x out)) '([1 2 3 :x])))
  (is (= (run* [out] (assoco [1 2 3] 4 :x out)) '()))
  (is (= (run* [v] (assoco v 1 :x [1 :x 3])) '([1 _0 3]))))

;; -----------------------------------------------------------------------------
;; unification

(deftest test-lvec-unify-list
  (is (= (run* [q] (fresh [x] (== (lcons 1 x) [1 2 3]) (== q x))) '((2 3))))
  (is (= (run* [q]
               (fresh [v t]
                      (conjo v 9 q)
                      (== v (lcons 1 t))
                      (counto q 3)))
         '((9 1 _0)))))

(deftest test-lvec-disequality
  (is (= (run* [q]
               (fresh [v]
                      (ntho v 0 1)
                      (!= v [1 2])
                      (counto v 2)
                      (== q v)))
         '(([1 _0] :- (!= (_0 2))))))
  (is (= (run* [q]
               (fresh [v]
                      (ntho v 0 1)
                      (!= v [1 2])
                      (counto v 2)
                      (ntho v 1 2)
                      (== q v)))
         '())))

(deftest test-lvec-tabled
  (let [firsto (tabled [v] (ntho v 0 :a))]
    (is (= (run 2 [q] (firsto q))
           [(lv [:a] '_0 [])]))))

(deftest test-lvec-copy-term
  (is (= (run* [q]
               (fresh [v c]
                      (ntho v 1 :a)
                      (copy-term v c)
                      (counto c 2)
                      (== q c)))
         '([_0 :a]))))

;; -----------------------------------------------------------------------------
;; get-ino and assoc-ino

(deftest test-get-ino
  (is (= (run* [x] (get-ino {:a {:b [1 2]}} [:a :b 1] x)) '(2)))
  (is (= (run* [x] (get-ino {:a 1} [] x)) '({:a 1})))
  (is (= (run* [x] (get-ino {:a 1} [:b] x)) '())))

(deftest test-get-ino-paths
  (is (= (set (run* [p] (get-ino {:a {:b 1} :c [1 {:d 1}]} p 1)))
         #{'(:a :b) '(:c 0) '(:c 1 :d)})))

(deftest test-get-ino-backward
  (is (= (run* [m] (get-ino m [:a 0 :b] 1))
         [(lm {:a (lm {0 (lm {:b 1} '_0)} '_1)} '_2)
          (lm {:a (lv [(lm {:b 1} '_0)] '_1 [])} '_2)])))

(deftest test-assoc-ino
  (is (= (run* [out] (assoc-ino {:a {:b 1}} [:a :c] 2 out)) '({:a {:b 1 :c 2}})))
  (is (= (run* [out] (assoc-ino {} [:a :b] 1 out)) '({:a {:b 1}})))
  (is (= (run* [out] (assoc-ino nil [:a] 1 out)) '({:a 1})))
  (is (= (run* [out] (assoc-ino {:a [1 2]} [:a 1] :x out)) '({:a [1 :x]})))
  (is (= (run* [out] (assoc-ino {:a [1 2]} [:a 2] :x out)) '({:a [1 2 :x]})))
  (is (= (run* [out] (assoc-ino {:a [1 2]} [:a 3] :x out)) '())))

(deftest test-assoc-ino-backward
  (is (= (run* [m] (assoc-ino m [:a :b] 1 {:a {:b 1}}))
         '(nil {} {:a nil} {:a {}} {:a {:b _0}})))
  (is (= (run* [ks] (assoc-ino {:a {:b 1}} ks 2 {:a {:b 2}}))
         '((:a :b)))))

;; =============================================================================
;; miniKanren parity

(defrel appendo-rel [l s out]
  (conde
   [(== l ()) (== s out)]
   [(fresh [a d res]
           (conso a d l)
           (conso a res out)
           (appendo-rel d s res))]))

(deftest test-defrel
  (is (= (run* [x y] (appendo-rel x y [1 2]))
         '([() [1 2]] [(1) (2)] [(1 2) ()])))
  ;; compared as printed: a quoted (_0 . _1) is not a partial list
  (is (= (map pr-str (run 2 [x y z] (appendo-rel x y z)))
         ["[() _0 _0]" "[(_0) _1 (_0 . _1)]"])))

(deftest test-type-constraints
  (is (= (run* [q] (symbolo q)) `((~'_0 :- (symbolo ~'_0)))))
  (is (= (run* [q] (symbolo q) (== q 'a)) '(a)))
  (is (= (run* [q] (symbolo q) (== q 1)) '()))
  (is (= (run* [q] (numbero q) (== q 1)) '(1)))
  (is (= (run* [q] (stringo q) (== q "a")) '("a")))
  (is (= (run* [q] (numbero q) (== q (lcons 1 (lvar)))) '())))

(deftest test-type-conflicts
  ;; conflicting types fail while still unbound
  (is (= (run* [q] (symbolo q) (numbero q)) '()))
  (is (= (run* [q]
               (fresh [x y]
                      (symbolo x)
                      (numbero y)
                      (== x y)
                      (== q 1)))
         '()))
  (is (= (run* [q]
               (fresh [x y]
                      (symbolo x)
                      (symbolo y)
                      (== x y)
                      (== q [x y])))
         `(([~'_0 ~'_0] :- (symbolo ~'_0))))))

(deftest test-absento
  (is (= (run* [q] (absento 'closure q))
         `((~'_0 :- (absento ~'closure ~'_0)))))
  (is (= (run* [q] (absento 'closure q) (== q '(1 closure))) '()))
  (is (= (run* [q] (fresh [x] (absento 1 [x 2]) (== x 1) (== q 1))) '()))
  (is (= (run* [q] (absento [1] q) (== q [[1]])) '()))
  (is (= (run* [q] (absento [1] q) (== q [[2]])) '([[2]])))
  (is (= (run* [q] (absento :a q) (geto q :a 1)) '())))

;; -----------------------------------------------------------------------------
;; faster-miniKanren's simple relational interpreter (quines), ported

(declare eval-expo)

(defrel not-in-envo [x env]
  (conde
   [(== () env)]
   [(fresh [y v rest]
           (== (lcons (lcons y v) rest) env)
           (!= y x)
           (not-in-envo x rest))]))

(defrel lookupo [x env t]
  (fresh [rest y v]
         (== (lcons (lcons y v) rest) env)
         (conde
          [(== y x) (== v t)]
          [(!= y x) (lookupo x rest t)])))

(defrel proper-listo [exp env val]
  (conde
   [(== () exp) (== () val)]
   [(fresh [a d t-a t-d]
           (== (lcons a d) exp)
           (== (lcons t-a t-d) val)
           (eval-expo a env t-a)
           (proper-listo d env t-d))]))

(defrel eval-expo [expr env val]
  (conde
   [(fresh [v]
           (== (list 'quote v) expr)
           (not-in-envo 'quote env)
           (absento 'closure v)
           (== v val))]
   [(fresh [a*]
           (== (lcons 'list a*) expr)
           (not-in-envo 'list env)
           (absento 'closure a*)
           (proper-listo a* env val))]
   [(symbolo expr) (lookupo expr env val)]
   [(fresh [rator rand x body env2 a]
           (== (list rator rand) expr)
           (eval-expo rator env (list 'closure x body env2))
           (eval-expo rand env a)
           (eval-expo body (lcons (lcons x a) env2) val))]
   [(fresh [x body]
           (== (list 'lambda (list x) body) expr)
           (symbolo x)
           (not-in-envo 'lambda env)
           (== (list 'closure x body env) val))]))

(defn- evalo [expr val] (eval-expo expr () val))

(deftest test-relational-interpreter
  (is (= (run* [v] (evalo '((lambda (x) x) (quote 5)) v)) '(5)))
  (is (= (count (run 5 [q] (evalo q 6))) 5)))

(deftest test-quine
  (let [[ans] (run 1 [q] (evalo q q))
        [quine] ans
        ;; the quine's variable as a concrete symbol
        quine (clojure.walk/postwalk-replace {'_0 'x} quine)]
    (is (= (run* [v] (evalo quine v)) (list quine)))))

(deftest test-twine
  (let [[[[p q]]] (run 1 [p q] (!= p q) (evalo p q) (evalo q p))
        [p q] (clojure.walk/postwalk-replace {'_0 'x} [p q])]
    (is (not= p q))
    (is (= (run* [v] (evalo p v)) (list q)))
    (is (= (run* [v] (evalo q v)) (list p)))))

;; =============================================================================
;; LSet - relational sets

(defn- ls
  "An LSet as it appears in a reified answer."
  [elems rest]
  (clojure.core.logic.LSet. elems rest -1))

(deftest test-containso
  (is (= (set (run* [x] (containso #{1 2 3} x))) #{1 2 3}))
  (is (= (run* [s] (containso s 1) (containso s 2)) [(ls #{1 2} '_0)]))
  (is (= (run* [s] (fresh [x] (containso s x)))
         `((~'_0 :- (containso ~'_0 ~'_1)))))
  (is (= (run* [q] (lackso q 1) (containso q 1)) '())))

(deftest test-containso-open-unknown-element
  ;; 1, 2, or another element of the unknown rest
  (is (= (run* [x] (fresh [s] (lseto s #{1 2} (lvar)) (containso s x)))
         `(1 2 (~'_0 :- (containso ~(ls #{1 2} '_1) ~'_0) (~'!= (~'_0 1)) (~'!= (~'_0 2)))))))

(deftest test-set-unify
  (is (= (set (run* [x y] (== #{x y} #{1 2}))) #{[1 2] [2 1]}))
  (is (= (run* [x y] (== #{x y} #{1})) '()))
  (is (= (run* [q] (== #{[q 1]} #{[2 1]})) '(2))))

(deftest test-set-elements-stay-distinct
  (is (= (run* [q] (fresh [x y] (== q #{x y}) (== x 1) (== y 1))) '()))
  (is (= (run* [q] (fresh [x y s] (== s #{x y}) (== x 1) (== y 1) (== q 1))) '())))

(deftest test-disjo-conjo-set
  (is (= (run* [out] (disjo #{1 2} 1 out)) '(#{2})))
  (is (= (set (run* [s] (disjo s 1 #{2}))) #{#{1 2} #{2}}))
  (is (= (run* [out] (conjo #{1} 2 out)) '(#{1 2})))
  (is (= (set (run* [s] (conjo s 2 #{1 2}))) #{#{1 2} #{1}})))

(deftest test-lseto
  (is (= (run* [s] (lseto s #{1} #{2})) '(#{1 2})))
  (is (= (set (run* [x r] (lseto #{1 2 3} #{x} r)))
         #{[1 #{2 3}] [2 #{1 3}] [3 #{1 2}]})))

(deftest test-set-algebra
  (is (= (run* [out] (uniono #{1 2} #{2 3} out)) '(#{1 2 3})))
  (is (= (run* [out] (intersectiono #{1 2} #{2 3} out)) '(#{2})))
  (is (= (run* [out] (differenceo #{1 2} #{2 3} out)) '(#{1})))
  (is (= (count (run* [a b] (uniono a b #{1 2}))) 9))
  (is (= (set (run* [a] (differenceo a #{2 3} #{1})))
         #{#{1} #{1 2} #{1 3} #{1 2 3}}))
  (is (= (set (run* [a] (subseto a #{1 2}))) #{#{} #{1} #{2} #{1 2}}))
  (is (= (run* [q] (subseto #{1 2} q)) [(ls #{1 2} '_0)]))
  (is (= (run* [q] (disjointo #{1} q) (containso q 1)) '())))

(deftest test-set-algebra-literal-distinct
  ;; a set literal's elements stay distinct when a relation takes it apart
  (is (= (run* [x] (uniono #{:cat x} #{} #{:cat})) '()))
  (is (= (run* [x] (subseto #{:cat x} #{:cat})) '()))
  (is (= (run* [x] (intersectiono #{:cat x} #{:cat} #{:cat}) (== x :cat)) '()))
  ;; two element vars bound to each other
  (is (= (run* [x y] (fresh [s] (== s #{x y}) (== x y))) '()))
  (is (= (run* [x y] (== x y) (fresh [s] (== s #{x y}))) '()))
  (is (= (run* [x y z] (fresh [s] (== s #{x y z}) (== x z))) '()))
  ;; the union from the upstream wiki's CLP(Set) page
  (is (= (set (run* [x y z] (uniono #{:cat x y} #{:dog :bird z} #{:cat :dog :bird})))
         #{[:dog :bird :cat] [:bird :dog :cat]})))

(deftest test-set-counto
  (is (= (run* [n] (counto #{1 2} n)) '(2)))
  (is (= (run* [s] (containso s 1) (counto s 1)) '(#{1}))))

(deftest test-set-disequality
  (is (= (run* [q] (!= #{q} #{1}) (== q 1)) '()))
  (is (= (run* [q] (!= #{q} #{1}) (== q 2)) '(2))))

(deftest test-set-tabled-copy-term
  (let [g (tabled [s] (containso s 1))]
    (is (= (run 2 [q] (g q)) [(ls #{1} '_0)])))
  (is (= (run* [q] (fresh [s c] (containso s 1) (copy-term s c) (containso c 2) (lackso c 1) (== q c)))
         '())))

(deftest test-set-not-a-map
  (is (= (run* [q] (fresh [s] (containso s 1) (== s {1 1}) (== q 1))) '()))
  (is (= (run* [q] (fresh [s] (geto s 1 1) (== s #{1}) (== q 1))) '())))

;; -----------------------------------------------------------------------------
;; FD residual answers

(defn residual-set [answer]
  [(first answer) (set (drop 2 answer))])

(deftest test-fd-residual-domain
  (is (= (run* [q] (fd/residual) (fd/in q (fd/interval 1 3)))
         `((~'_0 :- (fd/in ~'_0 (fd/interval 1 3))))))
  (is (= (run* [q] (fd/residual)
               (fresh [x] (fd/in x (fd/interval 1 1000000)) (== q [x])))
         `(([~'_0] :- (fd/in ~'_0 (fd/interval 1 1000000))))))
  (is (= (run* [q] (fd/residual) (fd/in q (fd/domain 1 5 9)))
         `((~'_0 :- (fd/in ~'_0 (fd/domain 1 5 9)))))))

(deftest test-fd-residual-constraints
  ;; fd/< narrows only once a side is known, so the domains stay 1..3
  (is (= (map residual-set
              (run* [x y] (fd/residual) (fd/in x y (fd/interval 1 3)) (fd/< x y)))
         `[[[~'_0 ~'_1] #{(fd/< ~'_0 ~'_1)
                          (fd/in ~'_0 (fd/interval 1 3))
                          (fd/in ~'_1 (fd/interval 1 3))}]]))
  (is (= (map residual-set
              (run* [x y] (fd/residual) (fd/in x y (fd/interval 1 3)) (fd/<= x y)
                    (fd/!= y 3)))
         `[[[~'_0 ~'_1] #{(fd/<= ~'_0 ~'_1)
                          (fd/in ~'_0 (fd/interval 1 2))
                          (fd/in ~'_1 (fd/interval 1 2))}]]))
  ;; y isn't in the answer, but x depends on it
  (is (= (map residual-set
              (run* [x] (fd/residual)
                    (fresh [y] (fd/in x y (fd/interval 0 9)) (fd/+ x y 10))))
         `[[~'_0 #{(fd/+ ~'_0 ~'_1 10)
                   (fd/in ~'_0 (fd/interval 1 9))
                   (fd/in ~'_1 (fd/interval 1 9))}]]))
  ;; z is unrelated to the answer
  (is (= (run* [x] (fd/residual)
               (fresh [z] (fd/in x (fd/interval 1 2)) (fd/in z (fd/interval 1 9))))
         `((~'_0 :- (fd/in ~'_0 (fd/interval 1 2)))))))

(deftest test-fd-residual-needs-solution
  ;; every domain stays {1 2}, but three distinct values don't fit
  (is (= (run* [x] (fd/residual)
               (fresh [y z] (fd/in x y z (fd/domain 1 2)) (fd/distinct [x y z])))
         '()))
  (is (= (count (run* [x] (fd/residual)
                      (fresh [y z] (fd/in x y z (fd/domain 1 2 3)) (fd/distinct [x y z]))))
         1)))

(deftest test-fd-residual-ground
  (is (= (run* [x] (fd/residual) (fd/in x (fd/interval 0 10))
               (conde [(fd/< x 3)] [(== x 7)]))
         `((~'_0 :- (fd/in ~'_0 (fd/interval 0 2))) 7)))
  ;; labeling stays the default
  (is (= (run* [q] (fd/in q (fd/interval 1 3))) '(1 2 3))))

;; -----------------------------------------------------------------------------
;; Disequality fixes found by running faster-miniKanren's tests

(deftest test-disequality-lcons
  ;; used to throw: seq on an LCons
  (is (= (run* [q] (fresh [w x y z] (!= (lcons w x) (lcons y z)) (== q 1)))
         '(1)))
  ;; used to say "always different": x may be (2)
  (is (= (run* [x] (!= (lcons 1 x) [1 2]))
         '((_0 :- (!= (_0 (2)))))))
  (is (= (run* [x] (!= (lcons 1 x) [1 2]) (== x [2])) '())))

(deftest test-disequality-lcons-equality
  ;; LCons = takes vars as wildcards, so this used to fail
  (is (= (map pr-str (run* [q] (fresh [a b] (!= q (lcons a b)) (== q (lcons 3 4)))))
         ["(3 . 4)"])))

(deftest test-disequality-shared-var
  ;; the second pairing of q used to overwrite the first: q != r only
  (is (= (run* [q p r] (!= [q q] [p r]) (== q 1) (== p 2) (== r 1))
         '([1 2 1])))
  (is (= (run* [q p r] (!= [q q] [p r]) (== q 1) (== p 1) (== r 1))
         '())))

(deftest test-disequality-wakes-on-nested-lcons
  ;; the vars of ((3 . e) f . 4) used to go unwatched
  (is (= (run* [q] (fresh [e f]
                          (!= q (lcons (lcons 3 e) (lcons f 4)))
                          (== e 1) (== f 2)
                          (== q (lcons (lcons 3 1) (lcons 2 4)))))
         '())))

(deftest test-absento-non-ground
  (is (= (run* [q] (absento q q)) '()))
  (is (= (run* [q] (fresh [a]
                          (== (lcons a 3) q)
                          (absento q (lcons a (lcons 4 (lcons a 3))))))
         '()))
  (is (= (map pr-str (run* [q] (fresh [a b]
                                      (absento (lcons a b) q)
                                      (== q (lcons 3 (lcons b b))))))
         ["(3 _0 . _0)"])))

(deftest test-residual-simplification
  ;; implied by the type
  (is (= (run* [q] (symbolo q) (!= q 5)) '((_0 :- (clojure.core.logic/symbolo _0)))))
  ;; on a var the answer doesn't show
  (is (= (run* [q] (fresh [x] (symbolo x) (!= x q))) '(_0)))
  ;; subsumed
  (is (= (run* [q] (fresh [x y] (== q [x y]) (!= x 5) (!= [x y] [5 6])))
         '(([_0 _1] :- (!= (_0 5)))))))

(deftest test-map-keys-var-collision
  ;; two key vars bound to each other: the map would lose an entry
  (is (= (run* [x y] (fresh [m] (== m {x 1 y 2}) (== x y))) '()))
  (is (= (run* [x y] (fresh [m] (== m {x 1 y 2}))) '(([_0 _1] :- (clojure.core.logic/distincto [_0 _1]))))))

(deftest test-disequality-map-residual
  ;; the leftover disequality on a map with an unknown key is shown
  (is (= (run* [k] (!= {k 1} {:a 1})) '((_0 :- (!= ({_0 1} {:a 1}))))))
  (is (= (run* [k] (!= {k 1} {:a 1}) (== k :a)) '()))
  (is (= (run* [k] (!= {k 1} {:a 1}) (== k :b)) '(:b))))

(deftest test-lseto-lmapo-unbound-parts
  ;; with the elements or entries unbound, lseto and lmapo wait
  (is (= (run* [e r] (lseto #{1 2} e r) (== e #{1})) '([#{1} #{2}])))
  (is (= (count (run* [e r] (lseto #{1 2} e r))) 1))
  (is (= (run* [r] (lseto #{1 2} [1] r)) '()))
  (is (= (run* [e r] (lmapo {:a 1} e r) (== e {:a 1})) '([{:a 1} {}])))
  (is (= (count (run* [e r] (lmapo {:a 1} e r))) 1))
  (is (= (run* [r] (lmapo {:a 1} [1] r)) '())))

(deftest test-keywordo
  (is (= (run* [q] (keywordo q) (== q :a)) [:a]))
  (is (= (run* [q] (keywordo q) (== q 'a)) []))
  (is (= (run* [q] (keywordo q) (symbolo q)) [])))

(deftest test-geto-one-value-per-key
  ;; a key has one value, also while map and key are unknown
  (is (= (run* [m k] (geto m k 1) (geto m k 2)) []))
  (is (= (run* [m k] (lacks-keyo m :z) (geto m k 1) (geto m k 2)) []))
  (is (= (run* [m n k] (geto m k 1) (geto n k 2) (== m n)) []))
  ;; a map can't hold itself
  (is (= (run* [m k] (lacks-keyo m :z) (geto m k [m])) []))
  ;; what is absent from a map is absent from what geto puts in it
  (is (= (run* [m k] (lacks-keyo m :z) (absento 1 m) (geto m k [1])) []))
  (is (= (run* [m k] (lacks-keyo m :z) (geto m k [1]) (absento 1 m)) [])))

(def ^:private vectoro* #(@#'clojure.core.logic/typeo :vector `vectoro %))

(deftest test-seq-element-at-unknown-index
  ;; an element at an unknown position of an open vector: these used to
  ;; enumerate the positions forever, each failing on its own
  (testing "a vector can't hold itself"
    (is (= (run* [i] (fresh [v] (vectoro* v) (geto v i (list v)))) []))
    (is (= (run* [i] (fresh [v] (vectoro* v) (geto v i [:a (list 1 v)]))) []))
    (is (= (run* [i] (fresh [v x] (vectoro* v) (geto v i x) (== x (list v)))) []))
    (is (= (run* [i] (fresh [v] (vectoro* v) (ntho v i (list v)))) []))
    (is (= (run* [i] (fresh [v a] (vectoro* v) (conjo a 1 v) (geto v i (list v)))) [])))
  (testing "what is absent from a vector is absent from its elements"
    (is (= (run* [i] (fresh [v] (vectoro* v) (absento 1 v) (geto v i 1))) []))
    (is (= (run* [i] (fresh [v] (vectoro* v) (geto v i 1) (absento 1 v))) []))
    (is (= (run* [i] (fresh [v] (vectoro* v) (geto v i [1]) (absento 1 v))) [])))
  (testing "a position has one element, also while it is unknown"
    (is (= (run* [i] (fresh [v] (vectoro* v) (geto v i 1) (geto v i 2))) []))
    (is (= (run* [i] (fresh [v a] (vectoro* v) (conjo a 0 v) (geto v i 1) (geto v i 2))) []))
    (is (= (run* [i] (fresh [v j] (vectoro* v) (geto v i 1) (geto v j 2) (== i j))) []))
    (is (= (run* [i] (fresh [v w] (vectoro* v) (vectoro* w) (geto v i 1) (geto w i 2) (== v w))) []))
    (is (= (map pr-str (run 2 [i v x] (vectoro* v) (geto v i 1) (geto v i x)))
           ["[0 (lvec [1] | _0 | []) 1]" "[1 (lvec [_0 1] | _1 | []) 1]"])))
  (testing "assoc into a closed sequence: the index is the length of what
            comes before"
    (is (= (run* [i m] (vectoro* m) (assoco m i 9 [1 9 3])) '([1 [1 _0 3]])))
    (is (= (run* [i m] (vectoro* m) (assoco m i 9 '(1 2 9))) '([2 [1 2]] [2 [1 2 _0]])))
    ;; the split of m waits, concato of the result has finitely many
    ;; alternatives: those are tried first, and decide the split
    (is (= (run* [i m x] (fresh [a b c d] (assoco m i x (list a b c d))))
           '([3 [_0 _1 _2] _3] [0 [_0 _1 _2 _3] _4] [1 [_0 _1 _2 _3] _4]
                               [2 [_0 _1 _2 _3] _4] [3 [_0 _1 _2 _3] _4]))))
  (testing "answers that hold are kept"
    (is (= (map pr-str (run 2 [i v] (vectoro* v) (absento 2 v) (geto v i 1)))
           ["([0 (lvec [1] | _0 | [])] :- (clojure.core.logic/absento 2 _0))"
            "([1 (lvec [_0 1] | _1 | [])] :- (clojure.core.logic/absento 2 _1) (clojure.core.logic/absento 2 _0))"]))
    (is (= (map pr-str (run 2 [i v] (fresh [a] (vectoro* v) (geto v i (list a)))))
           ["[0 (lvec [(_0)] | _1 | [])]" "[1 (lvec [_0 (_1)] | _2 | [])]"]))
    ;; an element of the known front may hold the middle, one in the
    ;; middle may not
    (is (= (run* [i] (fresh [m v] (vectoro* m) (== v (lcons (list m) m)) (geto v i (list m))))
           [0]))))

(deftest test-absento-long-term
  ;; absento of an atom looks through a long term without overflowing the
  ;; stack, past nil elements, and waits on the vars it finds
  (let [long-list (fn [n tail] (reduce #(lcons %2 %1) tail (concat (range n) [nil])))]
    (is (= (run* [q] (fresh [t] (absento :a q) (== q (long-list 5000 t)) (== t (list :a)))) []))
    (is (= (run* [q] (fresh [t] (absento :a q) (== q (long-list 100 t)) (== t (list :b))))
           [(long-list 100 (list :b))]))
    (is (= (run* [q] (absento :a q) (== q (cons nil (cons :a ())))) []))))

(defn- conj-chaino
  ;; v is a vector of n elements built by n conjos on typed vectors, the
  ;; innermost bound last
  [n v]
  (if (zero? n)
    (== v [])
    (fresh [v0]
           (vectoro* v0)
           (conjo v0 n v)
           (conj-chaino (dec n) v0))))

(deftest test-conjo-on-typed-vector
  ;; conjo acts on a var whose type says it is a vector, instead of waiting
  ;; in a chain that unwinds n deep once the innermost var is bound
  (is (= (run* [v] (vectoro* v) (conj-chaino 3 v)) [[1 2 3]]))
  (is (= (count (first (run* [v] (vectoro* v) (conj-chaino 1000 v)))) 1000)))
