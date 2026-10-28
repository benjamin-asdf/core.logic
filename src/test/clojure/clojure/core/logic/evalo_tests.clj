(ns clojure.core.logic.evalo-tests
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic :exclude [is]]
        [clojure.core.logic.evalo]
        [clojure.test]))

(defn- value
  "The values expr has, starting from prim-env plus the bindings m."
  ([expr] (value expr {}))
  ([expr m] (run* [v] (eval-expo expr (env-with m) v))))

;; -----------------------------------------------------------------------------
;; forwards

(deftest test-evalo-forwards
  (are [expr v] (= (value expr) [v])
    5 5
    :a :a
    "s" "s"
    nil nil
    ''x 'x
    '((fn [x] x) 5) 5
    '((fn [x y] [y x]) 1 2) [2 1]
    '((fn [x x] x) 1 2) 2
    '(let [x 1 y [x 2]] {:a y :b (get {:c 3} :c)}) {:a [1 2] :b 3}
    '(if (= 1 2) :yes :no) :no
    '(if nil :yes) nil
    '(if [] :yes :no) :yes
    '(:a {:a 1}) 1
    '(:z {:a 1}) nil
    '({:a 1} :a) 1
    '([1 2 3] 1) 2
    '(get {:a 1} :z) nil
    '(get nil :a) nil
    '(:a [1]) nil
    () ()
    '(conj {:a 1} [:b 2]) {:a 1 :b 2}
    '(let [x 1 x [x x]] x) [1 1]
    '((fn [x] ((fn [y] [x y]) 2)) 1) [1 2]
    '((fn [f] (f f)) (fn [g] :ok)) :ok
    '(if (fn [x] x) 1 2) 1
    '(assoc {:a 1} :b 2) {:a 1 :b 2}
    '(assoc [1 2] 0 :x) [:x 2]
    '(conj [1] 2) [1 2]
    '(conj (list 1) 2) '(2 1)
    '(conj #{1} 2) #{1 2}
    '(vector 1 (list 2)) [1 '(2)]
    '#{1 :a} #{1 :a}
    '(let [f (fn [x] [x x])] (f 3)) [3 3])
  (is (vector? (first (value '(vector 1 2)))))
  (is (seq? (first (value '(list 1 2)))))
  (is (= (value 'x '{x 7}) [7])))

(deftest test-evalo-shadowing
  ;; fn and let are macros, which locals shadow; quote and if are special
  ;; forms, which they don't
  (is (= (value '(let [fn 5] fn)) [5]))
  (is (= (value '(let [if 5] (if true 1 2))) [1]))
  (is (= (value '((fn [quote] (quote 3)) 1)) [3]))
  (is (= (value '((fn [list] (list 1)) (fn [x] [x x]))) [[1 1]]))
  (is (= (value '(let [fn (fn [x] :local)] (fn 1))) [:local])))

(deftest test-evalo-not-in-the-subset
  ;; these fail rather than give a wrong value
  (is (= (value 'y) []))
  (is (= (value '(1 2)) []))
  (is (= (value '(fn (x) x)) []))
  (is (= (value '(fn [& xs] xs)) []))
  (is (= (value '((fn [x] x))) []))
  (is (= (value '(get (list 1 2) 0)) []))
  ;; a quoted fn is data, not a fn
  (is (= (value '((quote (:clojure.core.logic.evalo/prim list)) 1)) []))
  (is (= (value '(= (fn [x] x) (fn [x] x))) [])))

(deftest test-evalo-quine-forwards
  (let [quine '((fn [x] (list x (list 'quote x)))
                '(fn [x] (list x (list 'quote x))))]
    (is (= (run* [v] (evalo quine v)) [quine]))))

;; -----------------------------------------------------------------------------
;; backwards

(deftest test-evalo-synthesis
  (is (= (take 2 (run 2 [q] (evalo q 6))) '(6 (quote 6))))
  (is (some #{[1 2]} (run 10 [q] (evalo q [1 2]))))
  (is (some #{{:a 1 :b 2}} (run 10 [q] (evalo q {:a 1 :b 2})))))

(deftest test-evalo-inputs
  ;; which m has 1 at :a: any map with that entry
  (is (= (pr-str (run* [m] (eval-expo '(get m :a) (env-with {'m m}) 1)))
         "((lmap {:a 1} | _0))"))
  ;; which m did assoc start from
  (is (= (run* [m] (eval-expo '(assoc m :b 2) (env-with {'m m}) {:a 1 :b 2}))
         '({:a 1} {:a 1 :b _0})))
  (is (= (run* [x y] (eval-expo '(= [x 1] [2 y]) (env-with {'x x 'y y}) true))
         [[2 1]]))
  (is (= (run* [x] (eval-expo '(if x :yes :no) (env-with {'x x}) :no))
         [false nil]))
  ;; the key path to 1, keys written as keywords
  (is (= (run* [k1 k2]
               (keywordo k1) (keywordo k2)
               (eval-expo (list 'get (list 'get 'm k1) k2) (env-with {'m {:a {:b 1} :c 2}}) 1))
         [[:a :b]])))

(defn- fn-body
  "The first body of (fn [m] body) that maps each in to its out."
  [examples]
  (first
   (run 1 [body]
        (fresh [f]
               (eval-expo (list 'fn '[m] body) prim-env f)
               (everyg (fn [[in out]] (eval-expo (list 'f in) (env-with {'f f}) out))
                       examples)))))

(deftest test-evalo-by-example
  (is (= (fn-body [[1 [1 1]] [2 [2 2]]]) '[m m]))
  (is (= (fn-body [[{:a 1} 1] [{:a 2} 2]]) '(:a m)))
  ;; with the shape of the call given
  (is (= (first (run 1 [b]
                     (fresh [x y z] (== b (list 'assoc x y z)))
                     (eval-expo b (env-with {'m {:a 1}}) {:a 1 :b 2})
                     (absento 1 b)))
         '(assoc m :b 2))))

(deftest test-evalo-quine-search
  ;; with the shape of the quine's body given; the unshaped search doesn't
  ;; finish in minutes, see post 9
  (let [[q] (run 1 [q]
                 (fresh [x e1 e2 b]
                        (== q (list (list 'fn [x] (list 'list e1 e2)) (list 'quote b))))
                 (evalo q q))
        quine (clojure.walk/postwalk-replace {'_0 'x} (first q))]
    (is (= (run* [v] (evalo quine v)) [quine]))))
