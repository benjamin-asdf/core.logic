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

(deftest test-evalo-quine-search-fn-shape
  ;; only the outer shape ((fn [x] body) 'b) given: a few seconds, since
  ;; vectors in the search are built at once and an element can't hold the
  ;; vector it is in
  (let [[q] (run 1 [q]
                 (fresh [x body b]
                        (== q (list (list 'fn [x] body) (list 'quote b))))
                 (evalo q q))
        quine (clojure.walk/postwalk-replace {'_0 'x} (first q))]
    (is (= (run* [v] (evalo quine v)) [quine]))))

;; -----------------------------------------------------------------------------
;; lib-env: numbers and sequences

(defn- lib-value
  ([expr] (lib-value expr {}))
  ([expr m] (run* [v] (eval-expo expr (env-with lib-env m) v))))

(deftest test-evalo-lib-forwards
  (are [expr m want] (= (lib-value expr m) [want])
    '(+ a b) '{a 1.5 b 2} 3.5
    '(count (filter odd? v)) '{v [1 2 3 5]} 3
    '(= a (reverse b)) '{a [1 2] b [2 1]} true
    '(map + a b) '{a [1 2 3] b [10 20]} '(11 22)
    '(join "\n" (map count (reverse v))) '{v ["ab" "c"]} "1\n2"
    '(/ (reduce + v) (count v)) '{v [1.0 2.0]} 1.5
    '(map (fn [x] (max 0 x)) v) '{v [-1 3]} '(0 3)
    '(second (sort (vector a b c))) '{a 3 b 1 c 2} 2
    '(join "\n" (range a b s)) '{a 0 b 7 s 3} "0\n3\n6"
    '(reduce + v) '{v []} 0
    '(reduce + v) '{v [4]} 4
    '(reduce (fn [acc x] (conj acc x)) (list) v) '{v [1 2]} '(2 1)
    '(remove odd? v) '{v [1 2 3 4]} '(2 4)
    '(filter (fn [x] (if (odd? x) nil x)) v) '{v [1 2 3 4]} '(2 4)
    '(map :a v) '{v [{:a 1} {:a 2}]} '(1 2)
    '(count {:a 1}) {} 1
    '(conj (map inc v) 0) '{v [1]} '(0 2)
    '(map inc nil) {} ())
  (testing "map's value is a list, which conj adds to at the front"
    (is (seq? (first (lib-value '(map inc [1])))))))

(deftest test-evalo-lib-not-in-the-subset
  ;; these fail rather than give a wrong value
  (are [expr] (= (lib-value expr) [])
    '(map inc {:a 1})
    '(range 0 5 0)
    '(inc :a)
    '(count (fn [x] x))
    '(first "ab")
    '(str (map inc [1]))
    '(quot 1 0))
  (testing "prim-env doesn't have them"
    (is (= (value '(inc 1)) []))))

(deftest test-evalo-lib-modes
  (testing "computed primitives wait for their arguments, and run once they come"
    (is (= (run* [q] (fresh [x] (eval-expo '(+ x 1) (env-with lib-env {'x x}) q)))
           '[(_0 :- (+ (_1 1) _0))]))
    (is (= (run* [q] (fresh [x] (eval-expo '(+ x 1) (env-with lib-env {'x x}) q) (== x 4)))
           [5])))
  (testing "a kind they rule out fails at once"
    (is (= (run* [q] (fresh [x] (numbero x) (eval-expo '(count x) (env-with lib-env {'x x}) q))) [])))
  (testing "map runs backwards: the coll, as a list and as a vector"
    (let [vs (run* [v] (eval-expo '(map (fn [x] [x x]) v) (env-with lib-env {'v v}) '([1 1] [2 2])))]
      (is (= vs ['(1 2) [1 2]]))
      (is (= [false true] (map vector? vs)))))
  (testing "which one-argument primitive takes [1 2 3] to 3"
    (is (= (set (run* [op] (symbolo op) (eval-expo (list op 'v) (env-with lib-env '{v [1 2 3]}) 3)))
           '#{count last}))))

(deftest test-evalo-constants
  ;; an environment with ::constants: those constants only, no quote, no
  ;; map or set literals
  (let [env (env-with lib-env {:clojure.core.logic.evalo/constants [0 "\n" :a] 'v [1 2]})
        value #(run* [q] (eval-expo % env q))]
    (is (= (value 0) [0]))
    (is (= (value 5) []))
    (is (= (value '(:a {:a 1})) []))
    (is (= (value '(quote x)) []))
    (is (= (value '#{0}) []))
    (is (= (value '[0 v]) [[0 [1 2]]]))
    (is (= (value '((fn [x] (if x 5 0)) v)) []))
    (is (= (value '((fn [x] (if x 0 5)) v)) [0]))
    (testing "the constants a search can use"
      (is (= (set (run* [c] (conde [(numbero c)] [(stringo c)] [(keywordo c)]) (eval-expo c env c)))
             #{0 "\n" :a})))))
