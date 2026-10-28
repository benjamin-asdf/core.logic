(ns clojure.core.logic.evalo
  "A relational interpreter for a subset of Clojure, in the style of
   faster-miniKanren's evalo, but over Clojure's own data: the environment
   is a relational map from symbols to values, and vector, map and set
   literals are vectors, maps and sets.

   (eval-expo expr env val) holds when expr evaluates to val in env. It runs
   in every direction: evaluate, find inputs, or synthesize expressions.

   The subset:
   - numbers, strings, keywords, true, false, nil and () evaluate to
     themselves
   - symbols are looked up in env
   - (quote x)
   - (if c a b) and (if c a); false and nil are false, as in Clojure
   - (fn [x ...] body): one arity, one body expression, no & rest args
   - (let [x e ...] body): sequential bindings, one body expression
   - application of fns, of the primitives in prim-env, and of keywords,
     maps and vectors as fns, as in Clojure
   - vector literals; map literals whose keys are keywords, numbers or
     strings; set literals of keywords, numbers and strings
   - primitives: list, vector, get, assoc, conj, =

   quote and if are special forms, so a local of that name never makes
   (quote x) or (if ...) an application. fn and let are macros in Clojure,
   and a local of that name shadows them, as here.

   An expression outside the subset has no value: evalo fails on it, in
   every mode. Left out: def, do, loop/recur, multi-arity and variadic fns,
   destructuring, more than one body expression, map keys and set elements
   that are not constants, chars, and the rest of clojure.core. Where
   Clojure would return nil, evalo fails instead for: get with an index a
   vector lacks or a non-keyword key on a vector, get on a list, and
   assoc on nil. = fails on fns, which Clojure compares by identity, and
   quoting the keywords that tag fns here fails."
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic]
        [clojure.core.logic.protocols :only [walk]]))

;; Values that are fns are tagged lists. The tags can't occur in any other
;; value: quote rejects them, they aren't self-evaluating, and no primitive
;; takes a closure apart.
(def ^:private closure-tag ::closure)
(def ^:private prim-tag ::prim)

(def prim-env
  "The environment every expression starts in: the primitives."
  (into {} (map (fn [p] [p (list prim-tag p)]))
        '[list vector get assoc conj =]))

(defn env-with
  "prim-env with the bindings of the map m added."
  [m]
  (merge prim-env m))

(def ^:private suspend @#'clojure.core.logic/lmap-suspend)

;; Lists and vectors unify, as they are = in Clojure, but code tells them
;; apart. These are type constraints like symbolo: an unbound var gets the
;; kind as its type, so it can't also become a number, or a list and a
;; vector at once.
(def ^:private typeo @#'clojure.core.logic/typeo)

(defn- list-formo [x] (typeo :list `listo x))
(defn- vector-formo [x] (typeo :vector `vectoro x))
(defn- map-formo [x] (typeo :map `mapo x))
(defn- set-formo [x] (typeo :set `seto x))

(defn- const-key? [k]
  (and (or (keyword? k) (number? k) (string? k))
       (not= k closure-tag)
       (not= k prim-tag)))

(defn- not-tago [x]
  (all (!= x closure-tag) (!= x prim-tag)))

(defn- no-tagso [x]
  (all (absento closure-tag x) (absento prim-tag x)))

(declare eval-expo)

(defrel ^:private eval-listo [es env vs]
  (conde
   [(== () es) (== () vs)]
   [(fresh [a d va vd]
           (== (lcons a d) es)
           (== (lcons va vd) vs)
           (eval-expo a env va)
           (eval-listo d env vd))]))

(defrel ^:private eval-veco
  ;; ev and vv are vectors of the same length, each element of vv the
  ;; value of the element of ev at the same index
  [ev env vv]
  (conde
   [(== [] ev) (== [] vv)]
   [(fresh [e es v vs]
           (conjo es e ev)
           (conjo vs v vv)
           (eval-veco es env vs)
           (eval-expo e env v))]))

(defn- closed-keys
  "The keys of the walked map m if it is a plain map with ground keys."
  [s m]
  (when (and (map? m) (every? #(ground-term? % s) (keys m)))
    (map #(walk* s %) (keys m))))

(defn- consto
  "x is a constant that may be a map key or set element in a literal."
  [x]
  (conde
   [(keywordo x) (not-tago x)]
   [(numbero x)]
   [(stringo x)]))

(defn- map-literalo
  "em is a map literal of n entries evaluating to vm."
  [n em env vm]
  (let [ks (vec (repeatedly n lvar))
        es (zipmap ks (repeatedly lvar))
        vs (zipmap ks (repeatedly lvar))]
    (all (== em es)
         (== vm vs)
         (everyg consto ks)
         (everyg #(eval-expo (es %) env (vs %)) ks))))

(defrel ^:private map-literal-sizeso
  ;; em is a map literal of n or more entries evaluating to vm
  [n em env vm]
  (conde
   [(map-literalo n em env vm)]
   [(map-literal-sizeso (inc n) em env vm)]))

(defn- eval-mapo
  "A map literal em evaluates to the map vm: the same keys, each value
   evaluated. Lists map literals by size if neither is known, and waits
   while one is partly known."
  [em env vm]
  (fn [s]
    (let [em' (walk s em) vm' (walk s vm)
          ks (or (closed-keys s em') (closed-keys s vm'))]
      (cond
        ks (when (every? const-key? ks)
             (let [es (zipmap ks (repeatedly lvar))
                   vs (zipmap ks (repeatedly lvar))]
               ((all (== em es)
                     (== vm vs)
                     (everyg #(eval-expo (es %) env (vs %)) ks))
                s)))
        (and (lvar? em') (lvar? vm')) ((map-literal-sizeso 0 em env vm) s)
        :else ((suspend `eval-mapo [em env vm] #(eval-mapo em env vm) [em vm]) s)))))

(defn- set-literalo
  "es is a set literal of n constants, and so its own value vs."
  [n es vs]
  (let [xs (repeatedly n lvar)]
    (all (== es (set xs))
         (== vs es)
         (everyg consto xs))))

(defrel ^:private set-literal-sizeso [n es vs]
  (conde
   [(set-literalo n es vs)]
   [(set-literal-sizeso (inc n) es vs)]))

(defn- eval-seto
  "A set literal of constants es evaluates to itself. Lists set literals
   by size if neither is known, and waits while one is partly known."
  [es vs]
  (fn [s]
    (let [e (walk* s es) v (walk* s vs)
          lit (cond (and (set? e) (ground-term? e s)) e
                    (and (set? v) (ground-term? v s)) v)]
      (cond
        lit (when (every? const-key? lit) ((all (== es lit) (== vs lit)) s))
        (and (lvar? e) (lvar? v)) ((set-literal-sizeso 0 es vs) s)
        :else ((suspend `eval-seto [es vs] #(eval-seto es vs) [es vs]) s)))))

(defrel ^:private symbol-veco
  ;; v is a vector of symbols, none of them &
  [v]
  (conde
   [(== [] v)]
   [(fresh [v0 p]
           (conjo v0 p v)
           (symbolo p)
           (!= p '&)
           (symbol-veco v0))]))

(defrel ^:private bindo
  ;; out is env with params bound to args, left to right
  [params args env out]
  (conde
   [(== [] params) (== () args) (== env out)]
   [(fresh [p ps a as env1]
           (== (lcons p ps) params)
           (== (lcons a as) args)
           (assoco env p a env1)
           (bindo ps as env1 out))]))

(defrel ^:private let-bindo
  ;; out is env extended by the let bindings bv, one after the other
  [bv env out]
  (conde
   [(== [] bv) (== env out)]
   [(fresh [bv0 bv1 x e v env0]
           (conjo bv1 e bv)
           (conjo bv0 x bv1)
           (let-bindo bv0 env env0)
           (symbolo x)
           (eval-expo e env0 v)
           (assoco env0 x v out))]))

(defrel ^:private vector-itemso
  ;; out is the vector acc followed by the items of the list xs
  [xs acc out]
  (conde
   [(== () xs) (== acc out)]
   [(fresh [a d acc']
           (== (lcons a d) xs)
           (conjo acc a acc')
           (vector-itemso d acc' out))]))

(defn- geto*
  "(get m k) is v, for a map, a vector or nil m. A key a map lacks, a
   keyword on a vector and anything on nil give nil, as in Clojure; an index
   a vector lacks fails."
  [m k v]
  (conde
   [(map-formo m)
    (conde
     [(geto m k v)]
     [(lacks-keyo m k) (== nil v)])]
   [(vector-formo m)
    (conde
     [(geto m k v)]
     [(keywordo k) (== nil v)])]
   [(== nil m) (== nil v)]))

(defn- conj-targeto
  "c is a collection conj takes: a vector, set or map, or a list that is not
   a fn."
  [c]
  (conde
   [(vector-formo c)]
   [(set-formo c)]
   [(map-formo c)]
   [(list-formo c)
    (conde
     [(== () c)]
     [(fresh [h t] (== (lcons h t) c) (not-tago h))])]))

(defn- primo [p args val]
  (conde
   [(== 'list p) (== args val)]
   [(== 'vector p) (vector-itemso args [] val)]
   [(== 'get p)
    (fresh [m k] (== (list m k) args) (geto* m k val))]
   [(== 'assoc p)
    (fresh [m k v]
           (== (list m k v) args)
           (conde [(map-formo m)] [(vector-formo m)])
           (assoco m k v val))]
   [(== 'conj p)
    (fresh [c x] (== (list c x) args) (conj-targeto c) (conjo c x val))]
   [(== '= p)
    (fresh [a b]
           (== (list a b) args)
           (no-tagso a)
           (no-tagso b)
           (conde
            [(== a b) (== true val)]
            [(!= a b) (== false val)]))]))

(defrel ^:private same-counto
  ;; the lists xs and ys have the same length
  [xs ys]
  (conde
   [(== () xs) (== () ys)]
   [(fresh [x xs' y ys']
           (== (lcons x xs') xs)
           (== (lcons y ys') ys)
           (same-counto xs' ys'))]))

(defrel ^:private same-lengtho
  ;; the vector params and the list rands have the same length
  [params rands]
  (conde
   [(== [] params) (== () rands)]
   [(fresh [p ps r rs]
           (== (lcons p ps) params)
           (== (lcons r rs) rands)
           (same-lengtho ps rs))]))

(defn- applyo
  "(f ...rands) evaluates to val in env, f being the value of the operator.
   A closure's arguments are evaluated first, so that its body runs on
   known values; for primitives and data used as fns, val says more about
   the arguments than the other way round, so they come second."
  [f rands env val]
  (fresh [args]
         (conde
          [(fresh [params body cenv env']
                  (== (list closure-tag params body cenv) f)
                  (symbol-veco params)
                  (same-lengtho params rands)
                  (eval-listo rands env args)
                  (bindo params args cenv env')
                  (eval-expo body env' val))]
          [(fresh [p]
                  (== (list prim-tag p) f)
                  (same-counto rands args)
                  (primo p args val))
           (eval-listo rands env args)]
          ;; (:k m), (m k) and (v i), as in Clojure
          [(keywordo f) (not-tago f)
           (fresh [m] (== (list m) args) (geto* m f val))
           (eval-listo rands env args)]
          [(map-formo f)
           (fresh [k] (== (list k) args) (geto* f k val))
           (eval-listo rands env args)]
          [(vector-formo f)
           (fresh [i] (== (list i) args) (geto f i val))
           (eval-listo rands env args)])))

(defrel eval-expo
  "expr evaluates to val in the environment env, a map from symbols to
   values."
  [expr env val]
  (conde
   [(conde
     [(numbero expr)]
     [(stringo expr)]
     [(keywordo expr) (not-tago expr)]
     [(== true expr)]
     [(== false expr)]
     [(== nil expr)])
    (== expr val)]
   [(== () expr) (list-formo expr) (== () val)]
   [(symbolo expr) (geto env expr val)]
   [(fresh [x]
           (== (list 'quote x) expr)
           (list-formo expr)
           (no-tagso x)
           (== x val))]
   [(fresh [c a b t]
           (conde
            [(== (list 'if c a b) expr)]
            [(== (list 'if c a) expr) (== nil b)])
           (list-formo expr)
           (eval-expo c env t)
           (conde
            [(conde [(== false t)] [(== nil t)])
             (eval-expo b env val)]
            [(!= false t) (!= nil t)
             (eval-expo a env val)]))]
   [(fresh [params body]
           (== (list 'fn params body) expr)
           (list-formo expr)
           (lacks-keyo env 'fn)
           (vector-formo params)
           (symbol-veco params)
           (== (list closure-tag params body env) val))]
   [(fresh [bv body env']
           (== (list 'let bv body) expr)
           (list-formo expr)
           (lacks-keyo env 'let)
           (vector-formo bv)
           (let-bindo bv env env')
           (eval-expo body env' val))]
   [(fresh [rator rands f]
           (== (lcons rator rands) expr)
           (list-formo expr)
           (!= 'quote rator)
           (!= 'if rator)
           (eval-expo rator env f)
           (applyo f rands env val))]
   [(vector-formo expr) (vector-formo val) (eval-veco expr env val)]
   [(map-formo expr) (map-formo val) (eval-mapo expr env val)]
   [(set-formo expr) (set-formo val) (eval-seto expr val)]))

(defn evalo
  "expr evaluates to val, starting from prim-env."
  [expr val]
  (eval-expo expr prim-env val))
