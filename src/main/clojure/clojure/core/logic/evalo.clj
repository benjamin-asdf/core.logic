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
   - in lib-env also: + - * / quot mod inc dec max min abs < > <= >= odd?
     even? neg? pos? zero? not= count first second last rest butlast
     reverse sort nth concat range str join (clojure.string/join), and map
     (over one or two colls), filter, remove and reduce. They evaluate their
     arguments first. map, filter, remove and reduce apply fns relationally
     and take nil, lists and vectors; the others wait until their arguments
     are ground, then compute as Clojure does

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
   quoting the keywords that tag fns here fails. The lib-env primitives fail
   where Clojure throws, on fns, on maps, sets and strings as the colls of
   map, filter, remove, reduce and the sequence fns (count takes them), on
   (range) and a step of 0, and on a seq as an argument of str, which
   Clojure may print as a lazy seq's identity."
  (:refer-clojure :exclude [==])
  (:require [clojure.string])
  (:use [clojure.core.logic]
        [clojure.core.logic.protocols :only [walk lfirst lnext]]))

;; Values that are fns are tagged lists. The tags can't occur in any other
;; value: quote rejects them, they aren't self-evaluating, and no primitive
;; takes a closure apart.
(def ^:private closure-tag ::closure)
(def ^:private prim-tag ::prim)

(defn- prims [syms]
  (into {} (map (fn [p] [p (list prim-tag p)])) syms))

(def prim-env
  "The environment every expression starts in: the primitives."
  (prims '[list vector get assoc conj =]))

(def ^:private seq-hofs '[map filter remove reduce])

(defn- seq-arg? [x] (or (nil? x) (sequential? x)))

(defn- every-arg [pred] (fn [xs] (every? pred xs)))

(defn- one-arg [pred] (fn [xs] (and (= 1 (count xs)) (pred (first xs)))))

(def ^:private computed
  ;; primitive → [the Clojure fn, whether it takes the ground arguments,
  ;; the kinds the arguments may have: a set for every argument, or by
  ;; arity a set per argument, nil for any]
  (let [nums (every-arg number?)
        num (one-arg number?)
        int (one-arg integer?)
        sq (one-arg seq-arg?)
        N #{:num}
        Q #{:list :vector :nil}]
    {'+ [+ nums N] '- [- nums N] '* [* nums N] '/ [/ nums N] 'quot [quot nums N] 'mod [mod nums N]
     'inc [inc num N] 'dec [dec num N] 'max [max nums N] 'min [min nums N]
     'abs [(fn [x] (if (neg? x) (- x) x)) num N]
     '< [< nums N] '> [> nums N] '<= [<= nums N] '>= [>= nums N]
     'odd? [odd? int N] 'even? [even? int N] 'neg? [neg? num N] 'pos? [pos? num N] 'zero? [zero? num N]
     'not= [not= (constantly true) nil]
     'count [count (one-arg #(or (nil? %) (coll? %) (string? %))) #{:list :vector :nil :map :set :str}]
     'first [first sq Q] 'second [second sq Q] 'last [last sq Q] 'rest [rest sq Q]
     'butlast [butlast sq Q] 'reverse [reverse sq Q] 'sort [sort sq Q]
     'nth [nth (fn [[c i :as xs]] (and (= 2 (count xs)) (seq-arg? c) (integer? i))) {2 [Q N]}]
     'concat [concat (every-arg seq-arg?) Q]
     ;; (range) is infinite, and so is a step of 0
     'range [range (fn [xs] (and (<= 1 (count xs) 3) (every? integer? xs) (not= 0 (nth xs 2 1)))) N]
     ;; a seq here may be a lazy seq in Clojure, which str doesn't print
     'str [str (every-arg #(not (seq? %))) nil]
     'join [clojure.string/join (fn [xs] (case (count xs)
                                           1 (seq-arg? (first xs))
                                           2 (and (string? (first xs)) (seq-arg? (second xs)))
                                           false))
            {1 [Q] 2 [#{:str} Q]}]}))

(def lib-env
  "prim-env plus numbers and sequences: arithmetic, comparison, map, filter,
   remove, reduce, range, count and the like, str and join. The key ::lib,
   which no expression can look up, marks it: its primitives apply only
   where the environment has it, so that searches in prim-env don't try
   them."
  (merge prim-env (prims (concat (sort (keys computed)) seq-hofs)) {::lib true}))

(defn env-with
  "prim-env, or the environment base, with the bindings of the map m added."
  ([m] (env-with prim-env m))
  ([base m] (merge base m)))

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

;; A guide may change the order in which eval-expo and primo try their
;; clauses, never which clauses they try: the answers stay the same, only
;; which come first changes.
(defonce ^:private guide (atom nil))

(defn set-guide!
  "Order the clauses of the interpreter by (f point s ctx tags), which
   returns the clause tags in the order to try them. point is :expr, with
   ctx {:expr :env :val}, or :prim, with ctx {:p :args :val}; s is the
   substitution, to walk ctx with. f must return every tag exactly once.
   nil restores source order."
  [f]
  (reset! guide f))

(defn- guided
  "The disjunction of the [tag goal] clauses, as conde, in source order or
   in the order the guide gives."
  [point ctx clauses]
  (fn [a]
    (let [f @guide
          goals (if f
                  (let [tags (mapv first clauses)
                        order (f point a ctx tags)]
                    (when-not (and (= (count order) (count tags)) (= (set order) (set tags)))
                      (throw (ex-info "evalo guide must return every clause tag once"
                                      {:tags tags :order order})))
                    (map (into {} clauses) order))
                  (map second clauses))]
      ((or* goals) a))))

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
  ;; typed, so that conjo builds them at once instead of waiting
  (vector-formo ev)
  (vector-formo vv)
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
  (vector-formo v)
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
  (vector-formo bv)
  (conde
   [(== [] bv) (== env out)]
   [(fresh [bv0 bv1 x e v env0]
           (vector-formo bv1)
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

(defn- tagged? [x]
  (some #(or (= closure-tag %) (= prim-tag %)) (tree-seq coll? seq x)))

(defn- kind
  "The kind of the term t: of its value, or of the type constraint on it if
   it is an unbound var (nil if there is none)."
  [s t]
  (let [t (walk s t)]
    (cond
      ;; by reflection: a hint on TypeDom breaks when core.logic is reloaded
      (lvar? t) (when-let [d (get-dom s t :clojure.core.logic/type)]
                  (clojure.lang.Reflector/getInstanceField d "t"))
      (nil? t) :nil
      (number? t) :num
      (string? t) :str
      (keyword? t) :kw
      (symbol? t) :sym
      (or (lcons? t) (seq? t)) :list
      (or (vector? t) (lvec? t)) :vector
      (or (map? t) (lmap? t)) :map
      (or (set? t) (lset? t)) :set
      :else :other)))

(defn- kinds-ok?
  "Whether the args may have the kinds: false only if one has a kind they
   rule out."
  [s args kinds]
  (let [as (loop [a (walk s args) acc []]
             (cond (lcons? a) (recur (walk s (lnext a)) (conj acc (lfirst a)))
                   (lvar? a) nil
                   :else (into acc a)))
        ks (when as (if (map? kinds) (get kinds (count as)) (repeat (count as) kinds)))]
    (every? (fn [[a k]] (let [ka (kind s a)] (or (nil? k) (nil? ka) (contains? k ka))))
            (map vector as ks))))

(defn- computo
  "(p ...args) is val, p a primitive that Clojure computes: waits until the
   args are ground, then calls f if ok? takes them. Fails where ok? doesn't,
   where Clojure throws, and on fns; also as soon as an argument has a kind
   kinds rules out."
  [p f ok? kinds args val]
  (fn [s]
    (let [xs (walk* s args)]
      (cond
        (tagged? xs) nil
        (not (kinds-ok? s args kinds)) nil
        (ground-term? args s)
        (let [xs (seq xs)
              r (if (ok? xs)
                  (try (let [r (apply f xs)] (if (seq? r) (apply list r) r))
                       (catch Exception _ ::none))
                  ::none)]
          (when-not (= ::none r) ((== val r) s)))
        :else ((suspend p [args val] #(computo p f ok? kinds args val) [args]) s)))))

(defn- over-seqo
  "(g ys), ys the items of xs, which is nil, a list or a vector. A known
   vector unifies with a list; an unknown one can't, as its type says
   vector, so it is built from ys after g has said what ys is."
  [xs g]
  (fn [s]
    ((conde
      [(== nil xs) (g ())]
      [(list-formo xs) (g xs)]
      [(vector-formo xs)
       (if (lvar? (walk s xs))
         (fresh [ys] (g ys) (vector-itemso ys [] xs))
         (g xs))])
     s)))

(defn- truthyo [t] (all (!= false t) (!= nil t)))

(defn- falsyo [t] (conde [(== false t)] [(== nil t)]))

(declare apply-valo)

(defrel ^:private map1o [f xs ys]
  (conde
   [(== () xs) (== () ys)]
   [(fresh [x xs' y ys']
           (== (lcons x xs') xs)
           (== (lcons y ys') ys)
           (apply-valo f (list x) y)
           (map1o f xs' ys'))]))

(defrel ^:private map2o
  ;; as map does, stops at the end of the shorter of xs and zs
  [f xs zs ys]
  (conde
   [(== () xs) (== () ys)]
   [(fresh [x xs'] (== (lcons x xs') xs) (== () zs) (== () ys))]
   [(fresh [x xs' z zs' y ys']
           (== (lcons x xs') xs)
           (== (lcons z zs') zs)
           (== (lcons y ys') ys)
           (apply-valo f (list x z) y)
           (map2o f xs' zs' ys'))]))

(defrel ^:private filtero
  ;; ys are the xs for which f is truthy, or falsy if keep is false
  [f keep xs ys]
  (conde
   [(== () xs) (== () ys)]
   [(fresh [x xs' t]
           (== (lcons x xs') xs)
           (apply-valo f (list x) t)
           (conde
            [(if keep (truthyo t) (falsyo t))
             (fresh [ys'] (== (lcons x ys') ys) (filtero f keep xs' ys'))]
            [(if keep (falsyo t) (truthyo t))
             (filtero f keep xs' ys)]))]))

(defrel ^:private foldo [f acc xs val]
  (conde
   [(== () xs) (== acc val)]
   [(fresh [x xs' acc']
           (== (lcons x xs') xs)
           (apply-valo f (list acc x) acc')
           (foldo f acc' xs' val))]))

(defn- hofo
  "(p ...args) is val, p one of map, filter, remove and reduce."
  [p args val]
  (case p
    map (fresh [f xs zs]
               (conde
                [(== (list f xs) args) (over-seqo xs #(map1o f % val))]
                [(== (list f xs zs) args)
                 (over-seqo xs (fn [xs'] (over-seqo zs #(map2o f xs' % val))))]))
    filter (fresh [f xs] (== (list f xs) args) (over-seqo xs #(filtero f true % val)))
    remove (fresh [f xs] (== (list f xs) args) (over-seqo xs #(filtero f false % val)))
    reduce (fresh [f init xs]
                  (conde
                   [(== (list f init xs) args) (over-seqo xs #(foldo f init % val))]
                   [(== (list f xs) args)
                    (over-seqo xs
                               (fn [xs']
                                 ;; (reduce f []) is (f), (reduce f [x]) is x
                                 (conde
                                  [(== () xs') (apply-valo f () val)]
                                  [(fresh [x d] (== (lcons x d) xs') (foldo f x d val))])))]))))

(defn- lib-primo [p args val]
  (guided
   :prim {:p p :args args :val val}
   (concat
    (for [[q [f ok? kinds]] (sort-by key computed)]
      [q (all (== q p) (computo q f ok? kinds args val))])
    (for [q seq-hofs]
      [q (all (== q p) (hofo q args val))]))))

(defn- primo [p args val]
  (guided
   :prim {:p p :args args :val val}
   [['list (all (== 'list p) (== args val))]
    ['vector (all (== 'vector p) (vector-itemso args [] val))]
    ['get (all (== 'get p)
               (fresh [m k] (== (list m k) args) (geto* m k val)))]
    ['assoc (all (== 'assoc p)
                 (fresh [m k v]
                        (== (list m k v) args)
                        (conde [(map-formo m)] [(vector-formo m)])
                        (assoco m k v val)))]
    ['conj (all (== 'conj p)
                (fresh [c x] (== (list c x) args) (conj-targeto c) (conjo c x val)))]
    ['= (all (== '= p)
             (fresh [a b]
                    (== (list a b) args)
                    (no-tagso a)
                    (no-tagso b)
                    (conde
                     [(== a b) (== true val)]
                     [(!= a b) (== false val)])))]]))

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

(def ^:private lib-prims (set (filter symbol? (remove (set (keys prim-env)) (keys lib-env)))))

(defn- lib-prim-or-varo
  "p is not known to be other than a lib-env primitive: a cheap check before
   evaluating arguments, which doesn't enumerate an unknown p (lib-primo
   binds it)."
  [p]
  (fn [s]
    (let [p (walk s p)]
      (when (or (lvar? p) (lib-prims p)) s))))

(defn- apply-valo
  "f applied to the values args is val."
  [f args val]
  (conde
   [(fresh [params body cenv env']
           (== (list closure-tag params body cenv) f)
           (bindo params args cenv env')
           (eval-expo body env' val))]
   [(fresh [p]
           (== (list prim-tag p) f)
           (conde
            [(primo p args val)]
            [(lib-primo p args val)]))]
   [(keywordo f) (not-tago f)
    (fresh [m] (== (list m) args) (geto* m f val))]
   [(map-formo f)
    (fresh [k] (== (list k) args) (geto* f k val))]
   [(vector-formo f)
    (fresh [i] (== (list i) args) (geto f i val))]))

(defn- applyo
  "(f ...rands) evaluates to val in env, f being the value of the operator.
   A closure's arguments are evaluated first, so that its body runs on
   known values; for the primitives of prim-env and data used as fns, val
   says more about the arguments than the other way round, so they come
   second. The primitives lib-env adds take their arguments first: they
   compute, or apply fns."
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
          [(fresh [p]
                  (== (list prim-tag p) f)
                  (geto env ::lib true)
                  (same-counto rands args)
                  (lib-prim-or-varo p)
                  (eval-listo rands env args)
                  (lib-primo p args val))]
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

;; An environment with the key ::constants, a vector, is a language for
;; synthesis: its constants are those, and it has no quote and no map or set
;; literals, whose contents would be constants too. Like ::lib, no
;; expression can look the key up. The checks take a plain map at once, so
;; that searches without the key branch as before.

(defn- constanto
  "expr is a constant env allows."
  [env expr]
  (fn [s]
    (let [e (walk s env)]
      (if (map? e)
        (if-let [cs (get e ::constants)] ((membero expr cs) s) s)
        ((conde
          [(lacks-keyo env ::constants)]
          [(fresh [cs] (geto env ::constants cs) (membero expr cs))])
         s)))))

(defn- literalso
  "env allows quote, map and set literals."
  [env]
  (fn [s]
    (let [e (walk s env)]
      (if (map? e)
        (when-not (contains? e ::constants) s)
        ((lacks-keyo env ::constants) s)))))

(defrel eval-expo
  "expr evaluates to val in the environment env, a map from symbols to
   values."
  [expr env val]
  (guided
   :expr {:expr expr :env env :val val}
   [[:const (all (constanto env expr)
                 (conde
                  [(numbero expr)]
                  [(stringo expr)]
                  [(keywordo expr) (not-tago expr)]
                  [(== true expr)]
                  [(== false expr)]
                  [(== nil expr)])
                 (== expr val))]
    [:empty (all (== () expr) (list-formo expr) (== () val))]
    [:sym (all (symbolo expr) (geto env expr val))]
    [:quote (fresh [x]
                   (literalso env)
                   (== (list 'quote x) expr)
                   (list-formo expr)
                   (no-tagso x)
                   (== x val))]
    [:if (fresh [c a b t]
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
    [:fn (fresh [params body]
                (== (list 'fn params body) expr)
                (list-formo expr)
                (lacks-keyo env 'fn)
                (vector-formo params)
                (symbol-veco params)
                (== (list closure-tag params body env) val))]
    [:let (fresh [bv body env']
                 (== (list 'let bv body) expr)
                 (list-formo expr)
                 (lacks-keyo env 'let)
                 (vector-formo bv)
                 (let-bindo bv env env')
                 (eval-expo body env' val))]
    [:app (fresh [rator rands f]
                 (== (lcons rator rands) expr)
                 (list-formo expr)
                 (!= 'quote rator)
                 (!= 'if rator)
                 (eval-expo rator env f)
                 (applyo f rands env val))]
    [:vec (all (vector-formo expr) (vector-formo val) (eval-veco expr env val))]
    [:map (all (literalso env) (map-formo expr) (map-formo val) (eval-mapo expr env val))]
    [:set (all (literalso env) (set-formo expr) (set-formo val) (eval-seto expr val))]]))

(defn evalo
  "expr evaluates to val, starting from prim-env."
  [expr val]
  (eval-expo expr prim-env val))
