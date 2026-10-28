;   Copyright (c) David Nolen, Rich Hickey, contributors. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns clojure.core.logic
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic.protocols])
  (:require [clojure.set :as set]
            [clojure.string :as string])
  (:import [java.io Writer]
           [java.util UUID]
           [clojure.core.logic.protocols
            IBindable ITreeTerm IVar ITreeConstraint INonStorable]))

(defmacro ^:private compile-when
  ([exp then]
   (if (try (eval exp)
            (catch Throwable _ false))
     `(do ~then))))

(def ^{:dynamic true} *locals*)

(def fk (Exception.))

;; =============================================================================
;; Utilities

(defn assoc-meta [x k v]
  (with-meta x (assoc (meta x) k v)))

(defn dissoc-meta [x k]
  (with-meta x (dissoc (meta x) k)))

(defn assoc-dom [x k v]
  (assoc x :doms (assoc (:doms x) k v)))

(defn dissoc-dom [x k]
  (assoc x :doms (dissoc (:doms x) k)))

(compile-when (not (resolve 'clojure.core/record?))
              (defn record? [x]
                (instance? clojure.lang.IRecord x)))

;; =============================================================================
;; Pair

(deftype Pair [lhs rhs]
  clojure.lang.ILookup
  (valAt [this k]
    (.valAt this k nil))
  (valAt [this k not-found]
    (case k
      :lhs lhs
      :rhs rhs
      not-found))

  clojure.lang.Counted
  (count [_] 2)

  clojure.lang.Indexed
  (nth [_ i] (case i
               0 lhs
               1 rhs
               (throw (IndexOutOfBoundsException.))))
  (nth [_ i not-found] (case i
                         0 lhs
                         1 rhs
                         not-found))

  java.util.Map$Entry
  (getKey [_] lhs)
  (getValue [_] rhs)

  Object
  (toString [_]
    (str "(" lhs " . " rhs ")"))

  (equals [_ o]
    (if (instance? Pair o)
      (and (= lhs (:lhs o))
           (= rhs (:rhs o)))
      false)))

(defn pair [lhs rhs]
  (Pair. lhs rhs))

(defmethod print-method Pair [x ^Writer writer]
  (.write writer (str "(" (:lhs x) " . " (:rhs x) ")")))

;; =============================================================================
;; Constraint Store

(declare lvar? bindable? add-var)

(defn var-rands [a c]
  (->> (-rands c)
       (map #(root-var a %))
       (filter lvar?)
       (into [])))

(defn unbound-rands [a c]
  (->> (var-rands a c)
       (filter #(lvar? (root-val a %)))))

;; ConstraintStore
;; -----
;; km  - mapping logic vars to constraints ids
;; cm  - mapping constraint ids to to actual constraints
;; cid - the current constraint id, an integer, incremented
;;       everytime we add a constraint to the store
;; running - set of running constraint ids

(deftype ConstraintStore [km cm cid running]
  clojure.lang.ILookup
  (valAt [this k]
    (.valAt this k nil))
  (valAt [this k not-found]
    (case k
      :km km
      :cm cm
      :cid cid
      :running running
      not-found))

  IConstraintStore
  (addc [this a c]
    (when (or (not (instance? clojure.core.logic.protocols.IVerifyConstraint c))
              (-verify c a this))
      (let [vars (var-rands a c)
            c    (with-id c cid)
            cs   (reduce (fn [cs v] (add-var cs v c)) this vars)]
        (ConstraintStore. (:km cs) (:cm cs) (inc cid) running))))

  (updatec [this a c]
    (let [oc (cm (id c))
          nkm (if (instance? clojure.core.logic.protocols.IEntailedVar c)
                (reduce (fn [km x]
                          (if (-entailed-var? c x)
                            (dissoc km x)
                            km))
                        km (var-rands a oc))
                km)]
      (ConstraintStore. nkm (assoc cm (id c) c) cid running)))

  (remc [this a c]
    (let [vs (var-rands a c)
          ocid (id c)
          nkm (reduce (fn [km v]
                        (let [vcs (disj (get km v) ocid)]
                          (if (empty? vcs)
                            (dissoc km v)
                            (assoc km v vcs))))
                      km vs)
          ncm (dissoc cm ocid)]
      (ConstraintStore. nkm ncm cid running)))

  (runc [this c state]
    (if state
      (ConstraintStore. km cm cid (conj running (id c)))
      (ConstraintStore. km cm cid (disj running (id c)))))

  (constraints-for [this a x ws]
    (when-let [ids (get km (root-var a x))]
      (filter #((-watched-stores %) ws) (map cm (remove running ids)))))

  (migrate [this x root a]
    (let [xcs    (km x)
          rootcs (km root #{})
          nkm    (assoc (dissoc km x) root (into rootcs xcs))]
      (when (every?
             (fn [c]
               (if (instance? clojure.core.logic.protocols.IVerifyConstraint c)
                 (-verify c a this)
                 true))
             (map cm xcs))
        (ConstraintStore. nkm cm cid running))))

  clojure.lang.Counted
  (count [this]
    (count cm)))

(defn add-var [cs x c]
  (when-not (lvar? x)
    (throw (Error. (str "constraint store assoc expected logic var key: " x))))
  (let [cm (:cm cs)
        km (:km cs)
        cid (:cid cs)
        nkm (update-in km [x] (fnil (fn [s] (conj s cid)) #{}))
        ncm (assoc cm cid c)]
    (ConstraintStore. nkm ncm cid (:running cs))))

(defn make-cs []
  (ConstraintStore. {} {} 0 #{}))

;; =============================================================================
;; SubstValue
;; v - the actual ground value of the var
;; doms - the constraint domains assigned to the var
;; eset - set of other vars this var is entangled with

(defrecord SubstValue [v doms eset]
  Object
  (toString [_]
    (str v)))

(defn subst-val? [x]
  (instance? SubstValue x))

(defn subst-val
  ([x] (SubstValue. x nil nil))
  ([x doms] (SubstValue. x doms nil))
  ([x doms _meta] (with-meta (SubstValue. x doms nil) _meta))
  ([x doms eset _meta] (with-meta (SubstValue. x doms eset) _meta)))

;; =============================================================================
;; Substitutions

(declare empty-s choice lvar lvar? pair lcons run-constraints*)

(defn occurs-check [s u v]
  (let [v (walk s v)]
    (occurs-check-term v u s)))

(declare check-map-keys)

;; Maps the occurs check met whose keys are not plain values (see
;; check-map-keys), per thread since the occurs check cannot return them,
;; as [n map] where n is the value of keyed-maps-count after adding it.
;; ext only looks at them when the count moved during its occurs check.
(def ^:private keyed-maps-seen
  (proxy [ThreadLocal] []
    (initialValue [] (java.util.ArrayList.))))

(def ^:private ^java.util.concurrent.atomic.AtomicLong keyed-maps-count
  (java.util.concurrent.atomic.AtomicLong.))

(defn- note-keyed-map [m]
  (.add ^java.util.List (.get ^ThreadLocal keyed-maps-seen)
        [(.incrementAndGet keyed-maps-count) m]))

(defn- take-keyed-maps
  "The maps noted on this thread since keyed-maps-count was n, forgetting
   all noted maps."
  [n]
  (let [^java.util.List seen (.get ^ThreadLocal keyed-maps-seen)
        maps (into [] (keep (fn [[i m]] (when (> i n) m))) seen)]
    (.clear seen)
    maps))

(defn- ext-occurs-checked [s u v]
  (let [n (.get keyed-maps-count)]
    (if (occurs-check s u (if (subst-val? v) (:v v) v))
      (do (when-not (clojure.core/== n (.get keyed-maps-count))
            (take-keyed-maps n))
          nil)
      (let [s (ext-no-check s u v)]
        (if (clojure.core/== n (.get keyed-maps-count))
          s
          (let [maps (take-keyed-maps n)]
            (if (seq maps)
              (check-map-keys s maps)
              s)))))))

(defn ext [s u v]
  (if (:oc s)
    (ext-occurs-checked s u v)
    (ext-no-check s u v)))

(declare tree-term?)

(defn walk* [s v]
  (let [v (walk s v)]
    (walk-term v
               (fn [x]
                 (let [x (walk s x)]
                   (if (tree-term? x)
                     (walk* s x)
                     x))))))

(defn unify [s u v]
  (if (identical? u v)
    s
    (let [u (walk s u)
          v (walk s v)]
      ;; TODO: we can't use an identical? check here at the moment
      ;; because we add metadata on vars in walk - David
      (if (and (lvar? u) (= u v))
        s
        (if (and (not (lvar? u)) (lvar? v))
          (unify-terms v u s)
          (unify-terms u v s))))))

(def unbound-names
  (let [r (range 100)]
    (zipmap r (map (comp symbol str) (repeat "_") r))))

(defn reify-lvar-name [s]
  (let [c (count s)]
    (if (< c 100)
      (unbound-names c)
      (symbol (str "_" (count s))))))

(defn -reify* [s v]
  (let [v (walk s v)]
    (reify-term v s)))

(defn -reify
  ([s v]
   (let [v (walk* s v)]
     (walk* (-reify* (with-meta empty-s (meta s)) v) v)))
  ([s v r]
   (let [v (walk* s v)]
     (walk* (-reify* r v) v))))

(defn build [s u]
  (build-term u s))

(declare empty-s make-s)

;; Substitutions
;; -----
;; s   - persistent hashmap to store logic var bindings
;; vs  - changed var set
;; ts  - atom containing a hashmap of
;;       tabled goals -> atoms of sets containing cached answers
;; cs  - constraint store
;; cq  - for the constraint queue
;; cqs - constraint ids in the queue
;; oc  - occurs check

(deftype Substitutions [s vs ts cs cq cqs oc _meta]
  Object
  (equals [this o]
    (or (identical? this o)
        (and (.. this getClass (isInstance o))
             (= s (:s o)))))
  ;; TODO: prn doesn't work anymore on empty-s, why not?
  (toString [_] (str s))

  clojure.lang.Counted
  (count [this] (count s))

  clojure.lang.IObj
  (meta [this] _meta)
  (withMeta [this new-meta]
    (Substitutions. s vs ts cs cq cqs oc new-meta))

  clojure.lang.ILookup
  (valAt [this k]
    (.valAt this k nil))
  (valAt [this k not-found]
    (case k
      :s   s
      :vs  vs
      :ts  ts
      :cs  cs
      :cq  cq
      :cqs cqs
      :oc  oc
      not-found))

  clojure.lang.IPersistentCollection
  (cons [this [k v]]
    (if (lvar? k)
      (assoc this k v)
      (throw (Exception. (str "key must be a logic var")))))
  (empty [this] empty-s)
  (equiv [this o]
    (.equals this o))

  clojure.lang.Associative
  (containsKey [this k]
    (contains? #{:s :vs :cs :cq :cqs :oc} k))
  (entryAt [this k]
    (case k
      :s   [:s s]
      :vs  [:vs vs]
      :ts  [:ts ts]
      :cs  [:cs cs]
      :cq  [:cq cq]
      :cqs [:cqs cqs]
      :oc  [:oc cqs]
      nil))
  (assoc [this k v]
    (case k
      :s   (Substitutions. v vs ts cs cq cqs oc _meta)
      :vs  (Substitutions. s  v ts cs cq cqs oc _meta)
      :ts  (Substitutions. s vs  v cs cq cqs oc _meta)
      :cs  (Substitutions. s vs ts  v cq cqs oc _meta)
      :cq  (Substitutions. s vs ts cs  v cqs oc _meta)
      :cqs (Substitutions. s vs ts cs cq   v oc _meta)
      :oc  (Substitutions. s vs ts cs cq cqs  v _meta)
      (throw (Exception. (str "Substitutions has no field for key" k)))))

  ISubstitutions
  (ext-no-check [this u v]
    (let [u (if-not (lvar? v)
              (assoc-meta u ::root true)
              u)]
      (Substitutions. (assoc s u v) (if vs (conj vs u)) ts cs cq cqs oc _meta)))

  (walk [this v]
    (if (bindable? v)
      (loop [lv v me (find s v)]
        (if (nil? me)
          lv
          (let [v  (key me)
                vp (val me)]
            (if (not (bindable? vp))
              (if (subst-val? vp)
                (let [sv (:v vp)]
                  (if (identical? sv ::unbound)
                    (with-meta v (assoc (meta vp) ::unbound true))
                    sv))
                vp)
              (recur vp (find s vp))))))
      v))

  ISubstitutionsCLP
  (root-val [this v]
    (if (lvar? v)
      (loop [lv v [v vp :as me] (find s v)]
        (cond
          (nil? me) lv
          (not (lvar? vp)) vp
          :else (recur vp (find s vp))))
      v))

  (root-var [this v]
    (if (lvar? v)
      (if (-> v meta ::root)
        v
        (loop [lv v [v vp :as me] (find s v)]
          (cond
            (nil? me) lv

            (not (lvar? vp))
            (if (subst-val? vp)
              (with-meta v (meta vp))
              v)

            :else (recur vp (find s vp)))))
      v))

  (ext-run-cs [this x v]
    (let [x  (root-var this x)
          xs (if (lvar? v)
               [x (root-var this v)]
               [x])
          s  (if oc
               (ext this x v)
               (ext-no-check this x v))]
      (when s
        ((run-constraints* xs cs ::subst) s))))

  (queue [this c]
    (let [id (id c)]
      (if-not (cqs id)
        (-> this
            (assoc :cq (conj (or cq []) c))
            (assoc :cqs (conj cqs id)))
        this)))

  (update-var [this x v]
    (assoc this :s (assoc (:s this) x v)))

  IBind
  (bind [this g]
    (g this))
  IMPlus
  (mplus [this f]
    (choice this f))
  ITake
  (take* [this] this))

(defn add-attr [s x attr attrv]
  (let [x (root-var s x)
        v (root-val s x)]
    (if (subst-val? v)
      (update-var s x (assoc-meta v attr attrv))
      (let [v (if (lvar? v) ::unbound v)]
        (ext-no-check s x (with-meta (subst-val v) {attr attrv}))))))

(defn rem-attr [s x attr]
  (let [x (root-var s x)
        v (root-val s x)]
    (if (subst-val? v)
      (let [new-meta (dissoc (meta v) attr)]
        (if (and (zero? (count new-meta)) (not= (:v v) ::unbound))
          (update-var s x (:v v))
          (update-var s x (with-meta v new-meta))))
      s)))

(defn get-attr [s x attr]
  (let [v (root-val s x)]
    (if (subst-val? v)
      (-> v meta attr))))

(defn sync-eset [s v seenset f]
  (if (not= seenset ::no-prop)
    (reduce
     (fn [s y]
       (let [y (root-var s y)]
         (if-not (contains? seenset y)
           (f s y)
           s)))
     s
     (:eset v))
    s))

(defn add-dom
  ([s x dom domv]
   (let [x (root-var s x)]
     (add-dom s x dom domv nil)))
  ([s x dom domv seenset]
   (let [v (root-val s x)
         s (if (subst-val? v)
             (update-var s x (assoc-dom v dom domv))
             (let [v (if (lvar? v) ::unbound v)]
               (ext-no-check s x (subst-val v {dom domv}))))]
     (sync-eset s v seenset
                (fn [s y] (add-dom s y dom domv (conj (or seenset #{}) x)))))))

(defn update-dom
  ([s x dom f]
   (let [x (root-var s x)]
     (update-dom s x dom f nil)))
  ([s x dom f seenset]
   (let [v (root-val s x)
         v (if (lvar? v)
             (subst-val ::unbound)
             v)
         doms (:doms v)
         s (update-var s x (assoc-dom v dom (f (get doms dom))))]
     (sync-eset s v seenset
                (fn [s y] (update-dom s y dom f (conj (or seenset #{}) x)))))))

(defn rem-dom
  ([s x dom]
   (let [x (root-var s x)]
     (rem-dom s x dom nil)))
  ([s x dom seenset]
   (let [v (root-val s x)
         s (if (subst-val? v)
             (let [new-doms (dissoc (:doms v) dom)]
               (if (and (zero? (count new-doms)) (not= (:v v) ::unbound))
                 (update-var s x (:v v))
                 (update-var s x (assoc v :doms new-doms))))
             s)]
     (sync-eset s v seenset
                (fn [s y] (rem-dom s y dom (conj (or seenset #{}) x)))))))

;; NOTE: I don't think we need to bother returning ::not-dom or some other
;; not found value. Assume the case where the var is bound to nil in
;; the substitution where the var has a domain. That the var is member
;; will be verified by domc or something similar. The case where the var
;; is nil and has no domain is trivial.

(defn get-dom [s x dom]
  (let [v (root-val s x)]
    (cond
      (subst-val? v) (let [v' (:v v)]
                       (if (not= v' ::unbound)
                         v'
                         (-> v :doms dom)))
      (not (lvar? v)) v)))

(defn- make-s
  ([] (make-s {}))
  ([m] (make-s m (make-cs)))
  ([m cs] (Substitutions. m nil nil cs nil #{} true nil)))

(defn tabled-s
  ([] (tabled-s false))
  ([oc] (tabled-s oc nil))
  ([oc meta]
   (-> (with-meta (make-s) meta)
       (assoc :oc oc)
       (assoc :ts (atom {})))))

(def empty-s (make-s))
(def empty-f (fn []))

(defn subst? [x]
  (instance? Substitutions x))

(defn to-s [v]
  (let [s (reduce (fn [m [k v]] (assoc m k v)) {} v)]
    (make-s s (make-cs))))

(defn annotate [k v]
  (fn [a]
    (vary-meta a assoc k v)))

;; NOTE: this may result in some redundant computations
;; in particular complex nominal logic programs that involve
;; FD and other similar constraint domains.
;; In nominal programs like quine generation we actually see
;; exponential behavior, so we'll probably want to revisit
;; this code at some point - David

(defn merge-doms [s x doms]
  (let [xdoms (:doms (root-val s x))]
    (loop [doms (seq doms) s s]
      (if doms
        (let [[dom domv] (first doms)]
          (let [xdomv (get xdoms dom ::not-found)
                ndomv (if (identical? xdomv ::not-found)
                        domv
                        (-merge-doms domv xdomv))]
            (when ndomv
              (recur (next doms)
                     (add-dom s x dom ndomv #{})))))
        s))))

(defn update-eset [s doms eset]
  (loop [eset (seq eset) s s]
    (if eset
      (when-let [s (merge-doms s (root-var s (first eset)) doms)]
        (recur (next eset) s))
      s)))

(defn merge-with-root [s x root]
  (let [xv    (root-val s x)
        rootv (root-val s root)
        eset  (set/union (:eset rootv) (:eset xv))
        doms (loop [xd (seq (:doms xv)) rd (:doms rootv) r {}]
               (if xd
                 (let [[xk xv] (first xd)]
                   (if-let [[_ rv] (find rd xk)]
                     (let [nd (-merge-doms xv rv)]
                       (when nd
                         (recur (next xd)
                                (dissoc rd xk) (assoc r xk nd))))
                     (recur (next xd) rd (assoc r xk xv))))
                 (merge r rd)))
        nv (when doms
             (subst-val (:v rootv) doms eset
                        (merge (meta xv) (meta rootv))))]
    (when nv
      (-> s
          (ext-no-check root nv)
          (update-eset doms eset)))))

;; =============================================================================
;; Entanglement

(defn to-subst-val [v]
  (if (subst-val? v)
    v
    (subst-val ::unbound)))

(defn entangle [s x y]
  (let [x  (root-var s x)
        y  (root-var s y)
        xv (to-subst-val (root-val s x))
        yv (to-subst-val (root-val s y))]
    (-> s
        (update-var x (assoc xv :eset (conj (or (:eset xv) #{}) y)))
        (update-var y (assoc yv :eset (conj (or (:eset yv) #{}) x))))))

;; =============================================================================
;; Logic Variables

(declare lmap? lmap-entries lmap-rest lvec? lvec-join lvec-parts)

(deftype LVar [id unique name oname hash meta]
  IVar
  clojure.lang.ILookup
  (valAt [this k]
    (.valAt this k nil))
  (valAt [this k not-found]
    (case k
      :name name
      :oname oname
      :id id
      not-found))

  clojure.lang.IObj
  (meta [this]
    meta)
  (withMeta [this new-meta]
    (LVar. id unique name oname hash new-meta))

  Object
  (toString [_] (str "<lvar:" name ">"))

  (equals [this o]
    (if (instance? IVar o)
      (if unique
        (identical? id (:id o))
        (identical? name (:name o)))
      false))

  (hashCode [_] hash)

  IUnifyTerms
  (unify-terms [u v s]
    (cond
      (lvar? v)
      (let [repoint (cond
                      (-> u clojure.core/meta ::unbound) [u v]
                      (-> v clojure.core/meta ::unbound) [v u]
                      :else nil)]
        (if repoint
          (let [[root other] repoint]
            (when-let [s (if (-> other clojure.core/meta ::unbound)
                           (merge-with-root s other root)
                           s)]
              (let [s  (ext-no-check s other root)
                    cs (migrate (:cs s) other root s)]
                (when cs
                  (assoc s :cs cs)))))
          (ext-no-check s u v)))

      (non-storable? v)
      (throw (Exception. (str v " is non-storable")))

      (not= v ::not-found)
      (if (tree-term? v)
        (ext s u v)
        (if (-> u clojure.core/meta ::unbound)
          (ext-no-check s u (assoc (root-val s u) :v v))
          (ext-no-check s u v)))

      :else nil))

  IReifyTerm
  (reify-term [v s]
    (let [rf (-> s clojure.core/meta :reify-vars)]
      (if (fn? rf)
        (rf v s)
        (if rf
          (ext s v (reify-lvar-name s))
          (ext s v (:oname v))))))

  IWalkTerm
  (walk-term [v f] (f v))

  IOccursCheckTerm
  (occurs-check-term [v x s] (= (walk s v) x))

  IBuildTerm
  (build-term [u s]
    (let [m (:s s)
          cs (:cs s)
          lv (lvar 'ignore)]
      (if (contains? m u)
        s
        (make-s (assoc m u lv) cs)))))

(defn lvar
  ([]
   (let [id (. clojure.lang.RT (nextID))
         name (str id)]
     (LVar. id true name nil (.hashCode name) nil)))
  ([name]
   (lvar name true))
  ([name unique]
   (let [oname name
         id   (if unique
                (. clojure.lang.RT (nextID))
                name)
         name (if unique
                (str name "__" id)
                (str name))]
     (LVar. id unique name oname (.hashCode name) nil))))

(defmethod print-method LVar [x ^Writer writer]
  (.write writer (str "<lvar:" (:name x) ">")))

(defn lvar? [x]
  (instance? IVar x))

(defn lvars [n]
  (repeatedly n lvar))

(defn bindable? [x]
  (or (lvar? x)
      (instance? IBindable x)))

;; =============================================================================
;; LCons

(declare lcons?)

(defmacro umi
  [& args]
  (if (resolve 'unchecked-multiply-int)
    `(unchecked-multiply-int ~@args)
    `(unchecked-multiply ~@args)))

(defmacro uai
  [& args]
  (if (resolve 'unchecked-add-int)
    `(unchecked-add-int ~@args)
    `(unchecked-add ~@args)))

;; TODO: clean up the printing code

(deftype LCons [a d ^{:unsynchronized-mutable true :tag int} cache meta]
  ITreeTerm
  clojure.lang.IObj
  (meta [this]
    meta)
  (withMeta [this new-meta]
    (LCons. a d cache new-meta))

  LConsSeq
  (lfirst [_] a)
  (lnext [_] d)

  LConsPrint
  (toShortString [this]
    (cond
      (.. this getClass (isInstance d)) (str a " " (toShortString d))
      :else (str a " . " d)))

  Object
  (toString [this] (cond
                     (.. this getClass (isInstance d))
                     (str "(" a " " (toShortString d) ")")
                     :else (str "(" a " . " d ")")))

  (equals [this o]
    (or (identical? this o)
        (and (.. this getClass (isInstance o))
             (loop [me this
                    you o]
               (cond
                 (nil? me) (nil? you)
                 (lvar? me) true
                 (lvar? you) true
                 (and (lcons? me) (lcons? you))
                 (let [mef  (lfirst me)
                       youf (lfirst you)]
                   (and (or (= mef youf)
                            (lvar? mef)
                            (lvar? youf))
                        (recur (lnext me) (lnext you))))
                 :else (= me you))))))

  (hashCode [this]
    (if (clojure.core/== cache -1)
      (do
        (set! cache (uai (umi (int 31) (clojure.lang.Util/hash d))
                         (clojure.lang.Util/hash a)))
        cache)
      cache))

  IUnifyTerms
  (unify-terms [u v s]
    (cond
      (lvec? v) (unify-terms v u s)

      (sequential? v)
      (loop [u u v (seq v) s s]
        (if-not (nil? v)
          (if (lcons? u)
            (if-let [s (unify s (lfirst u) (first v))]
              (recur (lnext u) (next v) s)
              nil)
            (unify s u v))
          (if (lvar? u)
            (if-let [s (unify s u '())]
              s
              (unify s u nil))
            nil)))

      (lcons? v)
      (loop [u u v v s s]
        (if (lvar? u)
          (unify s u v)
          (cond
            (lvar? v) (unify s v u)
            (and (lcons? u) (lcons? v))
            (if-let [s (unify s (lfirst u) (lfirst v))]
              (recur (lnext u) (lnext v) s)
              nil)
            :else (unify s u v))))

      :else nil))

  IReifyTerm
  (reify-term [v s]
    (loop [v v s s]
      (if (lcons? v)
        (recur (lnext v) (-reify* s (lfirst v)))
        (-reify* s v))))

  ;; TODO: no way to make this non-stack consuming w/o a lot more thinking
  ;; we could use continuation passing style and trampoline
  IWalkTerm
  (walk-term [v f]
    (lcons (f (lfirst v))
           (f (lnext v))))

  IOccursCheckTerm
  (occurs-check-term [v x s]
    (loop [v v x x s s]
      (if (lcons? v)
        (or (occurs-check s x (lfirst v))
            (recur (lnext v) x s))
        (occurs-check s x v))))

  IBuildTerm
  (build-term [u s]
    (loop [u u s s]
      (if (lcons? u)
        (recur (lnext u) (build s (lfirst u)))
        (build s u)))))

(defmethod print-method LCons [x ^Writer writer]
  (.write writer (str x)))

(defn lcons
  "Constructs a sequence a with an improper tail d if d is a logic variable."
  [a d]
  (cond
    (or (coll? d) (nil? d)) (cons a (seq d))
    (lvec? d) (lvec-join [a] d [])
    :else (LCons. a d -1 nil)))

(defn lcons? [x]
  (instance? LCons x))

(defmacro llist
  "Constructs a sequence from 2 or more arguments, with the last argument as the
   tail. The tail is improper if the last argument is a logic variable."
  ([f s] `(lcons ~f ~s))
  ([f s & rest] `(lcons ~f (llist ~s ~@rest))))

;; =============================================================================
;; Unification

;; TODO : a lot of cascading ifs need to be converted to cond

(defn unify-with-sequential* [u v s]
  (cond
    (sequential? v)
    (if (and (counted? u) (counted? v)
             (not (clojure.core/== (count u) (count v))))
      nil
      (loop [u (seq u) v (seq v) s s]
        (if-not (nil? u)
          (if-not (nil? v)
            (if-let [s (unify s (first u) (first v))]
              (recur (next u) (next v) s)
              nil)
            nil)
          (if-not (nil? v) nil s))))

    (or (lcons? v) (lvec? v)) (unify-terms v u s)
    :else nil))

(defn atomic-key?
  "True if the map key k is a plain value, i.e. not a logic var or a term
   that may contain one. Such a key is ground and compares by value."
  [k]
  (not (or (instance? IVar k)
           (instance? clojure.lang.IPersistentCollection k)
           (instance? ITreeTerm k))))

(declare unify-map-terms)

(defn unify-with-map* [u v s]
  (when (clojure.core/== (count u) (count v))
    (loop [ks (keys u) s s]
      (if (seq ks)
        (let [kf (first ks)]
          (if (atomic-key? kf)
            (let [vf (get v kf ::not-found)]
              (if (identical? vf ::not-found)
                ;; v may still have kf under a key that is not a plain value
                (when-not (every? atomic-key? (keys v))
                  (unify-map-terms u v s))
                (if-let [s (unify s (get u kf) vf)]
                  (recur (next ks) s)
                  nil)))
            (unify-map-terms u v s)))
        s))))

(extend-protocol IUnifyTerms
  nil
  (unify-terms [u v s]
    (if (nil? v) s nil))

  Object
  (unify-terms [u v s]
    (if (= u v)
      s
      nil))

  clojure.lang.Sequential
  (unify-terms [u v s]
    (unify-with-sequential* u v s))

  clojure.lang.IPersistentMap
  (unify-terms [u v s]
    (cond
      (lmap? v)
      (unify-terms v u s)  ;; delegate to LMap

      (instance? clojure.core.logic.protocols.IUnifyWithRecord v)
      (unify-with-record v u s)

      (map? v)
      (unify-with-map* u v s)

      :else nil)))

;; =============================================================================
;; Reification

(extend-protocol IReifyTerm
  nil
  (reify-term [v s] s)

  Object
  (reify-term [v s] s)

  clojure.lang.IPersistentCollection
  (reify-term [v s]
    (loop [v v s s]
      (if (seq v)
        (recur (next v) (-reify* s (first v)))
        s))))

;; =============================================================================
;; Walk Term

;; Walking a map whose keys have become equal records it: such a term
;; denotes no map, so reifyg drops the answer. Each collision gets a number
;; from the global count, and the thread keeps its latest one, so reifyg
;; only looks at the thread when the count moved.
(def ^:private ^java.util.concurrent.atomic.AtomicLong map-key-collision-count
  (java.util.concurrent.atomic.AtomicLong.))

(def ^:private ^ThreadLocal map-key-collision (ThreadLocal.))

(defn- map-keys-collided! []
  (.set map-key-collision (.incrementAndGet map-key-collision-count)))

(defn- map-keys-collided-since?
  "True if walking on this thread met colliding map keys since the
   collision count was n."
  [n]
  (and (not (clojure.core/== n (.get map-key-collision-count)))
       (let [last (.get map-key-collision)]
         (boolean (and last (> (long last) (long n)))))))

(defn walk-record-term [v f]
  (with-meta
    (loop [v v r (-uninitialized v)]
      (if (seq v)
        (let [[vfk vfv] (first v)]
          (recur (next v) (assoc r (walk-term (f vfk) f)
                                 (walk-term (f vfv) f))))
        r))
    (meta v)))

(extend-protocol IWalkTerm
  nil
  (walk-term [v f] (f nil))

  Object
  (walk-term [v f] (f v))

  clojure.lang.ISeq
  (walk-term [v f]
    (with-meta
      (doall (map #(walk-term (f %) f) v))
      (meta v)))

  clojure.lang.IPersistentVector
  (walk-term [v f]
    (with-meta
      (loop [v v r (transient [])]
        (if (seq v)
          (recur (next v) (conj! r (walk-term (f (first v)) f)))
          (persistent! r)))
      (meta v)))

  clojure.lang.IPersistentMap
  (walk-term [v f]
    (if (record? v)
      (walk-record-term v f)
      (let [r (loop [es v r (transient {})]
                (if (seq es)
                  (let [[vfk vfv] (first es)]
                    (recur (next es) (assoc! r (walk-term (f vfk) f)
                                             (walk-term (f vfv) f))))
                  (persistent! r)))]
        (when-not (clojure.core/== (count r) (count v))
          (map-keys-collided!))
        (with-meta r (meta v)))))

  clojure.lang.IRecord
  (walk-term [v f]
    (walk-record-term v f)))

;; =============================================================================
;; Occurs Check Term

(extend-protocol IOccursCheckTerm
  nil
  (occurs-check-term [v x s] false)

  Object
  (occurs-check-term [v x s] false)

  clojure.lang.IPersistentCollection
  (occurs-check-term [v x s]
    (loop [v v x x s s]
      (if (seq v)
        (or (occurs-check s x (first v))
            (recur (next v) x s))
        false)))

  clojure.lang.IPersistentMap
  (occurs-check-term [v x s]
    (loop [es (seq v) noted? false]
      (if es
        (let [[k val] (first es)
              note? (and (not noted?) (not (atomic-key? k)))]
          (when note?
            ;; ext checks the keys of this map once it is bound
            (note-keyed-map v))
          (or (occurs-check s x k)
              (occurs-check s x val)
              (recur (next es) (or noted? note?))))
        false))))

;; =============================================================================
;; Build Term

(extend-protocol IBuildTerm
  nil
  (build-term [u s] s)

  Object
  (build-term [u s] s)

  clojure.lang.IPersistentCollection
  (build-term [u s]
    (reduce build s u)))

;; =============================================================================
;; Goals and Goal Constructors

(defn composeg
  ([] identity)
  ([g0 g1]
   (fn [a]
     (let [a (g0 a)]
       (and a (g1 a))))))

(defmacro composeg*
  ([g0] g0)
  ([g0 & gs]
   `(composeg
     ~g0
     (composeg* ~@gs))))

(defmacro bind*
  ([a g] `(bind ~a ~g))
  ([a g & g-rest]
   `(bind* (bind ~a ~g) ~@g-rest)))

(defmacro mplus*
  ([e] e)
  ([e & e-rest]
   `(mplus ~e (fn [] (mplus* ~@e-rest)))))

(defmacro -inc [& rest]
  `(fn ~'-inc [] ~@rest))

(extend-type Object
  ITake
  (take* [this] this))

(deftype Choice [a f]
  clojure.lang.ILookup
  (valAt [this k]
    (.valAt this k nil))
  (valAt [this k not-found]
    (case k
      :a a
      not-found))
  IBind
  (bind [this g]
    (mplus (g a) (fn [] (bind f g))))
  IMPlus
  (mplus [this fp]
    (Choice. a (fn [] (mplus (fp) f))))
  ITake
  (take* [this]
    (lazy-seq (cons a (lazy-seq (take* f))))))

(defn choice [a f]
  (Choice. a f))

;; -----------------------------------------------------------------------------
;; MZero

(extend-type nil
  IBind
  (bind [_ g] nil)
  IMPlus
  (mplus [_ f] (f))
  ITake
  (take* [_] '()))

;; -----------------------------------------------------------------------------
;; Unit

(extend-type Object
  IMPlus
  (mplus [this f]
    (Choice. this f)))

;; -----------------------------------------------------------------------------
;; Inc

(extend-type clojure.lang.Fn
  IBind
  (bind [this g]
    (-inc (bind (this) g)))
  IMPlus
  (mplus [this f]
    (-inc (mplus (f) this)))
  ITake
  (take* [this] (lazy-seq (take* (this)))))

;; =============================================================================
;; Syntax

(defn succeed
  "A goal that always succeeds."
  [a] a)

(defn fail
  "A goal that always fails."
  [a] nil)

(def s# succeed)

(def u# fail)

(defn ext-run-csg [u v]
  (fn [a]
    (ext-run-cs a u v)))

(defn ==
  "A goal that attempts to unify terms u and v."
  [u v]
  (fn [a]
    (let [has-cs? (pos? (count (:cs a)))]
      (let [ap (unify (if has-cs? (assoc a :vs []) a) u v)
            vs (if has-cs? (:vs ap))
            changed? (pos? (count vs))]
        (if changed?
          ((run-constraints* vs (:cs ap) ::subst) (assoc ap :vs nil))
          ap)))))

(defn- bind-conde-clause [a]
  (fn [g-rest]
    `(bind* ~a ~@g-rest)))

(defn- bind-conde-clauses [a clauses]
  (map (bind-conde-clause a) clauses))

(defmacro conde
  "Logical disjunction of the clauses. The first goal in
  a clause is considered the head of that clause. Interleaves the
  execution of the clauses."
  [& clauses]
  (let [a (gensym "a")]
    `(fn [~a]
       (-inc
        (mplus* ~@(bind-conde-clauses a clauses))))))

(defn or*
  "A function version of conde, which takes a list of goals and tries them as if via conde.
   Note that or* only does disjunction, ie (or* [a b c]) is the same as (conde [a] [b] [c]).
   If you need something like (conde [a b] [c]), you can use and*, or all:
   (or* [(and* a b) c])."
  [goals]
  (letfn [(mplus'
            ([e] e)
            ([e & es]
             (mplus e (fn [] (apply mplus' es)))))]
    (fn [a]
      (fn []
        (apply mplus' (for [goal goals]
                        (bind a goal)))))))

(defn- lvar-bind [sym]
  ((juxt identity
         (fn [s] `(lvar '~s))) sym))

(defn- lvar-binds [syms]
  (mapcat lvar-bind syms))

(defmacro fresh
  "Creates fresh variables. Goals occuring within form a logical
  conjunction."
  [[& lvars] & goals]
  `(fn [a#]
     (-inc
      (let [~@(lvar-binds lvars)]
        (bind* a# ~@goals)))))

(declare reifyg)

(defmacro -run [opts [x :as bindings] & goals]
  (if (> (count bindings) 1)
    (let [[rbindings as-key [as]] (partition-by #{:as} bindings)]
      (if (seq as-key)
        `(-run ~opts [~as] (fresh [~@rbindings] (== ~as [~@rbindings]) ~@goals))
        `(-run ~opts [q#] (fresh ~bindings (== q# ~bindings) ~@goals))))
    `(let [opts# ~opts
           xs# (take* (fn []
                        ((fresh [~x]
                                ~@goals
                                (reifyg ~x))
                         (tabled-s (:occurs-check opts#)
                                   (merge {:reify-vars true} opts#)))))]
       (if-let [n# (:n opts#)]
         (take n# xs#)
         xs#))))

(def ^:dynamic *logic-dbs* [])

(defmacro run
  "Executes goals until a maximum of n results are found."
  [n bindings & goals]
  `(-run {:occurs-check true :n ~n :db *logic-dbs*} ~bindings ~@goals))

(defmacro run*
  "Executes goals until results are exhausted."
  [bindings & goals]
  `(-run {:occurs-check true :n false :db *logic-dbs*} ~bindings ~@goals))

(defmacro run-db
  "Executes goals until a maximum of n results are found. Uses a specified logic database."
  [n db bindings & goals]
  `(-run {:occurs-check true :n ~n :db (flatten [~db])} ~bindings ~@goals))

(defmacro run-db*
  "Executes goals until results are exhausted. Uses a specified logic database."
  [db bindings & goals]
  `(-run {:occurs-check true :n false :db (flatten [~db])} ~bindings ~@goals))

(defmacro run-nc
  "Executes goals until a maximum of n results are found. Does not
   occurs-check."
  [n bindings & goals]
  `(-run {:occurs-check false :n ~n :db *logic-dbs*} ~bindings ~@goals))

(defmacro run-nc*
  "Executes goals until results are exhausted. Does not occurs-check."
  [& goals]
  `(run-nc false ~@goals))

(defmacro all
  "Like fresh but does does not create logic variables."
  ([] `clojure.core.logic/s#)
  ([& goals] `(fn [a#] (bind* a# ~@goals))))

(defn and*
  "A function version of all, which takes a list of goals and succeeds only if they all succeed."
  [goals]
  (fn [a]
    (reduce bind a goals)))

(defn solutions
  ([s g]
   (solutions s (lvar) g))
  ([s q g]
   (take* ((all g (reifyg q)) s))))

;; =============================================================================
;; Debugging

(defmacro log
  "Goal for println"
  [& s]
  `(fn [a#]
     (println ~@s)
     a#))

(defmacro trace-s
  "Goal that prints the current substitution"
  []
  `(fn [a#]
     (println (str a#))
     a#))

(defn trace-lvar [a lvar]
  `(println (format "%5s = %s" (str '~lvar) (-reify ~a ~lvar))))

(defmacro trace-lvars
  "Goal for tracing the values of logic variables."
  [title & lvars]
  (let [a (gensym "a")]
    `(fn [~a]
       (println ~title)
       ~@(map (partial trace-lvar a) lvars)
       ~a)))

;; =============================================================================
;; Non-relational goals

;; =============================================================================
;; project

(defn- project-binding [s]
  (fn [var]
    `(~var (walk* ~s ~var))))

(defn- project-bindings [vars s]
  (reduce concat (map (project-binding s) vars)))

(defmacro project
  "Extract the values bound to the specified logic vars. Non-relational."
  [[& vars] & goals]
  (let [a (gensym "a")]
    `(fn [~a]
       (let [~@(project-bindings vars a)]
         ((fresh []
                 ~@goals) ~a)))))

(defmacro pred
  "Check a predicate against the value logic var. Non-relational."
  [v f]
  `(project [~v]
            (== (~f ~v) true)))

;; TODO: remove v argument - David

(defmacro is
  "Set the value of a var to value of another var with the operation
   applied. Non-relational."
  [u v op]
  `(project [~v]
            (== ~u (~op ~v))))

;; =============================================================================
;; conda (soft-cut), condu (committed-choice)
;;
;; conda once a line succeeds no others are tried
;; condu a line can succeed only one time

;; TODO : conda and condu should probably understanding logging

;; TODO : if -> when

(defmacro ifa*
  ([])
  ([[e & gs] & grest]
   `(ifa ~e [~@gs]
         ~(if (seq grest)
            `(delay (ifa* ~@grest))
            nil))))

(defmacro ifu*
  ([])
  ([[e & gs] & grest]
   `(ifu ~e [~@gs]
         ~(if (seq grest)
            `(delay (ifu* ~@grest))
            nil))))

(extend-protocol IIfA
  nil
  (ifa [b gs c]
    (when c
      (force c)))

  Substitutions
  (ifa [b gs c]
    (reduce bind b gs))

  clojure.lang.Fn
  (ifa [b gs c]
    (-inc (ifa (b) gs c)))

  Choice
  (ifa [b gs c]
    (reduce bind b gs)))

(extend-protocol IIfU
  nil
  (ifu [b gs c]
    (when c
      (force c)))

  Substitutions
  (ifu [b gs c]
    (reduce bind b gs))

  clojure.lang.Fn
  (ifu [b gs c]
    (-inc (ifu (b) gs c)))

  Choice
  (ifu [b gs c]
    (reduce bind (:a b) gs)))

(defn- cond-clauses [a]
  (fn [goals]
    `((~(first goals) ~a) ~@(rest goals))))

(defmacro conda
  "Soft cut. Once the head of a clause has succeeded
  all other clauses will be ignored. Non-relational."
  [& clauses]
  (let [a (gensym "a")]
    `(fn [~a]
       (ifa* ~@(map (cond-clauses a) clauses)))))

(defmacro condu
  "Committed choice. Once the head (first goal) of a clause
  has succeeded, remaining goals of the clause will only
  be run once. Non-relational."
  [& clauses]
  (let [a (gensym "a")]
    `(fn [~a]
       (ifu* ~@(map (cond-clauses a) clauses)))))

(defn onceo [g] (condu (g)))

;; =============================================================================
;; copy-term

(declare constrain-lmap-rests)

(defn copy-term
  "Copies a term u into v. Non-relational."
  [u v]
  (project [u]
           (let [c (walk* (build empty-s u) u)]
             (all
              (== c v)
              ;; copied open maps have fresh rests, without their constraints
              (fn [s] (constrain-lmap-rests s c))))))

;; =============================================================================
;; lvar nonlvar

(defmacro lvaro
  "A goal that succeeds if the argument is fresh. v must be a logic
  variable. Non-relational."
  [v]
  `(fn [a#]
     (if (lvar? (walk a# ~v))
       a# nil)))

(defmacro nonlvaro
  "A goal that succeeds if the argument is not fresh. v must be a
  logic variable. Non-relational."
  [v]
  `(fn [a#]
     (if (not (lvar? (walk a# ~v)))
       a# nil)))

;; =============================================================================
;; Pattern matching

(defn- warn [& msg]
  (binding [*out* *err*]
    (apply println "WARNING:" msg)))

(declare p->term)

(defn- lcons-p? [p]
  (and (coll? p)
       (not (nil? (some '#{.} p)))))

(defn- p->llist
  "Take an lcons pattern and convert it into a llist constructor
   expression."
  ([p vars] (p->llist p vars false))
  ([p vars quoted]
   `(llist
     ~@(doall
        (map #(p->term % vars quoted)
             (remove #(contains? '#{.} %) p))))))

(defn- lvar-sym? [s]
  (and (symbol? s)
       (not= s '.)
       (not (contains? *locals* s))))

(defn update-pvars! [x vars]
  (if (lvar-sym? x)
    (do
      (swap! vars conj x)
      x)
    x))

(defn- p->term
  "Convert a pattern p into a term suitable for unification. Takes an atom
   containing a set for returning any encountered vars which will be declared
   fresh."
  ([p vars] (p->term p vars false))
  ([p vars quoted]
   (cond
     (= p '_) `(lvar)
     (lcons-p? p) (p->llist p vars quoted)
     (coll? p)
     (cond
         ;; support simple expressions
       (seq? p)
       (let [[f s] p]
         (cond
           (= f 'quote)
           (if (and (seq? s) (not quoted))
             (p->term s vars true)
             p)
           (= f 'clojure.core/unquote)
           (if quoted
             (update-pvars! s vars)
             (throw (Exception. "Invalid use of clojure.core/unquote in pattern.")))
           :else
           (let [ps (map #(p->term % vars quoted) p)]
             (if quoted
               `(list ~@ps)
               ps))))
         ;; preserve original collection type
       :else
       (let [ps (map #(p->term % vars quoted) p)]
         (cond
           (instance? clojure.lang.MapEntry p) (into [] ps)
           :else (into (empty p) ps))))
     (symbol? p) (if quoted
                   (list 'quote p)
                   (update-pvars! p vars))
     :else p)))

(defn- fresh-expr? [cs]
  (= (first cs) `fresh))

(defn- ex
  "Takes a list of vars to declare fresh and a term t to be unified
   with relation argument a."
  ([vs t a]
   `(fresh [~@vs]
           (== ~t ~a)))
  ([vs t a exprs]
   (if (fresh-expr? exprs)
     `(fresh [~@vs]
             (== ~t ~a)
             ~exprs)
     `(fresh [~@vs]
             (== ~t ~a)
             ~@exprs))))

(defn- ex*
  "Takes a sequence of pattern/argument pairs, goal expressions and
   a set of seen variables. Returns source code that represents the
   equivalent miniKanren series of unifications."
  [[[p a :as pa] & par] exprs seen]
  (let [vars (atom #{})
        t    (p->term p vars)
        vs   (set/difference @vars seen)
        seen (reduce conj seen vs)]
    (cond
      (nil? pa) exprs
      (= p '_) (ex* par exprs seen)
      (empty? par) (if exprs
                     (ex vs t a exprs)
                     (ex vs t a))
      :else (let [r (ex* par exprs seen)]
              (if r
                (ex vs t a r)
                (ex vs t a))))))

(defn- all-blank? [p]
  (every? #(= % '_) p))

(defn- handle-clause [as]
  (when-not (vector? as)
    (throw (Exception. (str "Expecting vector of arguments, instead " as))))
  (fn [[p & exprs]]
    (when-not (vector? p)
      (throw (Exception. (str "Expecting vector of matches, instead " p))))
    (when-not (= (count p) (count as))
      (warn "Differing number of matches. Matching" p "against" as))
    (let [pas (partition 2 (interleave p as))
          r (ex* pas exprs #{})]
      (if (all-blank? p)
        r
        (list r)))))

(defn- handle-clauses [t as cs]
  `(~t
    ~@(doall (map (handle-clause as) cs))))

;; name-with-attributes by Konrad Hinsen, from clojure.contrib.def
(defn- name-with-attributes
  "To be used in macro definitions.
   Handles optional docstrings and attribute maps for a name to be defined
   in a list of macro arguments. If the first macro argument is a string
   it is added as a docstring to name and removed from the macro argument
   list. If afterwards the first macro argument is a map, its entries are
   added to the name's metadata map and the map is removed from the
   macro argument list. The return value is a vector containing the name
   with its extended metadata map and the list of unprocessed macro
   arguments."
  [name macro-args]
  (let [[docstring macro-args] (if (string? (first macro-args))
                                 [(first macro-args) (next macro-args)]
                                 [nil macro-args])
        [attr macro-args]          (if (map? (first macro-args))
                                     [(first macro-args) (next macro-args)]
                                     [{} macro-args])
        attr                       (if docstring
                                     (assoc attr :doc docstring)
                                     attr)
        attr                       (if (meta name)
                                     (conj (meta name) attr)
                                     attr)]
    [(with-meta name attr) macro-args]))

(declare tabled)

(defn env-locals [& syms]
  (disj (set (apply concat syms)) '_))

(defmacro -fnm [fn-gen t as & cs]
  (binding [*locals* (env-locals as (keys &env))]
    `(~fn-gen [~@as] ~(handle-clauses t as cs))))

(defmacro fnm
  {:arglists '([t as tabled? & cs])}
  [t as & cs]
  (if-let [cs (and (= (first cs) :tabled) (rest cs))]
    `(-fnm tabled ~t ~as ~@cs)
    `(-fnm fn ~t ~as ~@cs)))

(defmacro defnm [t n & rest]
  (let [[n [as & cs]] (name-with-attributes n rest)
        e (if (-> n meta :tabled)
            `(fnm ~t ~as :tabled ~@cs)
            `(fnm ~t ~as ~@cs))]
    `(def ~(vary-meta n #(merge {:arglists (list 'quote (list as))} %1)) ~e)))

;; =============================================================================
;; Useful goals

(defn nilo
  "A relation where a is nil"
  [a]
  (== nil a))

(defn emptyo
  "A relation where a is the empty list"
  [a]
  (== '() a))

(defn conso
  "A relation where l is a collection, such that a is the first of l
  and d is the rest of l. If ground d must be bound to a proper tail."
  [a d l]
  (== (lcons a d) l))

(defn firsto
  "A relation where l is a collection, such that a is the first of l"
  [l a]
  (fresh [d]
         (conso a d l)))

(defn resto
  "A relation where l is a collection, such that d is the rest of l"
  [l d]
  (fresh [a]
         (== (lcons a d) l)))

(defn everyg
  "A pseudo-relation that takes a coll and ensures that the goal g
   succeeds on every element of the collection."
  [g coll]
  (fn [a]
    (let [coll (walk a coll)]
      (((fn everyg* [g coll]
          (if (seq coll)
            (all
             (g (first coll))
             (everyg* g (next coll)))
            s#)) g coll) a))))

;; =============================================================================
;; Goal sugar syntax

(defmacro fne
  "Define an anonymous goal fn. Supports pattern matching. All
   patterns will be tried. See conde."
  [& rest]
  `(fnm conde ~@rest))

(defmacro defne
  "Define a goal fn. Supports pattern matching. All
   patterns will be tried. See conde."
  [& rest]
  `(defnm conde ~@rest))

(defmacro matche
  "Pattern matching macro. All patterns will be tried.
  See conde."
  [xs & cs]
  (binding [*locals* (env-locals xs (keys &env))]
    (handle-clauses `conde xs cs)))

;; -----------------------------------------------------------------------------
;; fnu, fna, defnu, defna, matcha, matchu

;; TODO: we need to rethink (de)fna and (de)fnu, the unification comes first
;; the *question* should come first

(defmacro fna
  "Define an anonymous soft cut goal. See conda."
  [& rest]
  `(fnm conda ~@rest))

(defmacro fnu
  "Define an anonymous committed choice goal. See condu."
  [& rest]
  `(fnm condu ~@rest))

(defmacro defna
  "Define a soft cut goal. See conda."
  [& rest]
  `(defnm conda ~@rest))

(defmacro defnu
  "Define a committed choice goal. See condu."
  [& rest]
  `(defnm condu ~@rest))

(defmacro matcha
  "Define a soft cut pattern match. See conda."
  [xs & cs]
  (binding [*locals* (env-locals xs (keys &env))]
    (handle-clauses `conda xs cs)))

(defmacro matchu
  "Define a committed choice goal. See condu."
  [xs & cs]
  (binding [*locals* (env-locals xs (keys &env))]
    (handle-clauses `condu xs cs)))

;; =============================================================================
;; More convenient goals

(declare !=)

(defne membero
  "A relation where l is a collection, such that l contains x."
  [x l]
  ([_ [x . tail]])
  ([_ [head . tail]]
   (membero x tail)))

(defne member1o
  "Like membero but uses to disequality further constraining
   the results. For example, if x and l are ground and x occurs
   multiple times in l, member1o will succeed only once."
  [x l]
  ([_ [x . tail]])
  ([_ [head . tail]]
   (!= x head)
   (member1o x tail)))

(defne appendo
  "A relation where x, y, and z are proper collections,
  such that z is x appended to y"
  [x y z]
  ([() _ y])
  ([[a . d] _ [a . r]] (appendo d y r)))

(declare rembero)

(defne permuteo
  "A relation that will permute xl into the yl. May not
   terminate if xl is not ground."
  [xl yl]
  ([() ()])
  ([[x . xs] _]
   (fresh [ys]
          (permuteo xs ys)
          (rembero x yl ys))))

;; =============================================================================
;; Rel

(defn to-stream [aseq]
  (let [aseq (drop-while nil? aseq)]
    (when (seq aseq)
      (choice (first aseq)
              (fn [] (to-stream (next aseq)))))))

;; =============================================================================
;; Tabling

;; See - William Byrd "Relational Programming in miniKanren:
;; Techniques, Applications, and Implementations"
;; http://scholarworks.iu.edu/dspace/bitstream/handle/2022/8777/Byrd_indiana_0093A_10344.pdf?sequence=1
;; http://code.google.com/p/iucs-relational-research/

;; -----------------------------------------------------------------------------
;; Data Structures
;; waiting streams are PersistentVectors

;; AnswerCache
;; ansl - ans list, for calculating the fixpoint
;; anss - cached answer set, for quickly checking whether an answer term
;;        is already in the cache

(deftype AnswerCache [ansl anss _meta]
  Object
  (toString [this]
    (str "<answer-cache:" (pr-str ansl) ">"))

  clojure.lang.IObj
  (meta [_] _meta)
  (withMeta [_ new-meta]
    (AnswerCache. ansl anss new-meta))

  clojure.lang.ILookup
  (valAt [this k]
    (.valAt this k nil))
  (valAt [this k not-found]
    (case k
      :ansl ansl
      :anss anss
      not-found))

  IAnswerCache
  (-add [this x]
    (AnswerCache. (conj ansl x) (conj anss x) _meta))
  (-cached? [_ x]
    (let [^clojure.lang.IPersistentSet anss anss]
      (.contains anss x))))

(defn answer-cache [] (AnswerCache. () #{} nil))

(defmethod print-method AnswerCache [x ^Writer writer]
  (.write writer (str x)))

(defrecord SuspendedStream [cache ansv* f]
  ISuspendedStream
  (ready? [this]
    (not (identical? (:ansl @cache) ansv*))))

(defn make-suspended-stream [cache ansv* f]
  (SuspendedStream. cache ansv* f))

(defn suspended-stream? [x]
  (instance? SuspendedStream x))

(defn waiting-stream? [x]
  (vector? x))

(defn waiting-stream-check
  "Take a waiting stream, a success continuation, and a failure continuation.
   If we don't find any ready suspended streams, invoke the failure continuation.
   If we find a ready suspended stream calculate the remainder of the waiting
   stream. If we've reached the fixpoint just call the thunk of the suspended
   stream, otherwise call mplus on the result of the thunk and the remainder
   of the waiting stream. Pass this result to the success contination."
  [w success-cont failure-cont]
  (loop [w w a []]
    (cond
      (nil? w) (failure-cont)

      (ready? (first w))
      (success-cont
       (fn []
         (let [ss (first w)
               f  (:f ss)
               w  (into a (next w))]
           (if (empty? w)
             (f)
             (mplus (f) (fn [] w))))))

      :else (recur (next w) (conj a (first w))))))

;; -----------------------------------------------------------------------------
;; Extend Substitutions to support tabling

;; CONSIDER: subunify, reify-term-tabled, extending all the necessary types to
;; them

(extend-type Substitutions
  ITabled

  ;; returns a substitution that maps fresh vars to
  ;; new ones. similar to Prolog's copy_term/2. this is to avoid
  ;; prematurely grounding vars.
  (-reify-tabled [this v]
    (let [v (walk this v)]
      (cond
        (lvar? v) (ext-no-check this v (lvar (count (:s this))))
        (lmap? v) (-reify-tabled
                   (-reify-tabled this (seq (lmap-entries v)))
                   (lmap-rest v))
        (lvec? v) (-reify-tabled this (lvec-parts v))
        (coll? v) (-reify-tabled
                   (-reify-tabled this (first v))
                   (next v))
        :else this)))

  ;; returns the term v with all fresh vars replaced with copies.
  ;; this is to avoid prematurely grounding vars.
  (reify-tabled [this v]
    (let [v (walk* this v)]
      (walk* (-reify-tabled empty-s v) v)))

  ;; argv are the actual parameters passed to a goal. cache
  ;; is the cache from the table for reified argv. on initial
  ;; call start and end are nil - so internally they will be
  ;; initialized to the contents of the cache & 0 respectively
  (reuse [this argv cache start end]
    (let [start (or start (:ansl @cache))
          end   (or end 0)]
      (letfn [(reuse-loop [ansv*]
                (if (= (count ansv*) end)
                  ;; we've run out of answers terms to reuse in the cache
                  [(make-suspended-stream cache start
                                          (fn [] (reuse this argv cache (:ansl @cache) (count start))))]
                  ;; we have answer terms to reuse in the cache
                  (let [ans (reify-tabled this (first ansv*))
                        s (subunify this argv ans)]
                    ;; copied open maps have fresh rests, without their constraints
                    (Choice. (when s (constrain-lmap-rests s ans))
                             (fn [] (reuse-loop (rest ansv*)))))))]
        (reuse-loop start))))

  ;; unify an argument with an answer from a cache
  (subunify [this arg ans]
    (let [arg (walk this arg)]
      (cond
        (= arg ans) this
        (lvar? arg) (ext-no-check this arg ans)
        (coll? arg) (subunify
                     (subunify this (next arg) (next ans))
                     (first arg) (first ans))
        :else this))))

;; -----------------------------------------------------------------------------
;; Waiting Stream

(extend-type clojure.lang.IPersistentVector
  IBind
  (bind [this g]
    (waiting-stream-check this
      ;; success continuation
                          (fn [f] (bind f g))
      ;; failure continuation
                          (fn []
                            (into []
                                  (map (fn [ss]
                                         (make-suspended-stream (:cache ss) (:ansv* ss)
                                                                (fn [] (bind ((:f ss)) g))))
                                       this)))))

  IMPlus
  (mplus [this f]
    (waiting-stream-check this
      ;; success continuation
                          (fn [fp] (mplus fp f))
      ;; failure continuation
                          (fn []
                            (let [a-inf (f)]
                              (if (waiting-stream? a-inf)
                                (into a-inf this)
                                (mplus a-inf (fn [] this)))))))

  ITake
  (take* [this]
    (waiting-stream-check this (fn [f] (take* f)) (fn [] ()))))

(defn master
  "Take the argument to the goal and check that we don't
   have an alpha equivalent cached answer term in the cache.
   If it doesn't already exist in the cache add the new
   answer term."
  [argv cache]
  (fn [a]
    (let [rargv (-reify a argv)]
      (when-not (-cached? @cache rargv)
        (swap! cache
               (fn [cache]
                 (if (-cached? cache rargv)
                   cache
                   (-add cache (reify-tabled a argv)))))
        a))))

;; -----------------------------------------------------------------------------
;; Syntax

;; TODO: consider the concurrency implications much more closely

(defmacro tabled
  "Macro for defining a tabled goal. Prefer ^:tabled with the
  defne/a/u forms over using this directly."
  [args & grest]
  (let [uuid (symbol (str "tabled-" (UUID/randomUUID)))]
    `(fn ~uuid [~@args]
       (let [argv# ~args]
         (fn [a#]
           (let [key#    (-reify a# argv#)
                 tables# (:ts a#)
                 tables# (if-not (contains? @tables# ~uuid)
                           (swap! tables#
                                  (fn [tables#]
                                    (if (contains? tables# ~uuid)
                                      tables#
                                      (assoc tables# ~uuid (atom {})))))
                           @tables#)
                 table#  (get tables# ~uuid)]
             (if-not (contains? @table# key#)
               (let [table# (swap! table#
                                   (fn [table#]
                                     (if (contains? table# key#)
                                       table#
                                       (assoc table# key# (atom (answer-cache))))))
                     cache# (get table# key#)]
                 ((fresh []
                         ~@grest
                         (master argv# cache#)) a#))
               (let [cache# (get @table# key#)]
                 (reuse a# argv# cache# nil nil)))))))))

;; =============================================================================
;; cKanren
;;
;; See - Claire Alvis, Dan Friedman, Will Byrd, et al
;; "cKanren - miniKanren with Constraints"
;; http://www.schemeworkshop.org/2011/papers/Alvis2011.pdf
;; http://github.com/calvis/cKanren

(defn addcg [c]
  (fn [a]
    (let [a  (reduce
              (fn [a x]
                (ext-no-check a x (subst-val ::unbound)))
              a (unbound-rands a c))
          cs (addc (:cs a) a c)]
      (when cs (assoc a :cs cs)))))

(defn updatecg [c]
  (fn [a]
    (assoc a :cs (updatec (:cs a) a c))))

(defn remcg [c]
  (fn [a]
    (assoc a :cs (remc (:cs a) a c))))

(defn runcg [c]
  (fn [a]
    (assoc a :cs (runc (:cs a) c true))))

(defn stopcg [c]
  (fn [a]
    (assoc a :cs (runc (:cs a) c false))))

(defn ientailed? [c]
  (instance? clojure.core.logic.protocols.IEntailed c))

(defn entailed? [c c' a]
  (let [id (id c)]
    (and (or ((-> a :cs :cm) id)
             (nil? id))
         (-entailed? c'))))

(defn run-constraint [c]
  (fn [a]
    (let [c' (-step c a)]
      (if (or (not (ientailed? c'))
              (not (entailed? c c' a)))
        (if (-runnable? c')
          ((composeg* (runcg c) c' (stopcg c)) a)
          a)
        ((remcg c) a)))))

;; TODO NOW: try an implementation that allows constraints
;; to run roughly in the order they normaly would. reverse
;; xcs in run-constraints, (into cq (reverse xcs)), cq should
;; be persistent list.

;; TRIED: but causes overflow errors for crypt1, and if we switch to BigInt
;; for crypt1 out of memory errors, needs more investigation

(defn fix-constraints
  "A goal to run the constraints in cq until it is empty. Of
   course running a constraint may grow cq so this function
   finds the fixpoint."
  [a]
  (loop [a a]
    (when a
      (let [cq (:cq a)]
        (if (zero? (count cq))
          (assoc a :cq nil)
          (let [c (first cq)]
            (recur
             ((run-constraint c)
              (-> a
                  (assoc :cq (subvec (:cq a) 1))
                  (assoc :cqs (disj (:cqs a) (id c))))))))))))

(defn run-constraints [xcs]
  (fn [a]
    (let [cq (:cq a)
          a  (reduce (fn [a c]
                       (queue a c))
                     (assoc a :cq (or cq [])) xcs)]
      (if cq
        a
        (fix-constraints a)))))

(defn run-constraints* [xs cs ws]
  (if (or (zero? (count cs))
          (nil? (seq xs)))
    s#
    (fn [a]
      (let [xcs (constraints-for cs a (first xs) ws)]
        (if (seq xcs)
          ((composeg*
            (run-constraints xcs)
            (run-constraints* (next xs) cs ws)) a)
          ((run-constraints* (next xs) cs ws) a))))))

;; TODO: we've hard coded finite domains here

(defn verify-all-bound [a constrained]
  (letfn [(verify-all-bound* [a constrained]
            (when constrained
              (let [x (first constrained)]
                (if (and (lvar? x)
                         (and (lvar? (walk a x))
                              (nil? (get-dom a x ::fd))))
                  (throw (Exception. (str "Constrained variable " x " without domain")))
                  (recur a (next constrained))))))]
    (verify-all-bound* a (seq constrained))))

(defn enforceable-constrained [a]
  (let [cs (:cs a)
        km (:km cs)
        cm (:cm cs)
        vs (keys km)]
    (filter (fn [v]
              (some (fn [cid]
                      (when-let [c (get cm cid)]
                        (enforceable? c)))
                    (get km v)))
            vs)))

;; TODO: we've hard coded force-ans here

(declare force-ans)

(defn enforce-constraints [x]
  (all
   (force-ans x)
   (fn [a]
     (let [constrained (enforceable-constrained a)]
       (verify-all-bound a constrained)
       ((onceo (force-ans constrained)) a)))))

(declare recover-vars-from-term simplify-residuals term-children reify-constraints*)

;; Constraints that hold for some value of any var they mention, whatever
;; the other vars are: one mentioning a var the answer doesn't show is
;; satisfied by choosing that var, and is left out.
(def ^:private purgeable-rators
  #{`!= `absento `symbolo `numbero `stringo `keywordo})

(defn- purgeable? [c]
  (and (instance? clojure.core.logic.protocols.IConstraintOp c)
       (contains? purgeable-rators (-rator c))))

(defn- constraint-vars [a c]
  (if-let [args (:args (::lmap-rel (meta c)))]
    (recover-vars-from-term (walk* a (vec args)))
    (if (instance? clojure.core.logic.protocols.IConstraintOp c)
      (recover-vars-from-term (walk* a (vec (-rands c))))
      #{})))

(defn reify-constraints
  ([v r a] (reify-constraints v r a nil))
  ([v r a extra]
   (if (and (empty? (:cm (:cs a))) (empty? extra))
     ;; nothing to show: skip naming and simplifying, which cost per answer
     (choice v empty-f)
     (reify-constraints* v r a extra))))

(defn- reify-constraints* [v r a extra]
  (let [cs    (->> (:cm (:cs a)) (sort-by key) vals (filter reifiable?))
        shown (into #{} (mapcat #(constraint-vars a %)) (remove purgeable? cs))
        shown? #(or (contains? shown %) (not (lvar? (walk r %))))
        cs    (filter #(or (not (purgeable? %))
                           (every? shown? (constraint-vars a %)))
                      cs)
        ;; name the vars only constraints show, the same in each
        r     (-reify* (vary-meta r assoc ::answer-names (set (vals (:s r))))
                       (vec (mapcat #(sort-by str (constraint-vars a %)) cs)))
        rcs   (->> cs
                   (map #(-reifyc % v r a))
                   (filter #(not (nil? %)))
                   (into (set extra))
                   (simplify-residuals (set (vals (:s r)))))]
    (if (empty? rcs)
      (choice v empty-f)
      (choice `(~v :- ~@rcs) empty-f))))

(defn- value-type [names x]
  (cond
    (contains? names x) nil
    (symbol? x) `symbolo
    (number? x) `numbero
    (string? x) `stringo
    (keyword? x) `keywordo
    :else ::other))

(defn- simplify-residuals
  "Simplifies reified residual constraints as faster-miniKanren does: drops
   disequalities implied by types or by other disequalities, and absento on
   a typed var. names are the reified vars."
  [names rcs]
  (let [types (into {} (keep (fn [f]
                               (when (and (seq? f) (= 2 (count f))
                                          (#{`symbolo `numbero `stringo `keywordo} (first f)))
                                 [(second f) (first f)])))
                    rcs)
        ;; u and v can never be equal because of their types
        apart? (fn [u v]
                 (let [tu (or (types u) (value-type names u))
                       tv (or (types v) (value-type names v))]
                   (and tu tv (not= tu tv))))
        pairs (fn [f] (set (map (fn [[u v]] #{u v}) (rest f))))
        neq? #(and (seq? %) (= '!= (first %)) (every? sequential? (rest %)))
        rcs (keep (fn [f]
                    (cond
                      (and (neq? f) (some (fn [[u v]] (apart? u v)) (rest f)))
                      nil

                      (and (seq? f) (= `absento (first f)) (types (nth f 2)))
                      (let [[_ t x] f]
                        (cond
                          (apart? t x) nil
                          (and (contains? names t) (not (types t))) f
                          :else `(~'!= (~x ~t))))

                      :else f))
                  rcs)
        absento? #(and (seq? %) (= `absento (first %)))
        ;; for each x, the terms absent from it
        absents (reduce (fn [m [_ t x]] (update-in m [x] (fnil conj #{}) t))
                        {} (filter absento? rcs))
        absent? (fn [t x] (contains? (get absents x) t))
        strictly-in? (fn in? [x t]
                       (some #(or (= x %) (in? x %)) (term-children t)))
        rcs (keep (fn [f]
                    (if (and (seq? f) (= `absento (first f)))
                      (let [[_ t x] f]
                        (when-not (or
                                   ;; x can't hold a term containing x
                                   (and (contains? names x) (strictly-in? x t))
                                   ;; a part of t is absent already
                                   (some #(strictly-in? % t) (get absents x)))
                          f))
                      ;; absento t x implies x != t, so a disequality
                      ;; holds when one of its pairs can't
                      (when-not (and (neq? f)
                                     (some (fn [[u v]] (or (absent? v u) (absent? u v)))
                                           (rest f)))
                        f)))
                  rcs)
        neqs (filter neq? rcs)]
    (set (remove (fn [f]
                   (and (neq? f)
                        (some #(and (not (identical? % f))
                                    (let [p (pairs %) q (pairs f)]
                                      (and (every? q p)
                                           (or (< (count p) (count q))
                                               ;; of two equal ones keep one
                                               (pos? (compare (pr-str f) (pr-str %)))))))
                              neqs)))
                 rcs))))

(declare lmap-force recover-vars-from-term)

(defn- some-answer?
  "Whether the stream has at least one answer. Searches depth first."
  [st]
  (loop [st st]
    (cond
      (nil? st) false
      (instance? clojure.lang.Fn st) (recur (st))
      :else true)))

(defn- reify-answer
  "A goal giving the reified answer x. residual, when given, is a fn of the
   answer's vars, the reifier r and the substitution a returning the reifier
   extended by the vars it names, and further residual forms."
  [x residual]
  (fn [a]
    (let [n (.get map-key-collision-count)
          v (walk* a x)]
      ;; two keys of a map in the answer became equal: it denotes no map
      (when-not (map-keys-collided-since? n)
        (let [r (-reify* (with-meta empty-s (meta a)) v)
              [r extra] (if residual
                          (residual (recover-vars-from-term v) r a)
                          [r nil])]
          (if (and (zero? (count r)) (empty? extra))
            (choice v empty-f)
            (reify-constraints (walk* r v) r a extra)))))))

(defn reifyg [x]
  (fn [a]
    (if-let [residual (::residual (meta a))]
      ;; leave constrained vars unlabeled, but only answer if labeling them
      ;; would find a solution
      ((all
        lmap-force
        (fn [a]
          (when (some-answer? ((all (enforce-constraints x) lmap-force) a))
            a))
        (reify-answer x residual)) a)
      ((all
        lmap-force
        (enforce-constraints x)
        ;; labeling may have woken relations that are ambiguous again
        lmap-force
        (reify-answer x nil)) a))))

(defn cgoal [c]
  (reify
    clojure.lang.IFn
    (invoke [_ a]
      (let [c' (-step c a)]
        (if (-runnable? c')
          (when-let [a (c' a)]
            (let [c' (-step c a)]
              (if (and (ientailed? c')
                       (not (entailed? c c' a)))
                ((addcg c) a)
                a)))
          ((addcg c) a))))
    IUnwrapConstraint
    (-unwrap [_] c)))

;; TODO: this stuff needs to be moved into fd - David

(defn get-dom-fd
  [a x]
  (if (lvar? x)
    (get-dom a x ::fd)
    x))

(defmacro let-dom
  [a vars & body]
  (let [get-var-dom (fn [a [v b]]
                      `(~b (get-dom-fd ~a ~v)))]
    `(let [~@(mapcat (partial get-var-dom a) (partition 2 vars))]
       ~@body)))

(defn sort-by-member-count [a]
  (fn [x y]
    (let-dom a [x dx y dy]
             (< (-member-count dx) (-member-count dy)))))

(defn sort-by-strategy [v x a]
  (case (-> x meta ::strategy)
    ::ff (seq (sort (sort-by-member-count a) v))
    ;; TODO: throw on non-existant strategies
    v))

;; TODO: handle all Clojure tree types
(extend-protocol IForceAnswerTerm
  nil
  (-force-ans [v x] s#)

  Object
  (-force-ans [v x]
    (if (lvar? x)
      (ext-run-csg x v)
      s#))

  clojure.lang.Sequential
  (-force-ans [v x]
    (letfn [(loop [ys]
              (if ys
                (all
                 (force-ans (first ys))
                 (fn [a]
                   (if-let [ys (sort-by-strategy (next ys) x a)]
                     ((loop ys) a)
                     a)))
                s#))]
      (loop (seq v))))

  clojure.lang.IPersistentMap
  (-force-ans [v x]
    (letfn [(loop [ys]
              (if ys
                (all
                 (force-ans (val (first ys)))
                 (loop (next ys)))
                s#))]
      (loop (seq v))))

  LCons
  (-force-ans [v x]
    (letfn [(loop [ys]
              (all
               (force-ans (lfirst ys))
               (if (lcons? (lnext ys))
                 (loop (lnext ys))
                 s#)))]
      (loop v))))

(defn force-ans [x]
  (fn [a]
    ((let [v (walk a x)]
       (if (lvar? v)
         (-force-ans (get-dom-fd a x) v)
         (let [x (root-var a x)]
           (if (sequential? v)
             (-force-ans (sort-by-strategy v x a) x)
             (-force-ans v x))))) a)))

(defn distribute [v* strategy]
  (fn [a]
    (add-attr a v* ::strategy ::ff)))

;; =============================================================================
;; CLP(Tree)

(defn disunify
  ([s u v] (disunify s u v {:prefixc {}}))
  ([s u v cs]
   (if (identical? u v)
     cs
     (let [u (walk s u)
           v (walk s v)]
       ;; a walked var may be a copy of the var: compare vars by =
       (if (or (identical? u v) (and (lvar? u) (lvar? v) (= u v)))
         cs
         (if (and (not (lvar? u)) (lvar? v))
           (-disunify-terms v u s cs)
           (-disunify-terms u v s cs)))))))

(extend-protocol IDisunifyTerms
  nil
  (-disunify-terms [u v s cs]
    (if-not (nil? v) nil cs))

  Object
  (-disunify-terms [u v s cs]
    (if-not (= u v) nil cs))

  LVar
  (-disunify-terms [u v s {pc :prefixc :as cs}]
    ;; the prefix is a substitution too: a var paired already is replaced
    ;; by its partner, so that no pairing is lost
    (cond
      (contains? pc u) (disunify s (pc u) v cs)
      (and (lvar? v) (contains? pc v)) (disunify s u (pc v) cs)
      :else (assoc cs :prefixc (assoc pc u v))))

  LCons
  (-disunify-terms [u v s cs]
    (cond
      (lvec? v) (-disunify-terms v u s cs)

      ;; pair up the heads, then disunify the tails, which may be vars
      (sequential? v)
      (when-let [v (seq v)]
        (when-let [cs (disunify s (lfirst u) (first v) cs)]
          (disunify s (lnext u) (rest v) cs)))

      (lcons? v)
      (when-let [cs (disunify s (lfirst u) (lfirst v) cs)]
        (disunify s (lnext u) (lnext v) cs))

      :else nil))

  clojure.lang.Sequential
  (-disunify-terms [u v s cs]
    (if (or (lcons? v) (lvec? v))
      (-disunify-terms v u s cs)
      (if (sequential? v)
        (loop [u (seq u) v (seq v) cs cs]
          (if u
            (if v
              (let [uv (first u)
                    vv (first v)
                    cs (disunify s uv vv cs)]
                (if cs
                  (recur (next u) (next v) cs)
                  nil))
              nil)
            (if (nil? v)
              cs
              nil)))
        nil)))

  clojure.lang.IPersistentMap
  (-disunify-terms [u v s cs]
    (cond
      (lmap? v)
      (-disunify-terms v u s cs)

      ;; which keys pair up is not known yet: keep the pair whole, the !=
      ;; constraint rechecks it whenever one of its vars is bound
      (and (map? v)
           (not (and (every? atomic-key? (keys u))
                     (every? atomic-key? (keys v)))))
      (when (unify s u v)
        (assoc cs :prefixc (assoc (:prefixc cs) u v)))

      (and (map? v) (= (count u) (count v)))
      (loop [ks (seq (keys u)) cs cs]
        (if ks
          (let [kf (first ks)
                vf (get v kf ::not-found)]
            (when-not (= vf ::not-found)
              (if-let [cs (disunify s (get u kf) vf cs)]
                (recur (next ks) cs)
                nil)))
          cs))

      :else nil)))

#_(defn prefix-subsumes? [p pp]
    (let [s (-> p meta :s)
          sp (reduce (fn [s [lhs rhs]]
                       (unify s lhs rhs))
                     s pp)]
      (when sp
        (identical? s sp))))

(defn recover-vars-from-term
  "The vars in the term x. Traverses x directly: the walk-term of LCons
   doesn't descend into its parts."
  [x]
  (loop [todo (list x) r (transient #{})]
    (if-let [[x & todo] (seq todo)]
      (cond
        (lvar? x) (recur todo (conj! r x))
        (lcons? x) (recur (list* (lfirst x) (lnext x) todo) r)
        (map? x) (recur (concat (keys x) (vals x) todo) r)
        (coll? x) (recur (concat x todo) r)
        (tree-term? x) (if-let [cs (term-children x)]
                         (recur (concat cs todo) r)
                         (let [r* (atom r)]
                           (walk-term x (fn [y] (when (lvar? y) (swap! r* conj! y)) y))
                           (recur todo @r*)))
        :else (recur todo r))
      (persistent! r))))

(defn recover-vars [p]
  (loop [p (seq p) r #{}]
    (if p
      (let [[u v] (first p)]
        (recur (next p)
               (clojure.set/union
                r (recover-vars-from-term u) (recover-vars-from-term v))))
      r)))

(declare normalize-store ground-term?)

(defn !=c [p]
  (reify
    ITreeConstraint
    IConstraintStep
    (-step [this s]
      (reify
        clojure.lang.IFn
        (invoke [_ s]
          (let [p (loop [sp (seq p) p p]
                    (if sp
                      (let [[x v] (first sp)
                             ;; TODO: this seems expensive to walk* both sides
                             ;; and run an equality test there must be a better
                             ;; way - David
                            xv (walk* s x)
                            vv (walk* s v)
                            ;; not =: LCons equality takes vars as wildcards
                            s' (unify s xv vv)]
                        (cond
                          (nil? s') nil
                          (identical? s' s) (recur (next sp) (dissoc p x))
                          :else (recur (next sp) (assoc (dissoc p x) xv vv))))
                      p))]
            (if p
              (when-not (empty? p)
                ((composeg*
                  (remcg this)
                  (cgoal (!=c p))) s))
              ((remcg this) s))))
        IRunnable
        (-runnable? [_]
          (some #(not= (walk s %) %) (recover-vars p)))
        IEntailed
        (-entailed? [_]
          (empty? p))))
    IPrefix
    (-prefix [_] p)
    IWithPrefix
    (-with-prefix [_ p] (!=c p))
    IReifiableConstraint
    (-reifyc [this v r a]
      ;; disunify again, to show the pairs of vars and atoms left; when a
      ;; pair can't hold any more, the constraint holds. Without this
      ;; constraint in the store: disunifying maps and vectors unifies the
      ;; pair, which this constraint would forbid.
      (when-let [cs (let [a ((remcg this) a)]
                      (reduce (fn [cs [u v]] (or (disunify a u v cs) (reduced nil)))
                              {:prefixc {}} p))]
        (let [p* (-reify a (map (fn [[lhs rhs]] `(~lhs ~rhs)) (:prefixc cs)) r)]
          (if (empty? p*)
            '()
            `(~'!= ~@p*)))))
    IConstraintOp
    (-rator [_] `!=)
    (-rands [_] (seq (recover-vars p)))
    IConstraintWatchedStores
    (-watched-stores [this] #{::subst})))

(defn !=
  "Disequality constraint. Ensures that u and v will never
   unify. u and v can be complex terms."
  [u v]
  (fn [a]
    (let [cs (disunify a u v)]
      (if-not (nil? cs)
        (let [p (:prefixc cs)]
          (when-not (empty? p)
            (if  (some (fn [[u v]] (nil? (unify a u v))) p)
              a
              ((cgoal (!=c p)) a))))
        a))))

(defne distincto
  "A relation which guarantees no element of l will unify
   with another element of l."
  [l]
  ([()])
  ([[h]])
  ([[h0 h1 . t]]
   (!= h0 h1)
   (distincto (lcons h0 t))
   (distincto (lcons h1 t))))

(defne rembero
  "A relation between l and o where x is removed from
   l exactly one time."
  [x l o]
  ([_ [x . xs] xs])
  ([_ [y . ys] [y . zs]]
   (!= y x)
   (rembero x ys zs)))

;; =============================================================================
;; Partial Maps

(declare featurec partial-map unify-pmap-relational unify-pmap-with-lmap)

(defn unify-with-pmap* [u v s]
  (loop [ks (keys u) s s]
    (if (seq ks)
      (let [kf (first ks)
            vf (if (atomic-key? kf) (get v kf ::not-found) ::not-plain)]
        (cond
          ;; a key that is not a plain value, here or possibly in v
          (or (identical? vf ::not-plain)
              (and (identical? vf ::not-found)
                   (not (every? atomic-key? (keys v)))))
          (unify-pmap-relational u v s)

          (identical? vf ::not-found)
          nil

          :else
          (let [uf (get u kf)
                vf (walk s vf)]
            (if (and (lvar? vf) (map? uf))
              (recur (next ks) ((featurec vf uf) s))
              (if (map? uf)
                (if-let [s (unify s (partial-map uf) vf)]
                  (recur (next ks) s))
                (if-let [s (unify s uf vf)]
                  (recur (next ks) s)
                  nil))))))
      s)))

(declare partial-map?)

(defrecord PMap []
  INonStorable

  IUnifyTerms
  (unify-terms [u v s]
    (cond
      (lmap? v) (unify-pmap-with-lmap u v s)
      (map? v) (unify-with-pmap* u v s)
      :else nil))

  IUnifyWithRecord
  (unify-with-record [u v s]
    (if (map? v)
      (unify-with-pmap* u v s)
      nil))

  IUninitialized
  (-uninitialized [_] (PMap.)))

(defn partial-map
  "Given map m, returns partial map that unifies with maps even if it
   doesn't share all of the keys of that map."
  [m]
  (map->PMap m))

(defn partial-map? [x]
  (instance? PMap x))

(extend-type clojure.lang.IPersistentMap
  IFeature
  (-feature [x] (partial-map x)))

(defn -featurec
  [x fs]
  (reify
    IConstraintStep
    (-step [this s]
      (reify
        clojure.lang.IFn
        (invoke [_ s]
          (let [fs (walk s fs)]
            ((composeg
              (== (partial-map fs) x)
              (remcg this)) s)))
        IRunnable
        (-runnable? [_]
          (and (not (lvar? (walk s x)))
               (not (lvar? (walk s fs)))))))
    IConstraintOp
    (-rator [_] `featurec)
    (-rands [_] [x])
    IReifiableConstraint
    (-reifyc [_ v r a]
      (if-not (lvar? fs)
        (let [fs (into {} fs)
              r (-reify* r (walk* a fs))]
          `(featurec ~(walk* r x) ~(walk* r fs)))
        (let [[x fs] (-reify a [x fs] r)]
          `(featurec ~x ~fs))))
    IConstraintWatchedStores
    (-watched-stores [this] #{::subst})))

(defn featurec
  "Ensure that a map contains at least the key-value pairs
  in the map fs. fs must be partially instantiated - that is,
  it may contain values which are logic variables to support
  feature extraction."
  [x fs]
  (cgoal (-featurec x fs)))

;; =============================================================================
;; defnc

(defn ground-term? [x s]
  (letfn [(-ground-term? [x s]
            (let [x (walk s x)]
              (if (lvar? x)
                (throw fk)
                (walk-term x
                           (fn [x]
                             (let [x (walk s x)]
                               (cond
                                 (lvar? x) (throw fk)
                                 (tree-term? x) (-ground-term? x s)
                                 :else x)))))))]
    (try
      (-ground-term? x s)
      true
      (catch Exception e
        false))))

;; consider ^:partial type hint for arguments
;; these argument only need to be partially instantiated

(defmacro fnc
  "Define an anonymous constraint that can be used with the unifier:

     (let [oddc (fnc [x] (odd? x))]

       (unifier {:a '?a} {:a 1} :when {'?a oddc})
         ;;=> {:a 1}

       (unifier {:a '?a} {:a 2} :when {'?a oddc})
         ;;=> nil
     )

  Note, the constraint will not run until all arguments are fully ground.

  Use defnc to define a constraint and assign a toplevel var."
  [args & body]
  (let [name (symbol (gensym "fnc"))]
    `(fn ~args
       (letfn [(~name [~@args]
                 (reify
                   clojure.core.logic.protocols/IConstraintStep
                   (-step [this# a#]
                     (reify
                       ~'clojure.lang.IFn
                       (~'invoke [_# a#]
                         (let [[~@args :as args#] (map #(clojure.core.logic/walk* a# %) ~args)
                               test# (do ~@body)]
                           (when test#
                             ((clojure.core.logic/remcg this#) a#))))
                       clojure.core.logic.protocols/IRunnable
                       (~'-runnable? [_#]
                         (clojure.core.logic/ground-term? ~args a#))))
                   clojure.core.logic.protocols/IConstraintOp
                   (~'-rator [_#] '~name)
                   (~'-rands [_#] (filter clojure.core.logic/lvar? (flatten ~args)))
                   clojure.core.logic.protocols/IReifiableConstraint
                   (~'-reifyc [_# _# r# a#]
                     (list '~name (map #(clojure.core.logic/-reify r# %) ~args)))
                   clojure.core.logic.protocols/IConstraintWatchedStores
                   (~'-watched-stores [_#] #{:clojure.core.logic/subst})))]
         (cgoal (~name ~@args))))))

(defmacro defnc [name args & body]
  `(def ~name (fnc ~args ~@body)))

;; =============================================================================
;; Predicate Constraint

(defn -predc
  ([x p] (-predc x p p))
  ([x p pform]
   (reify
     IConstraintStep
     (-step [this s]
       (reify
         clojure.lang.IFn
         (invoke [_ s]
           (let [x (walk s x)]
             (when (p x)
               ((remcg this) s))))
         IRunnable
         (-runnable? [_]
           (not (lvar? (walk s x))))))
     IConstraintOp
     (-rator [_] (if (seq? pform)
                   `(predc ~pform)
                   `predc))
     (-rands [_] [x])
     IReifiableConstraint
     (-reifyc [c v r s]
       (if (and (not= p pform) (fn? pform))
         (pform c v r s)
         pform))
     IConstraintWatchedStores
     (-watched-stores [this] #{::subst}))))

(defn predc
  ([x p] (predc x p p))
  ([x p pform]
   (cgoal (-predc x p pform))))

;; =============================================================================
;; Negation as failure

(defn tramp [f]
  (loop [f f]
    (if (fn? f)
      (recur (f))
      f)))

(defn -nafc
  ([c args]
   (reify
     IConstraintStep
     (-step [this s]
       (reify
         clojure.lang.IFn
         (invoke [_ s]
           (when-not (tramp ((apply c args) s))
             ((remcg this) s)))
         IRunnable
         (-runnable? [_]
           (every? #(ground-term? % s) args))))
     IConstraintOp
     (-rator [_]
       `nafc)
     (-rands [_]
       (vec (concat [c] args)))
     IReifiableConstraint
     (-reifyc [_ v r s]
       `(nafc ~c ~@(-reify s args r)))
     IConstraintWatchedStores
     (-watched-stores [this] #{::subst}))))

(defn nafc
  "EXPERIMENTAL: negation as failure constraint. All arguments to the goal c
   must be ground. If some argument is not ground the execution of this constraint
   will be delayed."
  [c & args]
  (cgoal (-nafc c args)))

;; =============================================================================
;; conjo

(extend-protocol IJonc
  clojure.lang.IPersistentMap
  (-joncf [f]
    (fn [coll & args]
      (reduce
       (fn [m [k v]]
         (if (= (get m k) v)
           (dissoc m k v)
           (reduced ::failed)))
       coll args)))

  clojure.lang.IPersistentVector
  (-joncf [f]
    (fn [coll & args]
      (let [args (reverse args)]
        (reduce
         (fn [v x]
           (if (= (peek v) x)
             (pop v)
             (reduced ::failed)))
         coll args))))

  clojure.lang.IPersistentList
  (-joncf [f]
    (fn [coll & args]
      (let [args (reverse args)]
        (reduce
         (fn [v x]
           (if (= (peek v) x)
             (pop v)
             (reduced ::failed)))
         coll args)))))

(defn -conjo
  ([coll args out]
   (reify
     IConstraintStep
     (-step [this s]
       (reify
         clojure.lang.IFn
         (invoke [_ s]
           (let [coll (walk s coll)
                 args (walk s args)]
             (if-not (lvar? coll)
               ((composeg
                 (== (apply conj coll args) out)
                 (remcg this)) s)
               (let [out  (walk s out)
                     outv (apply (-joncf out) out args)]
                 (if-not (= outv ::failed)
                   ((composeg
                     (== outv coll)
                     (remcg this)) s))))))
         IRunnable
         (-runnable? [_]
           (= (count (filter #(ground-term? % s) [coll args out])) 2))))
     IConstraintOp
     (-rator [_]
       `conjo)
     (-rands [_]
       (vec (concat [coll] args [out])))
     IReifiableConstraint
     (-reifyc [_ v r s]
       `(conjo ~coll ~@(-reify s (concat args [out]) r)))
     IConstraintWatchedStores
     (-watched-stores [this] #{::subst}))))

;; conjo itself is relational now, see the LVec section.

;; =============================================================================
;; Deep Constraint

(declare treec)

(extend-protocol IConstrainTree
  LCons
  (-constrain-tree [t fc s]
    (loop [t t s s]
      (if (lvar? t)
        (fc t s)
        (when-let [s (fc (lfirst t) s)]
          (recur (lnext t) s)))))

  clojure.lang.Sequential
  (-constrain-tree [t fc s]
    (loop [t (seq t) s s]
      (if t
        (when-let [s (fc (first t) s)]
          (recur (next t) s))
        s)))

  clojure.lang.IPersistentMap
  (-constrain-tree [t fc s]
    (loop [t (seq t) s s]
      (if t
        (let [[_ v] (first t)
              s (fc v s)]
          (when s
            (recur (next t) s)))
        s))))

(defn constrain-tree [t fc]
  (fn [a]
    (-constrain-tree t fc a)))

(defn -fixc
  ([x f reifier] (-fixc x f nil reifier))
  ([x f runnable reifier]
   (reify
     IConstraintStep
     (-step [this s]
       (let [xv (walk s x)]
         (reify
           clojure.lang.IFn
           (invoke [_ s]
             ((composeg (f xv s reifier) (remcg this)) s))
           IRunnable
           (-runnable? [_]
             (if (fn? runnable)
               (runnable x s)
               (not (lvar? xv)))))))
     IConstraintOp
     (-rator [_] `fixc)
     (-rands [_] (if (vector? x) x [x]))
     IReifiableConstraint
     (-reifyc [c v r s]
       (if (fn? reifier)
         (reifier c x v r s)
         (let [x (walk* r x)]
           `(fixc ~x ~reifier))))
     IConstraintWatchedStores
     (-watched-stores [this] #{::subst}))))

(defn fixc
  ([x f reifier] (fixc x f nil reifier))
  ([x f runnable reifier]
   (cgoal (-fixc x f runnable reifier))))

(defn treec [x fc reifier]
  (fixc x
        (fn loop [t a reifier]
          (if (tree-term? t)
            (composeg*
             (fc t)
             (constrain-tree t
                             (fn [t a] ((fixc t loop reifier) a))))
            (fc t)))
        reifier))

(defn seqc [v]
  (fixc v
        (fn [t _ _]
          (cond
            (sequential? t) succeed
            (lcons? t) (seqc (lnext t))
            :else fail))
        (fn [_ v _ r a]
          `(seqc ~(-reify a v r)))))

;; =============================================================================
;; LMap - Relational Maps
;;
;; Maps are relational in two ways:
;;
;; - Keys may be logic terms that are not ground yet. The keys of a map term
;;   are pairwise distinct, so {k1 1 k2 2} denotes a map of two entries and
;;   fails once k1 and k2 become equal. Unifying maps whose keys are not all
;;   ground branches over which keys pair up.
;;
;; - An LMap is an open map: known entries plus a rest, a logic var standing
;;   for the map of all other entries, disjoint from the known ones. LMaps
;;   are only created by the relations below (lmapo, geto, ...), which
;;   constrain each rest to lack the known keys (lacks-keyo) before anything
;;   can bind it. Their keys are always ground; a map whose keys are not is
;;   always closed, i.e. a plain map.
;;
;; The relations never fail just because too little is known yet. They
;; branch over the possibilities, or suspend until more of their arguments
;; are bound. A suspended relation that wakes up inside the constraint
;; solver, or a branching unification, commits if exactly one alternative
;; survives and otherwise stays pending; its alternatives are enumerated
;; just before an answer is reified (see lmap-force). Relations still
;; pending then appear in the answer as constraints, e.g. (geto _0 _1 1).
;;
;; Keeping map keys distinct is part of the occurs check: run and run* check
;; every map they bind, run-nc only the maps it unifies, passes to a
;; relation or returns in an answer.

(declare lmap? lmap* lmap-picko lacks-keyo geto unify-pmap-with-lmap lmap-ensure-lacks)

(deftype LMap [entries rest ^{:unsynchronized-mutable true :tag int} cache]
  ITreeTerm

  clojure.lang.IObj
  (meta [this] nil)
  (withMeta [this new-meta] this)

  Object
  (toString [this]
    (str "(lmap " entries " | " rest ")"))

  (equals [this o]
    (or (identical? this o)
        (and (instance? LMap o)
             (= entries (.entries ^LMap o))
             (= rest (.rest ^LMap o)))))

  (hashCode [this]
    (if (clojure.core/== cache -1)
      (do
        (set! cache (unchecked-add-int
                     (unchecked-multiply-int 31 (clojure.lang.Util/hash entries))
                     (clojure.lang.Util/hash rest)))
        cache)
      cache))

  IUnifyTerms
  (unify-terms [u v s]
    (cond
      (partial-map? v) (unify-pmap-with-lmap v u s)
      (or (map? v) (lmap? v)) (unify-map-terms u v s)
      :else nil))

  IReifyTerm
  (reify-term [v s]
    (-reify* (loop [kvs (seq entries) s s]
               (if kvs
                 (let [[k val] (first kvs)]
                   (recur (next kvs) (-reify* (-reify* s k) val)))
                 s))
             rest))

  IWalkTerm
  (walk-term [v f]
    (let [es (into {} (map (fn [[k val]]
                             [(walk-term (f k) f) (walk-term (f val) f)])
                           entries))
          r (walk-term (f rest) f)]
      ;; a rest repeating a known key denotes no map
      (when (and (map? r) (not (lmap? r))
                 (some #(contains? es %) (keys r)))
        (map-keys-collided!))
      (lmap* es r)))

  IOccursCheckTerm
  (occurs-check-term [v x s]
    (or (some (fn [[k val]]
                (or (occurs-check s x k)
                    (occurs-check s x val)))
              entries)
        (occurs-check s x rest)))

  IBuildTerm
  (build-term [u s]
    (build (loop [kvs (seq entries) s s]
             (if kvs
               (let [[k val] (first kvs)]
                 (recur (next kvs) (build (build s k) val)))
               s))
           rest)))

(defmethod print-method LMap [x ^Writer writer]
  (.write writer (str x)))

(defn lmap?
  "Returns true if x is an LMap, an open map in an answer."
  [x]
  (instance? LMap x))

(defn lmap-entries
  "Returns the known entries of an LMap, or the map itself if not an LMap."
  [x]
  (if (lmap? x) (.entries ^LMap x) x))

(defn lmap-rest
  "Returns the rest (unknown entries) of an LMap, or nil."
  [x]
  (if (lmap? x) (.rest ^LMap x) nil))

(defn- lmap*
  "Normal form of the map with the given entries and rest: a plain map if
   rest is nil or a map, the rest itself if there are no entries, otherwise
   an LMap whose rest is not itself a map."
  [entries rest]
  (cond
    (nil? rest) entries
    (lmap? rest) (recur (merge (.entries ^LMap rest) entries) (.rest ^LMap rest))
    (map? rest) (merge rest entries)
    (empty? entries) rest
    :else (LMap. entries rest -1)))

(defn- ground-key?
  "True if the fully walked term k contains no unbound logic var."
  [k]
  (cond
    (lvar? k) false
    (lcons? k) (and (ground-key? (lfirst k)) (ground-key? (lnext k)))
    (lmap? k) false
    (map? k) (every? (fn [[a b]] (and (ground-key? a) (ground-key? b))) k)
    (coll? k) (every? ground-key? k)
    :else true))

(defn- term-vars
  "The unbound vars in the terms ts."
  [s ts]
  (vec (recover-vars-from-term (walk* s (vec ts)))))

;; -----------------------------------------------------------------------------
;; Distinct keys

(declare map-parts coll-parts lset?)

(defn- coll-keys
  "The keys of map m, or the elements of set m."
  [m]
  (if (set? m) (seq m) (keys m)))

(defn- -map-keysc
  "Constraint that the keys of map m stay pairwise distinct, rechecked
   whenever one of the vars in watch is bound."
  [m watch]
  (with-meta
    (reify
      IConstraintStep
      (-step [this s]
        (reify
          clojure.lang.IFn
          (invoke [_ s]
            ;; map-parts fails on equal keys and re-adds this constraint
            ;; for keys that are still not ground
            (when-let [s ((remcg this) s)]
              (first (coll-parts s m))))
          IRunnable
          (-runnable? [_]
            ;; a key got a value, or two keys became the same var
            (let [ws (map #(walk s %) watch)]
              (boolean (or (some #(not (lvar? %)) ws)
                           (and (next ws) (not (apply distinct? ws)))))))))
      IConstraintOp
      (-rator [_] `distincto)
      (-rands [_] watch)
      IReifiableConstraint
      (-reifyc [_ v r a]
        ;; implied when the map itself is part of the answer
        (let [m' (walk* r (walk* a m))]
          (when-not (some #(= m' %) (tree-seq coll? seq v))
            `(distincto ~(vec (coll-keys m'))))))
      IConstraintWatchedStores
      (-watched-stores [_] #{::subst}))
    {::map-keys m}))

(defn- ensure-distinct-keys
  "Constrains the keys of map m to stay distinct, unless that is already
   done. Takes and returns a substitution."
  [s m]
  (let [watch (term-vars s (coll-keys m))
        cs (:cs s)
        done? (some (fn [cid]
                      (identical? m (::map-keys (meta ((:cm cs) cid)))))
                    (get (:km cs) (root-var s (first watch))))]
    (if done?
      s
      ((cgoal (-map-keysc m watch)) s))))

;; Maps grown one key at a time through their rests form chains, which
;; every later walk would follow again. Once walked, the var holding such a
;; chain is rebound to the equal flat map, which keeps repeated lookups on a
;; growing map from turning quadratic.
(defn- compress-map
  "Rebinds the var x, whose map spans more than one link, to the flat map
   term. Takes and returns a substitution."
  [s x links term]
  (if (and (> links 1) (lvar? x))
    (let [root (root-var s x)
          sm (:s s)]
      (if (let [v (get sm root)] (or (lmap? v) (lset? v)))
        (assoc s :s (assoc sm root term))
        s))
    s))

(defn- map-parts
  "Walks x in s and splits the map it denotes into [s ground nonground tail]:
   the entries with ground keys (a map), the entries whose keys are not
   ground yet (a vector of pairs), and the open tail, an unbound var or nil
   for a closed map. An unbound x is a map with nothing known. Returns nil
   if x is not a map or two of its keys are equal."
  [s x0]
  (letfn [(add-ground [g es]
            ;; disjoint union, without copying either map when possible
            (cond
              (empty? g) es
              (empty? es) g
              (< (count g) (count es))
              (when (not-any? #(contains? es %) (keys g)) (merge es g))
              :else
              (when (not-any? #(contains? g %) (keys es)) (merge g es))))]
    (loop [s s x (walk s x0) g {} links 0]
      (cond
        (lvar? x) [(compress-map s x0 links (lmap* g x)) g [] x]
        (lmap? x) (when-let [g (add-ground g (.entries ^LMap x))]
                    (recur s (walk s (.rest ^LMap x)) g (inc links)))
        (map? x) (if (every? atomic-key? (keys x))
                   (when-let [g (add-ground g x)]
                     [(compress-map s x0 links g) g [] nil])
                   (let [es (map (fn [[k v]] [(walk* s k) v]) x)
                         ground (filter (comp ground-key? first) es)
                         nonground (vec (remove (comp ground-key? first) es))
                         g' (into {} ground)]
                     (when (and (clojure.core/== (count g') (count ground))
                                (= (count nonground) (count (distinct (map first nonground)))))
                       (when-let [g (add-ground g g')]
                         (if (and (seq nonground) (> (count x) 1))
                           (when-let [s (ensure-distinct-keys s x)]
                             [s g nonground nil])
                           [s g nonground nil])))))
        :else nil))))

(defn- map-term
  "The map term with ground entries g, nonground entries n and tail."
  [g n tail]
  (if (seq n)
    (into g n)
    (lmap* g tail)))

(defn- map-term-without
  "The map term [g n tail] without the entry for key k."
  [g n tail k]
  (if (contains? g k)
    (map-term (dissoc g k) n tail)
    (map-term g (vec (remove #(= k (first %)) n)) tail)))

(defn constrain-lmap-rests
  "Constrains the rest of every open map in the term t to lack the map's
   known keys, for open maps copied with fresh rests (tabling, copy-term).
   Takes and returns a substitution."
  [s t]
  (letfn [(walk-into [s t]
            (cond
              (nil? s) nil
              (lmap? t) (let [s (reduce (fn [s [k v]] (walk-into (walk-into s k) v))
                                        s (.entries ^LMap t))
                              r (.rest ^LMap t)]
                          (if (and s (lvar? (walk s r)))
                            (lmap-ensure-lacks s (walk s r) (keys (.entries ^LMap t)))
                            s))
              (lcons? t) (walk-into (walk-into s (lfirst t)) (lnext t))
              (coll? t) (reduce walk-into s t)
              :else s))]
    (walk-into s t)))

(defn- check-map-keys
  "Checks the keys of maps that were just bound and are not all plain
   values: fails if two are equal, and keeps them distinct from now on."
  [s maps]
  (reduce (fn [s m] (or (first (coll-parts s m)) (reduced nil))) s maps))

;; -----------------------------------------------------------------------------
;; Absent keys

(declare lmap-lacks lmap-lacks-ground lset? lset-elems lset-rest)

(defn- lmap-lacks-constraint
  "The lacks-constraint on the var x, if any. There is at most one."
  [s x]
  (let [cs (:cs s)
        cm (:cm cs)]
    (some (fn [cid]
            (let [c (cm cid)]
              (when (::lmap-lacks (meta c)) c)))
          (get (:km cs) (root-var s x)))))

(defn- lmap-implied-keys
  "The keys that reified answer v already shows to be absent from the var
   reified as sym: the entries of every LMap in v whose rest is sym."
  [v sym]
  (letfn [(implied [acc t]
            (cond
              (lmap? t) (let [acc (reduce implied acc (vals (.entries ^LMap t)))]
                          (if (= (.rest ^LMap t) sym)
                            (into acc (keys (.entries ^LMap t)))
                            acc))
              (map? t) (reduce implied acc (vals t))
              (coll? t) (reduce implied acc t)
              (lvec? t) (reduce implied acc (lvec-parts t))
              (lset? t) (let [acc (reduce implied acc (lset-elems t))]
                          (if (= (lset-rest t) sym)
                            (into acc (lset-elems t))
                            acc))
              :else acc))]
    (implied #{} v)))

(defn- -lmap-lacksc
  "Constraint that the map the var x gets bound to has none of the ground
   keys ks, or for kind :set, that the set has none of those elements."
  [x ks kind]
  (with-meta
    (reify
      IConstraintStep
      (-step [this s]
        (reify
          clojure.lang.IFn
          (invoke [_ s]
            ((composeg (remcg this) (lmap-lacks-ground x ks kind)) s))
          IRunnable
          (-runnable? [_]
            (not (lvar? (walk s x))))))
      IConstraintOp
      (-rator [_] (if (= kind :set) `lackso `lacks-keyo))
      (-rands [_] [x])
      IReifiableConstraint
      (-reifyc [_ v r a]
        ;; hide what the answer already shows, e.g. the rest of (lmap {:a 1} | _0)
        ;; lacks :a, and constraints on vars that are not part of the answer
        (let [sym (walk* r (walk* a x))
              names (::answer-names (meta r))]
          (when (if names (contains? names sym) (not (lvar? sym)))
            (when-let [shown (seq (remove (lmap-implied-keys v sym) ks))]
              (if (= kind :set)
                `(lackso ~sym ~@shown)
                `(lacks-keyo ~sym ~@shown))))))
      IConstraintWatchedStores
      (-watched-stores [_] #{::subst}))
    {::lmap-lacks ks ::lacks-kind kind}))

(defn- lmap-ensure-lacks
  "Constrains the unbound var x to lack the ground keys ks. Keeps a single
   lacks-constraint per var, so a rest that is passed along keeps sharing
   one key set instead of collecting constraints. Takes and returns a
   substitution."
  ([s x ks]
   (lmap-ensure-lacks s x ks nil))
  ([s x ks kind]
   (let [ks (if (set? ks) ks (set ks))
         c (lmap-lacks-constraint s x)
         have (::lmap-lacks (meta c))
         kind (or kind (::lacks-kind (meta c)) :map)]
     (cond
       (nil? c) ((cgoal (-lmap-lacksc x ks kind)) s)
       ;; grow the larger set by the smaller one
       (> (count ks) (count have))
       ((cgoal (-lmap-lacksc x (into ks have) kind)) ((remcg c) s))
       (every? #(contains? have %) ks) s
       :else
       ((cgoal (-lmap-lacksc x (into have ks) kind)) ((remcg c) s))))))

(declare lmap-await)

(defn- lmap-lacks-ground
  "A goal that succeeds if the map x has none of the keys in the set ks,
   which are ground. Never branches. kind is :set if x is a set, nil if
   that is not known."
  [x ks kind]
  (fn [s]
    (when-let [[s g n tail] (coll-parts s x)]
      (when-not (if (< (count g) (count ks))
                  (some #(contains? ks %) (coll-keys g))
                  (some #(contains? g %) ks))
        ;; differ from the keys of x that are not ground
        (when-let [s (reduce (fn [s [k nk]] (or ((!= k nk) s) (reduced nil)))
                             s (for [[nk] n, k ks] [k nk]))]
          (if (and tail (seq ks))
            (let [v (walk s x)
                  kind (cond
                         (or (set? v) (lset? v)) :set
                         (or (map? v) (lmap? v)) :map
                         :else kind)]
              (lmap-ensure-lacks s tail ks kind))
            s))))))

(defn- lmap-lacks
  "A goal that succeeds if the map x has none of the keys ks, or for kind
   :set, the set x has none of the elements ks. Never branches, so it can
   run inside the constraint solver."
  ([x ks] (lmap-lacks x ks nil))
  ([x ks kind]
   (fn [s]
     (let [ks (map #(walk* s %) ks)
           ground (set (filter ground-key? ks))
           nonground (remove ground-key? ks)]
       (if (empty? nonground)
         ((lmap-lacks-ground x ground kind) s)
         (when-let [[s g n tail] (coll-parts s x)]
           (let [goals (concat
                       ;; differ from the keys of x that are not ground
                        (for [k nonground, [nk] n] (!= k nk))
                       ;; and from its ground keys and rest, once ground
                        (when (or (seq g) tail)
                          (for [k nonground]
                            (lmap-await (if (= kind :set) `lackso `lacks-keyo) [x k] k
                                        #(lmap-lacks x [k] kind)))))]
             (when-let [s (reduce (fn [s g] (or (g s) (reduced nil))) s goals)]
               ((lmap-lacks-ground x ground kind) s)))))))))

(defn- lmap-extendo
  "A goal where map x is the entries, whose keys are ground, plus the map r,
   which lacks those keys."
  [x entries r]
  (all
   (lmap-lacks r (keys entries))
   ;; build on what r is bound to, so maps grown step by step stay flat
   ;; instead of becoming chains of rests
   (fn [s] ((== x (lmap* entries (walk s r))) s))))

;; -----------------------------------------------------------------------------
;; Suspension

(defn- lmap-take
  "Up to n answers of the goal result stream x."
  [n x]
  (loop [x x acc []]
    (cond
      (or (nil? x) (clojure.core/== (count acc) n)) acc
      (instance? Choice x) (recur (.f ^Choice x) (conj acc (.a ^Choice x)))
      (fn? x) (recur (x) acc)
      :else (conj acc x))))

(defn- lmap-solve
  "Up to two answers of the goal (retry) on s. Runs it as a goal of its own,
   so that the constraints it triggers are fully propagated, then restores
   what s was in the middle of."
  [s retry]
  (let [vs (:vs s)
        cq (:cq s)]
    (mapv #(-> % (assoc :vs vs) (assoc :cq cq))
          (lmap-take 2 ((retry) (-> s (assoc :vs nil) (assoc :cq nil)))))))

(declare -lmap-relc)

(defn- lmap-pend
  "Adds the relation rel on args as a pending constraint that re-runs the
   goal (retry) when one of the vars in watch-terms is bound. A nil rel is
   hidden from answers. info is kept with the constraint: :force, returning
   the goal that enumerates an ambiguous relation (retry by default), or
   :link and :lin-eq for lengths."
  ([s rel args retry watch-terms ambiguous?]
   (lmap-pend s rel args retry watch-terms ambiguous? nil))
  ([s rel args retry watch-terms ambiguous? info]
   ((cgoal (-lmap-relc rel args retry (term-vars s watch-terms) ambiguous? info)) s)))

(defn- lmap-commit
  "Runs the goal (retry) where branching is not possible: fails if no
   alternative survives, commits if exactly one does, and otherwise keeps
   the relation pending as ambiguous."
  ([s rel args retry]
   (lmap-commit s rel args retry nil))
  ([s rel args retry info]
   (let [answers (lmap-solve s retry)]
     (case (count answers)
       0 nil
       1 (first answers)
       (lmap-pend s rel args retry args true info)))))

(defn- -lmap-relc
  "Constraint for the relation rel on args, suspended until one of the vars
   in watch is bound. retry returns the relation's goal."
  [rel args retry watch ambiguous? info]
  (with-meta
    (reify
      IConstraintStep
      (-step [this s]
        (reify
          clojure.lang.IFn
          (invoke [_ s]
            (when-let [s ((remcg this) s)]
              (lmap-commit s rel args retry info)))
          IRunnable
          (-runnable? [_]
            (boolean
             (if (:pick info)
               ;; also when a watched var is bound to another var, which
               ;; may be the map of another waiting pick of the same key
               (some #(let [w (walk s %)] (or (not (lvar? w)) (not= w %))) watch)
               (some #(not (lvar? (walk s %))) watch))))))
      IConstraintOp
      (-rator [_] rel)
      (-rands [_] watch)
      IReifiableConstraint
      (-reifyc [_ v r a]
        (when rel
          (cons rel (-reify a args r))))
      IConstraintWatchedStores
      (-watched-stores [_] #{::subst}))
    {::lmap-rel (merge {:ambiguous ambiguous? :retry retry :args args} info)}))

(defn- lmap-suspend
  "A goal suspending the relation rel on args until a var in watch-terms is
   bound, then re-running the goal (retry)."
  [rel args retry watch-terms]
  (fn [s]
    (lmap-pend s rel args retry watch-terms false)))

(defn- lmap-await
  "A goal that runs the goal (g) once x is ground, suspending until then."
  [rel args x g]
  (fn [s]
    (if (ground-key? (walk* s x))
      ((g) s)
      ((lmap-suspend rel args #(lmap-await rel args x g) [x]) s))))

(declare len-force-goal)

(defn- lmap-force
  "A goal enumerating the alternatives of ambiguous pending relations, and
   the lengths still tied to other lengths, until none are left. Runs
   before an answer is reified."
  [a]
  (let [info #(::lmap-rel (meta %))]
    (if-let [c (when (pos? (count (:cs a)))
                 (first (filter #(:ambiguous (info %)) (vals (:cm (:cs a))))))]
      ((all
        (remcg c)
        ((or (:force (info c)) (:retry (info c))))
        lmap-force) a)
      (if-let [g (len-force-goal a)]
        ((all g lmap-force) a)
        a))))

(defn- or-goals
  "Disjunction of goals, failing if there are none. Builds each
   alternative only when it is tried, so goals may be long or lazy."
  [goals]
  (if-let [[g & more] (seq goals)]
    (if more
      (conde
       [g]
       [(or-goals more)])
      g)
    fail))

;; -----------------------------------------------------------------------------
;; Picking an entry

(declare absento)

(defn- lmap-pick-wait
  "Waits on the relation rel on args, which says t holds key k with value
   x, until a var in watch-terms is bound. A key has one value, so other
   waiting relations about the same key of the same t give the same value."
  [s t k x rel args retry watch-terms]
  (let [t* (walk s t)
        k' (walk* s k)
        cs (vals (:cm (:cs s)))
        same (for [c cs
                   :let [[t2 k2 x2] (:pick (::lmap-rel (meta c)))]
                   :when (and t2 (= t* (walk s t2)) (= k' (walk* s k2)))]
               x2)
        ;; what is absent from t is absent from its keys and values
        absent (for [c cs
                     :let [[a2 t2] (:absent (::lmap-rel (meta c)))]
                     :when (and t2 (= t* (walk s t2)))]
                 a2)]
    ((all (everyg #(== x %) same)
          (everyg #(all (absento % k) (absento % x)) absent)
          (fn [s]
            ;; tells absento there is a waiting pick to look at
            (lmap-pend (vary-meta s assoc ::picks true)
                       rel args retry watch-terms false {:pick [t k x]})))
     s)))

(defn- lmap-picko
  "A relation where map t is the map t' plus key k with value x, and t'
   lacks k. Enumerates the entries of t if k is not ground. A nil t' means
   the remainder is not wanted, which saves building it. While it waits, it
   reifies as the relation rel on args."
  [t k x t' rel args]
  (fn [s]
    (when-let [[s g n tail] (map-parts s t)]
      (let [k' (walk* s k)
            retry #(lmap-picko t k x t' rel args)
            remainder (fn [k]
                        (if t'
                          (fn [s] ((== t' (map-term-without g n tail k)) s))
                          succeed))]
        (cond
          ;; nothing known about t
          (lvar? (walk s t))
          (if (ground-key? k')
            ((lmap-extendo t {k' x} (or t' (lvar 'rest))) s)
            ;; a key that is not ground fits only into a closed map
            (let [[_ g' n' tail' :as parts'] (map-parts s (or t' (lvar 'rest)))]
              (cond
                (nil? parts') nil
                (nil? tail') ((all (lmap-lacks t' [k'])
                                   (== t (assoc (map-term g' n' nil) k' x)))
                              s)
                ;; a map can't hold a value that holds the map
                (contains? (recover-vars-from-term (walk* s x)) (walk s t)) nil
                :else (lmap-pick-wait s t k x rel args retry [t k t' x]))))

          (and (ground-key? k') (contains? g k'))
          ((all (== x (get g k'))
                (remainder k'))
           s)

          :else
          ((or-goals
            (concat
             ;; one of the known entries
             (for [[ek ev] (concat (if (ground-key? k') [] g) n)]
               (all (== k ek)
                    (== x ev)
                    (remainder ek)))
             ;; or an entry of the unknown rest
             (when tail
               [(fresh [tail']
                       (everyg #(!= k %) (if (ground-key? k') [] (keys g)))
                       (lmap-picko tail k x (when t' tail') rel args)
                       (if t' (lmap-extendo t' g tail') succeed))])))
           s))))))

(defn- lmap-pick-each
  "A relation where map m is the entries es (pairs, keys distinct) plus the
   map rest, which lacks their keys. Picks one entry at a time."
  [es rest m rel args]
  (if-let [[[k x] & more] (seq es)]
    (fresh [m']
           (lmap-picko m k x m' rel args)
           (lmap-pick-each more rest m' rel args))
    (== m rest)))

(defn- lmap-take-ground
  "A relation where map m is the entries g, whose keys are ground, plus the
   map m', which lacks their keys. Takes them in one pass where it can."
  [m g m' rel args]
  (fn [s]
    (if (empty? g)
      ((== m m') s)
      (when-let [[s gm nm tail] (map-parts s m)]
        (if (lvar? (walk s m))
          ((lmap-extendo m g m') s)
          (let [present (filter #(contains? gm (key %)) g)
                missing (into {} (remove #(contains? gm (key %)) g))
                left (map-term (apply dissoc gm (map key present)) nm tail)]
            ((all
              (== (mapv val present) (mapv #(get gm (key %)) present))
              (cond
                (empty? missing) (== m' left)
                ;; may be under a key of m that is not ground yet
                (seq nm) (lmap-pick-each (seq missing) m' left rel args)
                tail (fresh [tail']
                            (lmap-extendo tail missing tail')
                            (lmap-extendo m' (apply dissoc gm (map key present)) tail'))
                :else fail))
             s)))))))

(defn- lmap-matcho
  "A relation where map m is the entries es (pairs, keys distinct) plus the
   map rest, which lacks their keys."
  [es rest m rel args]
  (let [ground (into {} (filter (comp ground-key? first) es))
        nonground (remove (comp ground-key? first) es)]
    (fresh [m']
           (lmap-take-ground m ground m' rel args)
           (lmap-pick-each nonground rest m' rel args))))

(defn- walk-keys
  "The entries of map es, with their keys walked."
  [s es]
  (map (fn [[k v]] [(walk* s k) v]) es))

;; -----------------------------------------------------------------------------
;; Unification

(defn- unify-map-parts
  "Unifies two maps given as ground entries and tails."
  [gu tu gv tv s]
  (when-let [s (reduce (fn [s [k x]]
                         (if (contains? gv k)
                           (or (unify s x (get gv k)) (reduced nil))
                           s))
                       s gu)]
    (let [only-u (apply dissoc gu (keys gv))
          only-v (apply dissoc gv (keys gu))]
      (cond
        (and (nil? tu) (nil? tv))
        (when (and (empty? only-u) (empty? only-v)) s)

        (nil? tu)
        (when (empty? only-v) (unify s tv only-u))

        (nil? tv)
        (when (empty? only-u) (unify s tu only-v))

        ;; same rest on both sides: the known keys must be the same too
        (= tu tv)
        (when (and (empty? only-u) (empty? only-v)) s)

        ;; each rest holds the other side's extra entries plus a shared rest
        :else
        (let [r (lvar 'rest)]
          (when-let [s (lmap-ensure-lacks s r (into (set (keys gu)) (keys gv)))]
            (when-let [s (unify s tu (lmap* only-v r))]
              (unify s tv (lmap* only-u r)))))))))

(defn- map-unifyo
  "A relation where the map terms u and v are equal, for maps whose keys
   are not all ground."
  [u v]
  (fn [s]
    (when-let [[s g n tail] (map-parts s u)]
      ((lmap-matcho (concat g n) (or tail {}) v `== [u v]) s))))

(defn unify-map-terms
  "Unifies two map terms (plain maps or LMaps). If not all keys are ground,
   the unification branches over which keys pair up."
  [u v s]
  (when-let [[s gu nu tu] (map-parts s u)]
    (when-let [[s gv nv tv] (map-parts s v)]
      (if (or (seq nu) (seq nv))
        (lmap-commit s `== [u v] #(map-unifyo u v))
        (unify-map-parts gu tu gv tv s)))))

(defn- pmap-matcho
  "A relation where map v has all the entries of the partial map u, whose
   map values are partial too."
  [u v]
  (everyg (fn [[k x]]
            (fresh [y]
                   (geto v k y)
                   (if (map? x) (featurec y x) (== x y))))
          (seq u)))

(defn- unify-pmap-relational
  "Unifies the partial map u with the map term v, branching over which keys
   pair up."
  [u v s]
  (lmap-commit s `featurec [v (into {} u)] #(pmap-matcho u v)))

(defn- unify-pmap-with-lmap
  "Unifies the partial map u with the LMap v: v must have all keys of u,
   with unifying values."
  [u v s]
  (when-let [[s g n tail] (map-parts s v)]
    (if (or (seq n) (not (every? atomic-key? (keys u))))
      (unify-pmap-relational u v s)
      (let [missing (remove #(contains? g %) (keys u))]
        (when-let [s (cond
                       (empty? missing) s
                       tail (let [r (lvar 'rest)
                                  added (zipmap missing (repeatedly #(lvar 'v)))]
                              (when-let [s (lmap-ensure-lacks s r (into (set (keys g)) missing))]
                                (unify s tail (lmap* added r))))
                       :else nil)]
          (when-let [[s g] (map-parts s v)]
            (unify-with-pmap* u g s)))))))

(extend-protocol IDisunifyTerms
  LMap
  (-disunify-terms [u v s cs]
    ;; keep the whole pair in the prefix rather than decomposing it, since
    ;; unifying open maps introduces fresh vars; the != constraint rechecks
    ;; the pair whenever one of its vars is bound
    (when (and (or (map? v) (lmap? v)) (unify s u v))
      (assoc cs :prefixc (assoc (:prefixc cs) u v)))))

;; -----------------------------------------------------------------------------
;; Relations

(defn lmapo
  "A relation where map m consists of the entries of the map entries plus
   the map rest, which has none of their keys. The keys of entries may be
   unbound. (lmapo m {:a x} r) takes m apart into the value at :a and the
   rest of m, or builds m from them."
  [m entries rest]
  (fn [s]
    (let [entries' (walk s entries)]
      (cond
        (map? entries')
        ((lmap-matcho (walk-keys s entries') rest m `lmapo [m entries rest]) s)

        ;; wait until the entries are known
        (or (lvar? entries') (lmap? entries'))
        ((lmap-suspend `lmapo [m entries rest] #(lmapo m entries rest) [entries]) s)

        :else nil))))

(defn lacks-keyo
  "A relation where map m has none of the keys ks."
  [m & ks]
  (lmap-lacks m ks))

(declare coll-kind index? seq-splito seq-assoco)

(defn- key-kind
  "The kind of collection the key k' alone says a collection must be, see
   coll-kind: a key that is not an index can only be in a map; :either for
   an index."
  [k']
  (cond
    (lvar? k') nil
    (index? k') :either
    :else :map))

(defn geto
  "A relation where m contains key k with value v, i.e. (get m k) is v.
   m is a map, or a sequence and k an index. Enumerates the entries of m if
   k is unbound."
  [m k v]
  (fn [s]
    (let [k' (walk* s k)
          m' (walk s m)]
      (cond
        (and (map? m') (atomic-key? k') (contains? m' k'))
        ;; the key itself is in the map, so no other key can be it
        ((== v (get m' k')) s)

        (and (vector? m') (index? k'))
        (when (< k' (count m'))
          ((== v (nth m' k')) s))

        :else
        (let [args [m k v]
              as-map #(lmap-picko m k v nil `geto args)
              as-seq #(seq-splito m k nil v nil `geto args)]
          (case (or (coll-kind s m') (key-kind k'))
            :map ((as-map) s)
            :seq (when (or (lvar? k') (index? k')) ((as-seq) s))
            (:other :set) nil
            :either (lmap-pend s `geto args #(geto m k v) [m k] true
                               {:force #(conde [(as-map)] [(as-seq)])})
            (lmap-pick-wait s m k v `geto args #(geto m k v) [m k])))))))

(defn dissoco
  "A relation where out is (dissoc m k)."
  [m k out]
  (conde
   [(fresh [x] (lmap-picko m k x out `dissoco [m k out]))]
   [(lacks-keyo m k) (== m out)]))

(defn- map-assoco [m k v out]
  (fresh [m']
         (dissoco m k m')
         (lmap-picko out k v m' `assoco [m k v out])))

(defn assoco
  "A relation where out is (assoc m k v). m is a map, or a sequence and k
   an index up to its length."
  [m k v out]
  (fn [s]
    (let [k' (walk* s k)
          args [m k v out]]
      (case (or (coll-kind s m) (coll-kind s out) (key-kind k'))
        :map ((map-assoco m k v out) s)
        :seq (when (or (lvar? k') (index? k')) ((seq-assoco m k v out) s))
        (:other :set) nil
        :either (lmap-pend s `assoco args #(assoco m k v out) [m k out] true
                           {:force #(conde [(map-assoco m k v out)]
                                           [(seq-assoco m k v out)])})
        ((lmap-suspend `assoco args #(assoco m k v out) [m k out]) s)))))

(defn- lmap-assoc-all
  "A relation where out is m with all entries es assoc'ed."
  [m es out]
  (if-let [[[k v] & more] (seq es)]
    (fresh [m']
           (assoco m k v m')
           (lmap-assoc-all m' more out))
    (== m out)))

(defn- lmap-merge-into
  "A relation where out is (merge es m), es being entries with distinct keys."
  [es m out rel args]
  (if-let [[[k v] & more] (seq es)]
    (conde
     [(fresh [x] (geto m k x)) (lmap-merge-into more m out rel args)]
     [(lacks-keyo m k)
      (fresh [out']
             (lmap-merge-into more m out' rel args)
             (lmap-picko out k v out' rel args))])
    (== m out)))

(defn- lmap-submapo
  "A relation where the closed map m consists of some of the entries es."
  [m es rel args]
  (if-let [[[k v] & more] (seq es)]
    (conde
     [(fresh [r] (lmap-picko m k v r rel args) (lmap-submapo r more rel args))]
     [(lacks-keyo m k) (lmap-submapo m more rel args)])
    (== m {})))

(defn mergeo
  "A relation where out is (merge m1 m2). Branches once m2, m1 or out is
   closed, and waits otherwise."
  [m1 m2 out]
  (fn [s]
    (let [args [m1 m2 out]]
      (when-let [[s g2 n2 t2] (map-parts s m2)]
        (if (nil? t2)
          (let [[_ g1 n1 t1] (map-parts s m1)]
            (if (and (nil? t1) (empty? n1) (empty? n2) (map? (walk s m1)))
              ;; both closed with ground keys: just merge
              ((== out (merge g1 g2)) s)
              ((lmap-assoc-all m1 (concat g2 n2) out) s)))
          (when-let [[s g1 n1 t1] (map-parts s m1)]
            (if (nil? t1)
              ((lmap-merge-into (concat g1 n1) m2 out `mergeo args) s)
              (when-let [[s go no to] (map-parts s out)]
                (if (nil? to)
                  ;; m2 is a submap of out; closing it lets mergeo proceed
                  ((all (lmap-submapo m2 (concat go no) `mergeo args)
                        (mergeo m1 m2 out))
                   s)
                  ((lmap-suspend `mergeo args #(mergeo m1 m2 out) args) s))))))))))

(defn- lmap-list
  "The elements of l if it is a proper list, else nil."
  [s l]
  (loop [l (walk s l) acc []]
    (cond
      (or (nil? l) (and (sequential? l) (empty? l))) acc
      (lcons? l) (recur (walk s (lnext l)) (conj acc (lfirst l)))
      (sequential? l) (into acc l)
      :else nil)))

(defn- lmap-permutationo
  "A relation where the proper list ys holds the elements of the list xs in
   some order. Compares directly when both are ground, and otherwise removes
   the elements of ys from xs one at a time, so it only branches where an
   element is not ground yet."
  [s xs ys]
  (let [xs' (map #(walk* s %) xs)
        ys' (map #(walk* s %) ys)]
    (cond
      (not (clojure.core/== (count xs') (count ys'))) fail
      (and (every? ground-key? xs') (every? ground-key? ys'))
      (if (= (frequencies xs') (frequencies ys')) succeed fail)
      :else
      ((fn remove-each [xs ys]
         (if-let [[y & more] (seq ys)]
           (fresh [xs*]
                  (rembero y xs xs*)
                  (remove-each xs* more))
           (== xs ())))
       (or (seq xs) ()) ys))))

(declare set-elems)

(defn keyso
  "A relation where ks is the set of the keys of map m. A set, not a seq:
   the keys of a map have no order, so (keyso {:a 1 :b 2} ks) has one
   answer, #{:a :b}. ks given as a vector or list fails, as (= #{:a} [:a])
   is false."
  [m ks]
  (fn [s]
    (when-let [[s g n tail] (map-parts s m)]
      (if (nil? tail)
        ((== ks (into (set (keys g)) (map first n))) s)
        (let [ks' (walk s ks)]
          (cond
            (set? ks')
            (when-let [[s kl] (set-elems s ks)]
              ((lmapo m (zipmap kl (repeatedly #(lvar 'v))) {}) s))

            ;; wait until the map or the key set is closed
            (or (lvar? ks') (lset? ks'))
            ((lmap-suspend `keyso [m ks] #(keyso m ks) [m ks]) s)

            :else nil))))))

(defn- lmap-remove-each
  "A relation where the list l without one occurrence of each of xs is out."
  [xs l out]
  (if-let [[x & more] (seq xs)]
    (fresh [l']
           (rembero x l l')
           (lmap-remove-each more l' out))
    (== l out)))

(defn valso
  "A relation where vs is a list of the values of map m, in any order.
   Lists every ordering if vs is unbound."
  [m vs]
  (fn [s]
    (when-let [[s g n tail] (map-parts s m)]
      (if (nil? tail)
        (let [all-vals (concat (vals g) (map second n))]
          (if-let [vl (lmap-list s vs)]
            ((lmap-permutationo s all-vals vl) s)
            ((permuteo (or (seq all-vals) ()) vs) s)))
        (if-let [vl (lmap-list s vs)]
          (let [unknown (- (count vl) (count g))
                xs (vec (repeatedly unknown #(lvar 'v)))]
            ;; the rest holds the values left over, under keys that are not
            ;; known, so taking them in the order of vs loses no answer
            (when-not (neg? unknown)
              ((all (lmap-remove-each (vals g) vs xs)
                    (lmapo tail (zipmap (repeatedly unknown #(lvar 'k)) xs) {}))
               s)))
          ((lmap-suspend `valso [m vs] #(valso m vs) [m vs]) s))))))

(defn- lmap-select
  "A relation where out is (select-keys m ks); seen are the keys already
   selected."
  [m ks seen out rel args]
  (if-let [[k & more] (seq ks)]
    (conde
     ;; the same key again selects nothing new
     [(membero k seen) (lmap-select m more seen out rel args)]
     [(everyg #(!= k %) seen)
      (conde
       [(fresh [x out']
               (geto m k x)
               (lmap-picko out k x out' rel args)
               (lmap-select m more (conj seen k) out' rel args))]
       [(lacks-keyo m k)
        (lmap-select m more (conj seen k) out rel args)])])
    (== out {})))

(defn- lmap-covering-keys
  "A relation where ks is a list holding each of the keys missing at least
   once, any of the keys of out again, and any keys m lacks, in any order."
  [m out-keys missing ks]
  (conde
   [(== ks ()) (if (empty? missing) succeed fail)]
   [(fresh [k more]
           (== ks (lcons k more))
           (conde
            [(membero k out-keys)
             (fn [s]
               (let [k (walk* s k)]
                 ((lmap-covering-keys m out-keys (remove #(= k %) missing) more) s)))]
            [(lacks-keyo m k)
             (lmap-covering-keys m out-keys missing more)]))]))

(defn selectso
  "A relation where out is (select-keys m ks). If ks is unbound, lists every
   key list that selects out from m: the keys of out in any order and
   repeated, mixed with any keys m lacks. There are infinitely many, so use
   run n rather than run* then."
  [m ks out]
  (fn [s]
    (let [args [m ks out]]
      (if-let [kl (lmap-list s ks)]
        ((lmap-select m kl [] out `selectso args) s)
        (let [[_ _ _ tm :as pm] (map-parts s m)
              [_ go no to :as po] (map-parts s out)]
          (cond
            (or (nil? pm) (nil? po)) nil
            (and (nil? tm) (nil? to))
            (let [out-entries (concat go no)
                  out-keys (map first out-entries)]
              ((all
                (everyg (fn [[k x]] (geto m k x)) out-entries)
                (lmap-covering-keys m out-keys out-keys ks))
               s))
            :else ((lmap-suspend `selectso args #(selectso m ks out) args) s)))))))

;; =============================================================================
;; LVec - Relational Vectors
;;
;; Sequences are relational like maps. A sequence that is only partly known
;; is an LVec: known elements at the front, an unknown middle, a logic var
;; standing for a sequence of any length, and known elements at the back.
;; Vectors, lists and partial lists (lcons) are sequences too, and all of
;; them unify with each other, as they are = in Clojure. LVecs are built by
;; the relations below and by unification, and appear in answers as
;; (lvec [front] | middle | [back]).
;;
;; Every middle has a length: a logic var, linked to the middle by a hidden
;; constraint created when the length is first needed (see mid-len). Lengths
;; are natural numbers, related by linear equations that are solved exactly
;; as soon as they are posted (see len==), so that sequences whose lengths
;; cannot match fail without enumerating anything. When the length of a
;; middle becomes known, the middle becomes a vector of that many fresh
;; vars. Before an answer is reified, every length still tied to other
;; lengths is enumerated (see len-force-goal); a middle whose length is tied
;; to nothing stays open in the answer.

;; -----------------------------------------------------------------------------
;; Lengths

(declare ->lin lin-plus lin-scale len==)

(deftype Lin [terms const]
  ;; terms maps each var to its nonzero coefficient
  ITreeTerm

  Object
  (toString [_]
    (str "(lin " terms " " const ")"))
  (equals [this o]
    (and (instance? Lin o)
         (= terms (.terms ^Lin o))
         (= const (.const ^Lin o))))
  (hashCode [_]
    (clojure.lang.Util/hash [terms const]))

  IUnifyTerms
  (unify-terms [u v s]
    (len== s u v))

  IWalkTerm
  (walk-term [v f]
    (reduce (fn [acc [x c]]
              (lin-plus acc (lin-scale (->lin (walk-term (f x) f)) c)))
            (Lin. {} const) terms))

  IOccursCheckTerm
  (occurs-check-term [v x s]
    (boolean (some #(occurs-check s x %) (keys terms))))

  IReifyTerm
  (reify-term [v s]
    (reduce -reify* s (keys terms)))

  IBuildTerm
  (build-term [u s]
    (reduce build s (keys terms))))

(defmethod print-method Lin [x ^Writer writer]
  (.write writer (str x)))

(defn- ->lin
  "The linear expression for a natural number, a var or an expression."
  [x]
  (cond
    (instance? Lin x) x
    (lvar? x) (Lin. {x 1} 0)
    (integer? x) (Lin. {} (long x))
    :else nil))

(defn- lin-terms [^Lin l] (.terms l))

(defn- lin-const [^Lin l] (.const l))

(defn- lin-plus [^Lin a ^Lin b]
  (Lin. (reduce (fn [ts [x c]]
                  (let [c (+ (get ts x 0) c)]
                    (if (zero? c) (dissoc ts x) (assoc ts x c))))
                (.terms a) (.terms b))
        (+ (.const a) (.const b))))

(defn- lin-scale [^Lin a k]
  (if (zero? k)
    (Lin. {} 0)
    (Lin. (into {} (map (fn [[x c]] [x (* c k)])) (.terms a))
          (* (.const a) k))))

(defn- lin-walk
  "The linear expression x denotes in s, over unbound vars only."
  [s x]
  (->lin (walk* s x)))

(defn- lin-bound
  "The upper bound on the var y implied by l >= 0 over the naturals, or nil."
  [l y]
  (let [ts (lin-terms l)
        a (get ts y)]
    (when (and a (neg? a) (not-any? pos? (vals ts)))
      (quot (lin-const l) (- a)))))

(defn- gcd [a b]
  (if (zero? b) a (recur b (rem a b))))

(defn- updateg
  "A goal applying f to the substitution, then running the constraints on
   the vars f bound, as == does."
  [f]
  (fn [a]
    (when-let [ap (f (assoc a :vs []))]
      (let [vs (:vs ap)]
        (if (seq vs)
          ((run-constraints* vs (:cs ap) ::subst) (assoc ap :vs nil))
          (assoc ap :vs nil))))))

(defn- len==
  "Equates the lengths a and b: naturals, length vars, or linear
   expressions over them. Solves for one var where it can, and keeps the
   equation as a constraint otherwise. Takes and returns a substitution."
  [s a b]
  (let [la (lin-walk s a)
        lb (lin-walk s b)]
    (when (and la lb)
      (let [d (lin-plus la (lin-scale lb -1))
            ts (lin-terms d)
            c (lin-const d)]
        (if (empty? ts)
          (when (zero? c) s)
          (let [g (reduce gcd (map #(Math/abs (long %)) (vals ts)))]
            (when (zero? (rem c g))
              (let [d (if (clojure.core/== g 1)
                        d
                        (Lin. (into {} (map (fn [[x k]] [x (quot k g)])) ts)
                              (quot c g)))
                    ts (lin-terms d)
                    c (lin-const d)
                    signs (set (map pos? (vals ts)))]
                ;; a sum of naturals with one sign never meets a constant of
                ;; the same sign
                (when-not (and (clojure.core/== (count signs) 1)
                               (if (contains? signs true) (pos? c) (neg? c)))
                  (if-let [[x k] (first (filter #(clojure.core/== 1 (Math/abs (long (val %)))) ts))]
                    ;; k x + rest = 0, so x = -k rest
                    (let [e (lin-scale (Lin. (dissoc ts x) c) (- k))]
                      (if (empty? (lin-terms e))
                        (when-not (neg? (lin-const e))
                          (ext s x (lin-const e)))
                        (ext s x e)))
                    (lmap-pend s nil [d] #(updateg (fn [s] (len== s d 0))) [d] false
                               {:lin-eq d})))))))))))

(defn- len=g
  "A goal equating the lengths a and b."
  [a b]
  (updateg #(len== % a b)))

(defn- nat-enumg
  "A goal enumerating (g k), (g (inc k)), ... up to hi, without end if hi
   is nil."
  [g k hi]
  (if (and hi (> k hi))
    fail
    (conde
     [(g k)]
     [(nat-enumg g (inc k) hi)])))

(defn- nat-enum
  "A goal enumerating the naturals from k to hi as values of the length var y."
  [y k hi]
  (nat-enumg #(len=g y %) k hi))

;; -----------------------------------------------------------------------------
;; The LVec term

(declare lvec-join unify-seqs)

(deftype LVec [front mid back ^{:unsynchronized-mutable true :tag int} cache]
  ITreeTerm

  clojure.lang.IObj
  (meta [this] nil)
  (withMeta [this new-meta] this)

  Object
  (toString [this]
    (str "(lvec " front " | " mid " | " back ")"))

  (equals [this o]
    (or (identical? this o)
        (and (instance? LVec o)
             (= front (.front ^LVec o))
             (= mid (.mid ^LVec o))
             (= back (.back ^LVec o)))))

  (hashCode [this]
    (if (clojure.core/== cache -1)
      (do
        (set! cache (int (clojure.lang.Util/hash [front mid back])))
        cache)
      cache))

  IUnifyTerms
  (unify-terms [u v s]
    (unify-seqs u v s))

  IReifyTerm
  (reify-term [v s]
    (reduce -reify* (-reify* (reduce -reify* s front) mid) back))

  IWalkTerm
  (walk-term [v f]
    (lvec-join (mapv #(walk-term (f %) f) front)
               (walk-term (f mid) f)
               (mapv #(walk-term (f %) f) back)))

  IOccursCheckTerm
  (occurs-check-term [v x s]
    (boolean (or (some #(occurs-check s x %) front)
                 (occurs-check s x mid)
                 (some #(occurs-check s x %) back))))

  IBuildTerm
  (build-term [u s]
    (reduce build (build (reduce build s front) mid) back)))

(defmethod print-method LVec [x ^Writer writer]
  (.write writer (str x)))

(defn lvec?
  "Returns true if x is an LVec, a partly known sequence in an answer."
  [x]
  (instance? LVec x))

(defn- lvec-parts
  "The front, middle and back of the LVec v."
  [^LVec v]
  [(.front v) (.mid v) (.back v)])

(defn- lvec*
  "Normal form of the sequence front, then mid, then back: a vector if mid
   is nil, mid itself if there is nothing around it, otherwise an LVec."
  [front mid back]
  (cond
    (nil? mid) (into front back)
    (and (empty? front) (empty? back)) mid
    :else (LVec. front mid back -1)))

(defn- seq-parts*
  "Splits the sequence x into [front mid back], walking with walkf: the
   known elements at the front, the unknown middle (an unbound var, or nil
   if the sequence is closed), and the known elements at the back. An
   unbound x is a sequence with nothing known. Returns nil if x is not a
   sequence."
  [walkf x]
  (loop [x (walkf x) front [] back []]
    (cond
      (lvar? x) [front x back]
      (lvec? x) (recur (walkf (.mid ^LVec x))
                       (if (empty? front) (.front ^LVec x) (into front (.front ^LVec x)))
                       (if (empty? back) (.back ^LVec x) (into (.back ^LVec x) back)))
      (lcons? x) (let [[front t] (loop [x x front front]
                                   (if (lcons? x)
                                     (recur (walkf (lnext x)) (conj front (lfirst x)))
                                     [front x]))]
                   ;; a partial list ending in nil is a proper list
                   (recur (if (nil? t) [] t) front back))
      (sequential? x) [(if (and (vector? x) (empty? front) (empty? back))
                         x
                         (-> front (into x) (into back)))
                       nil []]
      :else nil)))

(defn- seq-parts
  "Walks x in s and splits the sequence it denotes into [front mid back],
   see seq-parts*."
  [s x]
  (seq-parts* #(walk s %) x))

(defn- seq-compress
  "Rebinds the var x, if it holds a sequence spanning more than one LVec,
   to the equal flat sequence, as compress-map does for maps. Takes and
   returns a substitution."
  [s x]
  (if (lvar? x)
    (let [root (root-var s x)
          sm (:s s)
          v (get sm root)]
      (if (and (lvec? v) (not (lvar? (walk s (.mid ^LVec v)))))
        (let [[f m b] (seq-parts s root)]
          (assoc s :s (assoc sm root (lvec* f m b))))
        s))
    s))

(defn- lvec-join
  "The sequence front, then the sequence m, then back."
  [front m back]
  (if-let [[f m' b] (seq-parts* identity m)]
    (lvec* (into front f) m' (into b back))
    (LVec. front m back -1)))

;; -----------------------------------------------------------------------------
;; Lengths of middles

(declare mid-len)

(defn- mid-len-link
  "The length var linked to the middle m, an unbound var, if any."
  [s m]
  (let [cs (:cs s)
        cm (:cm cs)]
    (some (fn [cid]
            (when-let [[_ L] (:link (::lmap-rel (meta (cm cid))))]
              L))
          (get (:km cs) (root-var s m)))))

(defn- seq-len
  "The length of the sequence x as [s l], l a linear expression, or nil if
   x is not a sequence."
  [s x]
  (when-let [[f m b] (seq-parts s x)]
    (let [k (+ (count f) (count b))]
      (if m
        (let [[s L] (mid-len s m)]
          [s (lin-plus (->lin L) (->lin k))])
        [s (->lin k)]))))

(defn- lin-nonneg
  "Checks that l >= 0 can hold over the naturals, and binds its vars to 0
   where only that makes it hold. Returns a substitution or nil."
  [s l]
  (let [ts (lin-terms l)
        c (lin-const l)]
    (cond
      (some pos? (vals ts)) s
      (neg? c) nil
      (zero? c) ((updateg (fn [s]
                            (reduce (fn [s y] (or (len== s y 0) (reduced nil)))
                                    s (keys ts))))
                 s)
      :else s)))

(defn- mid-linkg
  "A goal keeping the middle m and its length L in step: once L is known, m
   is that many fresh vars, and once m is bound, L is its length."
  [m L]
  (fn [s]
    (let [v (walk s m)]
      (if (lvar? v)
        (let [l (lin-walk s L)]
          (cond
            (nil? l) nil

            (empty? (lin-terms l))
            (let [n (lin-const l)]
              (when-not (neg? n)
                ((== m (vec (repeatedly n lvar))) s)))

            :else
            (let [s' (lin-nonneg s l)]
              (cond
                (nil? s') nil
                (identical? s' s) (lmap-pend s nil [m L] #(mid-linkg m L) [m L] false
                                             {:link [m L]})
                :else ((mid-linkg m L) s')))))
        (when-let [[s l] (seq-len s v)]
          ((len=g L l) s))))))

(defn- mid-len
  "The length var of the middle m, an unbound var, as [s L]. Links a new
   one to m if it has none yet."
  [s m]
  (if-let [L (mid-len-link s m)]
    [s L]
    (let [L (lvar 'len)]
      [(lmap-pend s nil [m L] #(mid-linkg m L) [m L] false {:link [m L]}) L])))

(defn- len-exprs
  "The linear expressions that must stay >= 0 in a and still have vars: the
   lengths of open middles that are tied to other lengths, and both sides
   of the length equations that could not be solved yet."
  [a]
  (let [cs (:cs a)]
    (when (pos? (count cs))
      (mapcat (fn [c]
                (let [{[m L] :link eq :lin-eq} (::lmap-rel (meta c))]
                  (cond
                    L (when (and (lvar? (walk a m)) (not (lvar? (walk a L))))
                        (let [l (lin-walk a L)]
                          (when (seq (lin-terms l)) [l])))
                    eq (let [l (lin-walk a eq)]
                         [l (lin-scale l -1)])
                    :else nil)))
              (vals (:cm cs))))))

(defn- len-bound
  "The least upper bound on the var y that the expressions exprs imply."
  [exprs y]
  (reduce (fn [hi l]
            (if-let [b (lin-bound l y)]
              (if hi (min hi b) b)
              hi))
          nil exprs))

(defn- len-force-goal
  "A goal enumerating one length still tied to other lengths in a, or nil
   if there is none. Runs before an answer is reified."
  [a]
  (let [exprs (len-exprs a)]
    (when-let [y (some #(first (keys (lin-terms %))) exprs)]
      (nat-enum y 0 (len-bound exprs y)))))

(defn- len-enumg
  "A goal enumerating the values of the length l in s, through its first var."
  [l]
  (fn [a]
    (let [l (lin-walk a l)]
      (if-let [y (first (keys (lin-terms l)))]
        ((nat-enum y 0 (len-bound (len-exprs a) y)) a)
        a))))

;; -----------------------------------------------------------------------------
;; Unification

(defn- unify-all
  "Unifies the terms of xs and ys pairwise."
  [s xs ys]
  (loop [s s xs (seq xs) ys (seq ys)]
    (if (and s xs)
      (recur (unify s (first xs) (first ys)) (next xs) (next ys))
      s)))

(defn- unify-closed-open
  "Unifies the closed sequence e with the sequence front, then the middle
   m, then back."
  [s e front m back]
  (let [n (count e)
        k (count front)
        j (count back)]
    (when (<= (+ k j) n)
      (some-> s
              (unify-all front (subvec e 0 k))
              (unify-all back (subvec e (- n j)))
              (unify m (subvec e k (- n j)))))))

(defn- overlap-alts
  "A relation where x, then the elements bs, is the elements fs, then y:
   x either covers all of fs or ends within them."
  [x bs fs y]
  (let [nf (count fs)
        nb (count bs)]
    (or-goals
     (cons
      (fresh [z]
             (== x (lvec* fs z []))
             (== y (lvec* [] z bs)))
      (for [i (range nf)
            :let [r (- nf i)]
            :when (<= r nb)]
        (all
         (== x (subvec fs 0 i))
         (== (subvec fs i) (subvec bs 0 r))
         (== y (subvec bs r))))))))

(defn- unify-middles
  "Unifies f1, then m1, then b1 with f2, then m2, then b2, after equal
   elements were taken off both ends: f1 or f2 is empty, and b1 or b2 is."
  [s u v f1 m1 b1 f2 m2 b2]
  (cond
    (= m1 m2)
    (cond
      (and (empty? f1) (empty? b1) (empty? f2) (empty? b2)) s
      (not (clojure.core/== (+ (count f1) (count b1)) (+ (count f2) (count b2)))) nil
      ;; m1 with elements around it equal to itself with others around it: a
      ;; word equation, decided by enumerating the length of m1 at the end
      :else (lmap-pend s `== [u v] #(== u v) [u v] true
                       {:force #(fresh []
                                       (fn [a] (when-let [[a l] (seq-len a m1)]
                                                 ((len-enumg l) a)))
                                       (== u v))}))
    (and (empty? f1) (empty? b1)) (unify s m1 (lvec* f2 m2 b2))
    (and (empty? f2) (empty? b2)) (unify s m2 (lvec* f1 m1 b1))
    :else
    ;; x, then bs, is fs, then y
    (let [[x bs fs y] (if (seq f1) [m2 b2 f1 m1] [m1 b1 f2 m2])]
      (when-let [[s lx] (seq-len s x)]
        (when-let [[s ly] (seq-len s y)]
          (when-let [s (len== s (lin-plus lx (->lin (count bs)))
                              (lin-plus ly (->lin (count fs))))]
            (lmap-commit s `== [u v] #(overlap-alts x bs fs y))))))))

(defn- unify-seqs
  "Unifies the sequence terms u and v."
  [u v s]
  (let [pu (seq-parts s u)
        pv (seq-parts s v)]
    (when (and pu pv)
      (let [[f1 m1 b1] pu
            [f2 m2 b2] pv]
        (cond
          (and (nil? m1) (nil? m2))
          (when (clojure.core/== (count f1) (count f2))
            (unify-all s f1 f2))

          (nil? m1) (unify-closed-open s f1 f2 m2 b2)
          (nil? m2) (unify-closed-open s f2 f1 m1 b1)

          :else
          (let [k (min (count f1) (count f2))
                j (min (count b1) (count b2))
                n1 (count b1)
                n2 (count b2)]
            (when-let [s (some-> s
                                 (unify-all (subvec f1 0 k) (subvec f2 0 k))
                                 (unify-all (subvec b1 (- n1 j)) (subvec b2 (- n2 j))))]
              (let [f1 (subvec f1 k)
                    f2 (subvec f2 k)
                    b1 (subvec b1 0 (- n1 j))
                    b2 (subvec b2 0 (- n2 j))]
                (if (or (not (lvar? (walk s m1))) (not (lvar? (walk s m2))))
                  ;; unifying elements bound a middle: start over
                  (unify s (lvec* f1 m1 b1) (lvec* f2 m2 b2))
                  (unify-middles s u v f1 (walk s m1) b1 f2 (walk s m2) b2))))))))))

;; -----------------------------------------------------------------------------
;; Splitting a sequence at a position

(defn- seq-split-at
  "A relation where sequence v is pre, then x, then post, where pre has n
   elements, n a natural. A nil pre or post is not wanted."
  [v n pre x post rel args]
  (fn [s]
    (when-let [[f m b] (seq-parts s v)]
      (let [s (seq-compress s v)
            nf (count f)
            pre-is #(if pre (== pre %) succeed)
            post-is #(if post (== post %) succeed)]
        (cond
          (< n nf)
          ((all (== x (nth f n))
                (pre-is (subvec f 0 n))
                (post-is (lvec* (subvec f (inc n)) m b)))
           s)

          (nil? m) nil

          :else
          (let [j (- n nf)]
            (lmap-commit
             s rel args
             #(or-goals
               (cons
                ;; within the middle
                (fresh [m']
                       (fn [s]
                         (let [ys (vec (repeatedly j lvar))]
                           ((all (== m (lvec* (conj ys x) m' []))
                                 (pre-is (into f ys))
                                 (post-is (lvec* [] m' b)))
                            s))))
                ;; within the back, the middle having j - t elements
                (for [t (range (min (count b) (inc j)))]
                  (fn [s]
                    (let [ys (vec (repeatedly (- j t) lvar))]
                      ((all (== m ys)
                            (== x (nth b t))
                            (pre-is (-> f (into ys) (into (subvec b 0 t))))
                            (post-is (subvec b (inc t))))
                       s)))))))))))))

(defn- seq-split-from
  "seq-split-at for every position i from k on."
  [v i k pre x post rel args]
  (conde
   [(== i k) (seq-split-at v k pre x post rel args)]
   [(seq-split-from v i (inc k) pre x post rel args)]))

(defn- seq-split-enum
  "seq-split-at for every position i of v."
  [v i pre x post rel args]
  (fn [s]
    (when-let [[f m] (seq-parts s v)]
      ((or-goals
        (concat
         (for [n (range (count f))]
           (all (== i n) (seq-split-at v n pre x post rel args)))
         (when m
           [(seq-split-from v i (count f) pre x post rel args)])))
       s))))

(defn- seq-splito
  "A relation where sequence v is pre, then x, then post, where pre has i
   elements. Enumerates i before an answer is reified if it is still
   unbound; an i with a finite domain is labeled instead."
  [v i pre x post rel args]
  (fn [s]
    (let [i' (walk s i)]
      (cond
        (integer? i') (when-not (neg? i')
                        ((seq-split-at v i' pre x post rel args) s))
        ;; positions of a closed sequence are enumerated right away, as the
        ;; entries of a map are
        (and (lvar? i') (not (get-dom-fd s i)) (nil? (second (seq-parts s v))))
        ((seq-split-enum v i pre x post rel args) s)

        (lvar? i') (lmap-pend s rel args #(seq-splito v i pre x post rel args) [v i] true
                              {:force #(fn [a]
                                         (if (get-dom-fd a i)
                                           ((all (force-ans i)
                                                 (seq-splito v i pre x post rel args))
                                            a)
                                           ((seq-split-enum v i pre x post rel args) a)))})
        :else nil))))

;; -----------------------------------------------------------------------------
;; Kinds of collections

(defn- index?
  "True if k is a natural number, i.e. could be an index of a sequence."
  [k]
  (and (integer? k) (not (neg? k))))

(declare type-kind)

(defn- coll-kind
  "Whether x is a map (:map), a sequence (:seq) or something else (:other),
   or nil if that is not known yet."
  [s x]
  (let [x (walk s x)]
    (cond
      (lvar? x) (if-let [c (lmap-lacks-constraint s x)]
                  (::lacks-kind (meta c))
                  (or (type-kind s x)
                      (when (mid-len-link s x) :seq)))
      (or (map? x) (lmap? x)) :map
      (or (set? x) (lset? x)) :set
      (or (sequential? x) (lcons? x) (lvec? x)) :seq
      :else :other)))

(defn- conj-kind
  "Where conj adds to x: at the back of a vector (:vec), the front of a
   list (:list), into a map (:map), or nil if that is not known yet."
  [s x]
  (let [x (walk s x)]
    (cond
      (lvar? x) (when-let [c (lmap-lacks-constraint s x)]
                  (::lacks-kind (meta c)))
      (or (set? x) (lset? x)) :set
      (or (vector? x) (lvec? x)) :vec
      (or (lcons? x) (sequential? x)) :list
      (or (map? x) (lmap? x)) :map
      :else :other)))

;; -----------------------------------------------------------------------------
;; Relations

(defn ntho
  "A relation where (nth v i) is x, for a sequence v. Enumerates the
   positions of x in v if i is unbound."
  [v i x]
  (fn [s]
    (let [v' (walk s v)
          i' (walk s i)]
      (if (and (vector? v') (index? i'))
        (when (< i' (count v'))
          ((== x (nth v' i')) s))
        (case (coll-kind s v')
          (:map :set :other) nil
          ((seq-splito v i nil x nil `ntho [v i x]) s))))))

(defn- seq-counto [c n]
  (fn [s]
    (when-let [[s l] (seq-len s c)]
      (let [n' (walk s n)]
        (cond
          (integer? n') ((len=g l n') s)

          (lvar? n')
          (if (empty? (lin-terms (lin-walk s l)))
            ((== n (lin-const (lin-walk s l))) s)
            (lmap-pend s `counto [c n] #(seq-counto c n) [c n] true
                       {:force #(fn [a]
                                  (if (get-dom-fd a n)
                                    ((all (force-ans n) (seq-counto c n)) a)
                                    ((all (len-enumg l) (seq-counto c n)) a)))}))

          :else nil)))))

(declare counto set-counto set-conjo)

(defn- map-counto [c n]
  (fn [s]
    (when-let [[s g nn tail] (map-parts s c)]
      (let [k (+ (count g) (count nn))
            n' (walk s n)]
        (cond
          (nil? tail) ((== n k) s)
          (integer? n') (cond
                          (< n' k) nil
                          (clojure.core/== n' k) ((== tail {}) s)
                          :else ((lmap-suspend `counto [c n] #(counto c n) [c n]) s))
          :else ((lmap-suspend `counto [c n] #(counto c n) [c n]) s))))))

(defn counto
  "A relation where (count c) is n, for a map or sequence c. Enumerates the
   lengths of c if n is unbound and c is a sequence."
  [c n]
  (fn [s]
    (case (coll-kind s c)
      :seq ((seq-counto c n) s)
      :map ((map-counto c n) s)
      :set ((set-counto c n) s)
      :other nil
      ((lmap-suspend `counto [c n] #(counto c n) [c]) s))))

(defn- seq-conjo
  "A relation where out is the sequence v with x added at the back."
  [v x out]
  (fn [s]
    (when-let [[f m b] (seq-parts s v)]
      ((== out (if m (lvec* f m (conj b x)) (conj f x))) s))))

(defn- seq-popo
  "A relation where sequence v is out with x added at the back."
  [v out x rel args]
  (fn [s]
    (when-let [[f m b] (seq-parts s v)]
      (cond
        (seq b) ((all (== x (peek b)) (== out (lvec* f m (pop b)))) s)
        (nil? m) (when (seq f)
                   ((all (== x (peek f)) (== out (pop f))) s))
        :else (lmap-commit
               s rel args
               #(or-goals
                 [(fresh [m']
                         (== m (lvec* [] m' [x]))
                         (== out (lvec* f m' [])))
                  (if (seq f)
                    (all (== m []) (== x (peek f)) (== out (pop f)))
                    fail)]))))))

(defn conjo
  "A relation where out is (conj c x ...): c with each x added at the back
   of a vector, at the front of a list, or, x being a pair [k v], into a
   map. The last argument is out."
  ([c x out]
   (fn [s]
     (case (or (conj-kind s c) (conj-kind s out))
       :vec ((seq-conjo c x out) s)
       :list ((== out (lcons x c)) s)
       :map ((fresh [k v] (== x [k v]) (assoco c k v out)) s)
       :set ((set-conjo c x out) s)
       :other nil
       ((lmap-suspend `conjo [c x out] #(conjo c x out) [c out]) s))))
  ([c x y & more]
   (fresh [c']
          (conjo c x c')
          (apply conjo c' y more))))

(defn peeko
  "A relation where (peek c) is x: the last element of a vector, or the
   first of a list."
  [c x]
  (fn [s]
    (case (conj-kind s c)
      :vec ((fresh [out] (seq-popo c out x `peeko [c x])) s)
      :list ((fresh [d] (== c (lcons x d))) s)
      (:map :set :other) nil
      ((lmap-suspend `peeko [c x] #(peeko c x) [c]) s))))

(defn popo
  "A relation where out is (pop c): a vector without its last element, or
   a list without its first."
  [c out]
  (fn [s]
    (case (or (conj-kind s c) (conj-kind s out))
      :vec ((fresh [x] (seq-popo c out x `popo [c out])) s)
      :list ((fresh [x] (== c (lcons x out))) s)
      (:map :set :other) nil
      ((lmap-suspend `popo [c out] #(popo c out) [c out]) s))))

(defn concato
  "A relation where out is the sequence of the elements of sequence a,
   then those of sequence b."
  [a b out]
  (fn [s]
    (let [pa (seq-parts s a)
          pb (seq-parts s b)
          po (seq-parts s out)]
      (when (and pa pb po)
        (let [[fa ma ba] pa
              [fb mb bb] pb
              [fo mo] po]
          (cond
            (nil? ma) ((== out (lvec* (into fa fb) mb bb)) s)
            (nil? mb) ((== out (lvec* fa ma (into ba fb))) s)

            ;; out is closed: a ends at one of its positions
            (nil? mo)
            (lmap-commit s `concato [a b out]
                         #(or-goals
                           (for [p (range (inc (count fo)))]
                             (all (== a (subvec fo 0 p))
                                  (== b (subvec fo p))))))

            ;; both a and b are open: out is the front of a, then a middle
            ;; as long as the rest of both, then the back of b
            :else
            ((fresh [mid]
                    (== out (lvec* fa mid bb))
                    (fn [s]
                      (when-let [[s lm] (seq-len s mid)]
                        (when-let [[s la] (seq-len s ma)]
                          (when-let [[s lb] (seq-len s mb)]
                            ((len=g lm (lin-plus (lin-plus la lb)
                                                 (->lin (+ (count ba) (count fb)))))
                             s)))))
                    ;; wake when one of the unknown middles is bound
                    (lmap-suspend `concato [a b out] #(concato a b out) [ma mb mid]))
             s)))))))

(defn subveco
  "A relation where out is (subvec v start end)."
  [v start end out]
  (fresh [pre post tail upto]
         (concato pre tail v)
         (concato out post tail)
         (concato pre out upto)
         (counto pre start)
         (counto upto end)))

(defn- seq-assoco
  "assoco on sequences: replaces the element at index i, or adds x at the
   back if i is the length of m."
  [m i x out]
  (conde
   [(fresh [pre y post]
           (seq-splito m i pre y post `assoco [m i x out])
           (concato pre (lcons x post) out))]
   [(counto m i)
    (seq-conjo m x out)]))

;; -----------------------------------------------------------------------------
;; Paths

(defn- missingo
  "A relation where m, a map or sequence, has no entry at key k: a map
   lacks k, or k is the length of the sequence, the one index assoc can add."
  [m k]
  (fn [s]
    (let [k' (walk* s k)]
      (case (or (coll-kind s m) (key-kind k'))
        :map ((lacks-keyo m k) s)
        :seq ((counto m k) s)
        (:other :set) nil
        :either (lmap-pend s `missingo [m k] #(missingo m k) [m k] true
                           {:force #(conde [(lacks-keyo m k)] [(counto m k)])})
        ((lmap-suspend `missingo [m k] #(missingo m k) [m k]) s)))))

(defn get-ino
  "A relation where (get-in m ks) is v and the path ks exists in m, through
   maps and sequences. Enumerates the paths to v if ks is unbound."
  [m ks v]
  (conde
   [(== ks []) (== m v)]
   [(fresh [k more x]
           (conso k more ks)
           (geto m k x)
           (get-ino x more v))]))

(defn assoc-ino
  "A relation where out is (assoc-in m ks v), through maps and sequences.
   Like assoc-in, missing levels are created as maps, and nil counts as
   an empty map."
  [m ks v out]
  (fresh [k more m']
         (conso k more ks)
         (conde
          [(== m nil) (== m' {})]
          [(!= m nil) (== m' m)])
         (conde
          [(== more []) (assoco m' k v out)]
          [(fresh [k2 more2 x x']
                  (conso k2 more2 more)
                  ;; relating this level first lets a known out bound the descent
                  (assoco m' k x' out)
                  (conde
                   [(geto m' k x)]
                   [(missingo m' k) (== x nil)])
                  (assoc-ino x more v x'))])))

;; =============================================================================
;; LSet - Relational Sets
;;
;; Sets are relational like maps, and work much like maps whose keys are
;; their elements. Elements of a set term are pairwise distinct, so #{x y}
;; denotes a set of two elements and fails once x and y become equal, and
;; unifying sets whose elements are not all ground branches over which
;; elements pair up. An LSet is an open set: known elements plus a rest, a
;; logic var standing for the set of all other elements. Like the keys of an
;; LMap, the elements of an LSet are always ground; a set whose elements are
;; not is always closed. LSets appear in answers as (lset #{elements} | rest).

(declare unify-set-terms lset*)

(deftype LSet [elems rest ^{:unsynchronized-mutable true :tag int} cache]
  ITreeTerm

  clojure.lang.IObj
  (meta [this] nil)
  (withMeta [this new-meta] this)

  Object
  (toString [this]
    (str "(lset " elems " | " rest ")"))

  (equals [this o]
    (or (identical? this o)
        (and (instance? LSet o)
             (= elems (.elems ^LSet o))
             (= rest (.rest ^LSet o)))))

  (hashCode [this]
    (if (clojure.core/== cache -1)
      (do
        (set! cache (int (clojure.lang.Util/hash [elems rest])))
        cache)
      cache))

  IUnifyTerms
  (unify-terms [u v s]
    (when (or (set? v) (instance? LSet v))
      (unify-set-terms u v s)))

  IReifyTerm
  (reify-term [v s]
    (-reify* (reduce -reify* s elems) rest))

  IWalkTerm
  (walk-term [v f]
    (let [es (into #{} (map #(walk-term (f %) f)) elems)
          r (walk-term (f rest) f)]
      ;; a rest repeating a known element denotes no set
      (when (and (set? r) (some #(contains? es %) r))
        (map-keys-collided!))
      (lset* es r)))

  IOccursCheckTerm
  (occurs-check-term [v x s]
    (boolean (or (some #(occurs-check s x %) elems)
                 (occurs-check s x rest))))

  IBuildTerm
  (build-term [u s]
    (build (reduce build s elems) rest)))

(defmethod print-method LSet [x ^Writer writer]
  (.write writer (str x)))

(defn lset?
  "Returns true if x is an LSet, an open set in an answer."
  [x]
  (instance? LSet x))

(defn lset-elems
  "Returns the known elements of an LSet, or the set itself if not an LSet."
  [x]
  (if (lset? x) (.elems ^LSet x) x))

(defn lset-rest
  "Returns the rest (unknown elements) of an LSet, or nil."
  [x]
  (if (lset? x) (.rest ^LSet x) nil))

(defn- lset*
  "Normal form of the set with the given elements and rest: a plain set if
   rest is nil or a set, the rest itself if there are no elements,
   otherwise an LSet whose rest is not itself a set."
  [elems rest]
  (cond
    (nil? rest) elems
    (set? rest) (into elems rest)
    (lset? rest) (lset* (into elems (.elems ^LSet rest)) (.rest ^LSet rest))
    (and (empty? elems) (lvar? rest)) rest
    :else (LSet. elems rest -1)))

(defn- set-parts
  "Walks x in s and splits the set it denotes into [s ground nonground
   tail], as map-parts does for maps: the ground elements (a set), the
   elements that are not ground yet (a vector of pairs [e e], as keys
   mapped to themselves), and the open tail, an unbound var or nil for a
   closed set. Returns nil if x is not a set or two of its elements are
   equal."
  [s x0]
  (letfn [(add-ground [g es]
            ;; disjoint union, without copying either set when possible
            (cond
              (empty? g) es
              (empty? es) g
              (< (count g) (count es))
              (when (not-any? #(contains? es %) g) (into es g))
              :else
              (when (not-any? #(contains? g %) es) (into g es))))]
    (loop [x (walk s x0) g #{} links 0]
      (cond
        (lvar? x) [(if (> links 1) (compress-map s x0 links (lset* g x)) s) g [] x]
        (lset? x) (when-let [g (add-ground g (.elems ^LSet x))]
                    (recur (walk s (.rest ^LSet x)) g (inc links)))
        (set? x) (if (every? atomic-key? x)
                   (when-let [g (add-ground g x)]
                     [(if (> links 1) (compress-map s x0 links g) s) g [] nil])
                   (let [es (map #(walk* s %) x)
                         ground (filter ground-key? es)
                         nonground (vec (remove ground-key? es))
                         g' (set ground)]
                     (when (and (clojure.core/== (count g') (count ground))
                                (apply distinct? nil nonground))
                       (when-let [g (add-ground g g')]
                         (let [n (mapv (fn [e] [e e]) nonground)]
                           (if (and (seq nonground) (> (count x) 1))
                             (when-let [s (ensure-distinct-keys s x)]
                               [s g n nil])
                             [s g n nil]))))))
        :else nil))))

(defn- coll-parts
  "map-parts for maps, set-parts for sets."
  [s x]
  (let [v (walk s x)]
    (if (or (set? v) (lset? v))
      (set-parts s x)
      (map-parts s x))))

(defn- set-term
  "The set term with ground elements g, nonground elements n and tail."
  [g n tail]
  (if (seq n)
    (into g (map first n))
    (lset* g tail)))

(defn- set-term-without
  "The set term [g n tail] without the element e."
  [g n tail e]
  (if (contains? g e)
    (set-term (disj g e) n tail)
    (set-term g (vec (remove #(= e (first %)) n)) tail)))

(defn- set-lacks
  "A goal that succeeds if the set x has none of the elements es."
  [x es]
  (lmap-lacks x es :set))

(defn- set-extendo
  "A goal where set x is the elements es, which are ground, plus the set r,
   which lacks them."
  [x es r]
  (all
   (set-lacks r es)
   (fn [s] ((== x (lset* es (walk s r))) s))))

(defn- set-picko
  "A relation where set t is the set t' plus the element x, and t' lacks x.
   Enumerates the elements of t if x is not ground. A nil t' means the
   remainder is not wanted. While it waits, it reifies as rel on args."
  [t x t' rel args]
  (fn [s]
    (when-let [[s g n tail] (set-parts s t)]
      (let [x' (walk* s x)
            remainder (fn [e]
                        (if t'
                          (fn [s] ((== t' (set-term-without g n tail e)) s))
                          succeed))]
        (cond
          ;; nothing known about t
          (lvar? (walk s t))
          (if (ground-key? x')
            ((set-extendo t #{x'} (or t' (lvar 'rest))) s)
            ;; an element that is not ground fits only into a closed set
            (let [[_ g' n' tail' :as parts'] (set-parts s (or t' (lvar 'rest)))]
              (cond
                (nil? parts') nil
                (nil? tail') ((all (set-lacks t' [x'])
                                   (== t (conj (set-term g' n' nil) x')))
                              s)
                :else ((lmap-suspend rel args #(set-picko t x t' rel args) [t x t']) s))))

          (and (ground-key? x') (contains? g x'))
          ((remainder x') s)

          :else
          ((or-goals
            (concat
             ;; one of the known elements
             (for [e (concat (if (ground-key? x') [] g) (map first n))]
               (all (== x e)
                    (remainder e)))
             ;; or an element of the unknown rest
             (when tail
               [(fresh [tail']
                       (everyg #(!= x %) (if (ground-key? x') [] g))
                       (set-picko tail x (when t' tail') rel args)
                       (if t' (set-extendo t' g tail') succeed))])))
           s))))))

(defn- set-pick-each
  "A relation where set m is the elements es (distinct) plus the set rest,
   which lacks them. Picks one element at a time."
  [es rest m rel args]
  (if-let [[e & more] (seq es)]
    (fresh [m']
           (set-picko m e m' rel args)
           (set-pick-each more rest m' rel args))
    (== m rest)))

(defn- unify-set-parts
  "Unifies two sets given as ground elements and tails."
  [gu tu gv tv s]
  (let [only-u (set (remove #(contains? gv %) gu))
        only-v (set (remove #(contains? gu %) gv))]
    (cond
      (and (nil? tu) (nil? tv))
      (when (and (empty? only-u) (empty? only-v)) s)

      (nil? tu)
      (when (empty? only-v) (unify s tv only-u))

      (nil? tv)
      (when (empty? only-u) (unify s tu only-v))

      ;; same rest on both sides: the known elements must be the same too
      (= tu tv)
      (when (and (empty? only-u) (empty? only-v)) s)

      ;; each rest holds the other side's extra elements plus a shared rest
      :else
      (let [r (lvar 'rest)]
        (when-let [s (lmap-ensure-lacks s r (into gu gv) :set)]
          (when-let [s (unify s tu (lset* only-v r))]
            (unify s tv (lset* only-u r))))))))

(defn- set-unifyo
  "A relation where the set terms u and v are equal, for sets whose
   elements are not all ground."
  [u v]
  (fn [s]
    (when-let [[s g n tail] (set-parts s u)]
      ((set-pick-each (concat g (map first n)) (or tail #{}) v `== [u v]) s))))

(defn unify-set-terms
  "Unifies two set terms (plain sets or LSets). If not all elements are
   ground, the unification branches over which elements pair up."
  [u v s]
  (when-let [[s gu nu tu] (set-parts s u)]
    (when-let [[s gv nv tv] (set-parts s v)]
      (if (or (seq nu) (seq nv))
        (lmap-commit s `== [u v] #(set-unifyo u v))
        (unify-set-parts gu tu gv tv s)))))

(extend-protocol IUnifyTerms
  clojure.lang.IPersistentSet
  (unify-terms [u v s]
    (cond
      (and (set? v) (every? atomic-key? u) (every? atomic-key? v))
      (when (= u v) s)

      (or (set? v) (lset? v)) (unify-set-terms u v s)
      :else nil)))

(extend-protocol IWalkTerm
  clojure.lang.IPersistentSet
  (walk-term [v f]
    (let [r (into (empty v) (map #(walk-term (f %) f)) v)]
      ;; elements that became equal denote no set
      (when-not (clojure.core/== (count r) (count v))
        (map-keys-collided!))
      (with-meta r (meta v)))))

(extend-protocol IOccursCheckTerm
  clojure.lang.IPersistentSet
  (occurs-check-term [v x s]
    (when-not (every? atomic-key? v)
      ;; ext checks the elements of this set once it is bound
      (note-keyed-map v))
    (boolean (some #(occurs-check s x %) v))))

(extend-protocol IDisunifyTerms
  clojure.lang.IPersistentSet
  (-disunify-terms [u v s cs]
    (cond
      (lset? v) (-disunify-terms v u s cs)
      (and (set? v) (every? atomic-key? u) (every? atomic-key? v))
      (when (= u v) cs)
      ;; keep the pair whole, as for maps
      (and (set? v) (unify s u v))
      (assoc cs :prefixc (assoc (:prefixc cs) u v))
      :else nil))

  LSet
  (-disunify-terms [u v s cs]
    (when (and (or (set? v) (lset? v)) (unify s u v))
      (assoc cs :prefixc (assoc (:prefixc cs) u v)))))

;; -----------------------------------------------------------------------------
;; Relations

(defn lseto
  "A relation where set s consists of the elements of the set elems plus
   the set rest, which has none of them. The elements of elems may be
   unbound."
  [s elems rest]
  (fn [a]
    (let [elems' (walk a elems)]
      (cond
        (set? elems')
        (let [es (map #(walk* a %) elems')]
          ((set-pick-each es rest s `lseto [s elems rest]) a))

        ;; wait until the elements are known
        (or (lvar? elems') (lset? elems'))
        ((lmap-suspend `lseto [s elems rest] #(lseto s elems rest) [elems]) a)

        :else nil))))

(defn containso
  "A relation where set s contains x, i.e. (contains? s x). Enumerates the
   elements of s if x is unbound."
  [s x]
  (fn [a]
    (let [s' (walk a s)
          x' (walk* a x)]
      (if (and (set? s') (atomic-key? x') (contains? s' x'))
        a
        ((set-picko s x nil `containso [s x]) a)))))

(defn lackso
  "A relation where set s has none of the elements xs."
  [s & xs]
  (set-lacks s xs))

(defn disjo
  "A relation where out is (disj s x)."
  [s x out]
  (conde
   [(set-picko s x out `disjo [s x out])]
   [(set-lacks s [x]) (== s out)]))

(defn- set-conjo
  "A relation where out is (conj s x) for a set s."
  [s x out]
  (fresh [s']
         (disjo s x s')
         (set-picko out x s' `conjo [s x out])))

(defn- set-elems
  "[a' elems]: the elements of the set x, and a extended with the
   constraint keeping its elements distinct; nil if x is not closed."
  [a x]
  (when-let [[a g n tail] (set-parts a x)]
    (when (nil? tail)
      [a (concat g (map first n))])))

(defn- set-filtero
  "A relation where out is the set of the elements es for which (in? e)
   holds; (out? e) holds for each of the others."
  [es in? out? acc out]
  (if-let [[e & more] (seq es)]
    (conde
     [(in? e) (set-filtero more in? out? (conj acc e) out)]
     [(out? e) (set-filtero more in? out? acc out)])
    (== out (set acc))))

(defn- set-conj-allo
  "A relation where out is the set s with all elements es added."
  [s es out]
  (if-let [[e & more] (seq es)]
    (fresh [s']
           (set-conjo s e s')
           (set-conj-allo s' more out))
    (== s out)))

(defn- set-covero
  "A relation where the sets a and b together hold exactly the elements es:
   each is in a, in b, or in both."
  [es acc-a acc-b a b]
  (if-let [[e & more] (seq es)]
    (conde
     [(set-covero more (conj acc-a e) acc-b a b)]
     [(set-covero more acc-a (conj acc-b e) a b)]
     [(set-covero more (conj acc-a e) (conj acc-b e) a b)])
    (all (== a (set acc-a)) (== b (set acc-b)))))

(defn- plain-set
  "x walked, if it is a set of plain values."
  [s x]
  (let [v (walk s x)]
    (when (and (set? v) (every? atomic-key? v))
      v)))

(defn subseto
  "A relation where set a is a subset of set b. Lists the subsets of b if
   only b is closed."
  [a b]
  (fn [s]
    (if-let [[s es] (set-elems s a)]
      ((everyg #(containso b %) es) s)
      (if-let [[s bs] (set-elems s b)]
        ((set-filtero bs (constantly succeed) (constantly succeed) [] a) s)
        ((lmap-suspend `subseto [a b] #(subseto a b) [a b]) s)))))

(defn disjointo
  "A relation where the sets a and b have no element in common."
  [a b]
  (fn [s]
    (if-let [[s es] (set-elems s a)]
      ((set-lacks b es) s)
      (if-let [[s bs] (set-elems s b)]
        ((set-lacks a bs) s)
        ((lmap-suspend `disjointo [a b] #(disjointo a b) [a b]) s)))))

(defn uniono
  "A relation where out is (clojure.set/union a b). Lists every way to
   split out if only out is closed."
  [a b out]
  (fn [s]
    (if-let [[pa pb] (let [pa (plain-set s a) pb (plain-set s b)] (when (and pa pb) [pa pb]))]
      ((== out (clojure.set/union pa pb)) s)
      (if-let [[s es] (set-elems s a)]
        ((set-conj-allo b es out) s)
        (if-let [[s es] (set-elems s b)]
          ((set-conj-allo a es out) s)
          (if-let [[s es] (set-elems s out)]
            ((set-covero es [] [] a b) s)
            ((lmap-suspend `uniono [a b out] #(uniono a b out) [a b out]) s)))))))

(defn intersectiono
  "A relation where out is (clojure.set/intersection a b)."
  [a b out]
  (fn [s]
    (if-let [[pa pb] (let [pa (plain-set s a) pb (plain-set s b)] (when (and pa pb) [pa pb]))]
      ((== out (clojure.set/intersection pa pb)) s)
      (if-let [[s es] (set-elems s a)]
        ((set-filtero es #(containso b %) #(lackso b %) [] out) s)
        (if-let [[s es] (set-elems s b)]
          ((set-filtero es #(containso a %) #(lackso a %) [] out) s)
          ((lmap-suspend `intersectiono [a b out] #(intersectiono a b out) [a b out]) s))))))

(defn differenceo
  "A relation where out is (clojure.set/difference a b)."
  [a b out]
  (fn [s]
    (if-let [[pa pb] (let [pa (plain-set s a) pb (plain-set s b)] (when (and pa pb) [pa pb]))]
      ((== out (clojure.set/difference pa pb)) s)
      (if-let [[s es] (set-elems s a)]
        ((set-filtero es #(lackso b %) #(containso b %) [] out) s)
        (if-let [[s bs] (set-elems s b)]
        ;; a is out plus the elements of b it has
          ((fresh [c]
                  (disjointo out b)
                  (set-filtero bs (constantly succeed) (constantly succeed) [] c)
                  (uniono c out a))
           s)
          ((lmap-suspend `differenceo [a b out] #(differenceo a b out) [a b out]) s))))))

(defn- set-counto [c n]
  (fn [s]
    (when-let [[s g nn tail] (set-parts s c)]
      (let [k (+ (count g) (count nn))
            n' (walk s n)]
        (cond
          (nil? tail) ((== n k) s)
          (integer? n') (cond
                          (< n' k) nil
                          (clojure.core/== n' k) ((== tail #{}) s)
                          :else ((lmap-suspend `counto [c n] #(set-counto c n) [c n]) s))
          :else ((lmap-suspend `counto [c n] #(set-counto c n) [c n]) s))))))

;; =============================================================================
;; miniKanren parity: defrel, type constraints, absento

(defmacro defrel
  "Defines a relation, as in The Reasoned Schemer: like defn, but the body
   is a conjunction of goals, suspended until the relation is searched, so
   that recursive relations interleave fairly."
  [name & more]
  (let [[doc more] (if (string? (first more)) [[(first more)] (next more)] [[] more])
        [args & goals] more]
    `(defn ~name ~@doc ~args
       (fn [a#]
         (-inc (bind* a# succeed ~@goals))))))

;; Type constraints. A var constrained to a type carries the type as a
;; domain, so that unifying two vars of different types fails at once, and
;; a constraint checks the value it is bound to.

(deftype TypeDom [t]
  IMergeDomains
  (-merge-doms [a b]
    (when (= t (.t ^TypeDom b)) a)))

;; The collection kinds tell a list from a vector, which unify with each
;; other as they are = in Clojure.
(def ^:private type-preds
  {:sym symbol? :num number? :str string? :kw keyword?
   :list #(or (lcons? %) (seq? %))
   :vector #(or (vector? %) (lvec? %))
   :map #(or (map? %) (lmap? %))
   :set #(or (set? %) (lset? %))})

(defn- type-kind
  "The collection kind (see coll-kind) the type constraint on the var x
   gives, or nil if it has none."
  [s x]
  (when-let [d (get-dom s x ::type)]
    (case (.t ^TypeDom d)
      :map :map
      (:vector :list) :seq
      :set :set
      :other)))

(defn- -typec [x t rel]
  (reify
    IConstraintStep
    (-step [this s]
      (reify
        clojure.lang.IFn
        (invoke [_ s]
          (when ((type-preds t) (walk s x))
            ((remcg this) s)))
        IRunnable
        (-runnable? [_]
          (not (lvar? (walk s x))))))
    IConstraintOp
    (-rator [_] rel)
    (-rands [_] [x])
    IReifiableConstraint
    (-reifyc [_ v r s]
      (list rel (-reify s x r)))
    IConstraintWatchedStores
    (-watched-stores [_] #{::subst})))

(defn- typeo [t rel x]
  (fn [s]
    (let [v (walk s x)]
      (if (lvar? v)
        (let [d (get-dom s v ::type)]
          (cond
            (nil? d) ((cgoal (-typec v t rel)) (add-dom s v ::type (TypeDom. t)))
            (= t (.t ^TypeDom d)) s
            :else nil))
        (when ((type-preds t) v) s)))))

(defn symbolo
  "A constraint that x is a symbol."
  [x]
  (typeo :sym `symbolo x))

(defn numbero
  "A constraint that x is a number."
  [x]
  (typeo :num `numbero x))

(defn stringo
  "A constraint that x is a string."
  [x]
  (typeo :str `stringo x))

(defn keywordo
  "A constraint that x is a keyword."
  [x]
  (typeo :kw `keywordo x))

(defn- term-children
  "The subterms of the walked term x, or nil if it has none."
  [x]
  (cond
    (lcons? x) [(lfirst x) (lnext x)]
    (lmap? x) (concat (keys (lmap-entries x)) (vals (lmap-entries x)) [(lmap-rest x)])
    (lvec? x) (let [[f m b] (lvec-parts x)] (concat f [m] b))
    (lset? x) (concat (lset-elems x) [(lset-rest x)])
    (map? x) (concat (keys x) (vals x))
    (coll? x) (seq x)
    :else nil))

(defn absento
  "A constraint that the term t occurs nowhere in the term x."
  [t x]
  (fn [s]
    (let [t' (walk* s t)
          x' (walk s x)]
      (cond
        (lvar? x')
        (if (identical? x' t')
          nil
          ((all
            ;; x is a subterm of itself, and a var t may become x
            (if (ground-term? t' s) succeed (!= x' t'))
            ;; the keys and values waiting relations put into x
            (everyg (fn [[k v]] (all (absento t k) (absento t v)))
                    (when (::picks (meta s))
                      (for [c (vals (:cm (:cs s)))
                            :let [[m2 k2 v2] (:pick (::lmap-rel (meta c)))]
                            :when (and m2 (= x' (walk s m2)))]
                        [k2 v2])))
            (fn [s]
              (lmap-pend s `absento [t x] #(absento t x) [x] false
                         {:absent [t x]})))
           s))

        :else
        ((all
          (if (and (ground-term? t' s) (not (coll? t')) (not (tree-term? t')))
            (if (= x' t') fail succeed)
            (!= x' t'))
          (everyg #(absento t' %) (term-children x')))
         s)))))

(extend-protocol IDisunifyTerms
  LVec
  (-disunify-terms [u v s cs]
    ;; keep the whole pair, as for maps: unifying open sequences may
    ;; introduce fresh vars
    (when (and (or (sequential? v) (lcons? v) (lvec? v)) (unify s u v))
      (assoc cs :prefixc (assoc (:prefixc cs) u v)))))

(defn tree-term? [x]
  (or (coll? x)
      (instance? ITreeTerm x)))
