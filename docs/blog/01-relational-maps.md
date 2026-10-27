# Relational maps for core.logic

*My core.logic fork, part 1 of 8.* [Index](README.md) · [No unsupported behaviour →](02-no-unsupported-behaviour.md)

miniKanren grew up on lists. `appendo` runs forwards and backwards, `membero`
enumerates, and the whole thing works because a list that is only partly known
has a natural representation: a known front and an unbound tail, `(1 2 . _0)`.

Clojure programs don't live in lists. They live in maps. And core.logic, until
now, had no good answer for a map that is partly known. You could unify two
maps with exactly the same keys, and `featurec` could require a map to have
some entries, but nothing could build a map or take one apart. There was no `(get m k)` you could run
backwards, no `(assoc m k v)` that answers "what was `m`?".

This fork adds them.

## Open maps

The central idea is the same as the list tail. A map that is only partly known
is a set of known entries plus an unbound *rest*:

```clojure
(run* [m] (geto m :a 1))
;;=> ((lmap {:a 1} | _0))
```

Read `(lmap {:a 1} | _0)` as "a map with `:a` → `1`, plus whatever `_0` holds".
`_0` is a map too, and it is constrained not to contain `:a`: the entries and the
rest never overlap. Ask for more and the open map grows:

```clojure
(run* [m] (geto m :a 1) (geto m :b 2))
;;=> ((lmap {:b 2, :a 1} | _0))
```

Close it by saying what all the keys are:

```clojure
(run* [m] (geto m :a 1) (geto m :b 2) (keyso m [:a :b]))
;;=> ({:a 1, :b 2})
```

An open map with nothing left open is just a Clojure map. Answers come back as
ordinary maps whenever they can.

## Every relation, every direction

`geto` is `get`. Forwards it looks up; with the key unknown it enumerates; with the
value known it searches:

```clojure
(run* [v] (geto {:a 1 :b 2} :b v))      ;;=> (2)
(run* [k v] (geto {:a 1 :b 2} k v))     ;;=> ([:a 1] [:b 2])
(run* [k] (geto {:a 1 :b 2} k 2))       ;;=> (:b)
```

`assoco` is `assoc`. Run backwards, it finds *every* map that `assoc` could
have produced the output from:

```clojure
(run* [out] (assoco {:a 1} :b 2 out))          ;;=> ({:a 1, :b 2})
(run* [m] (assoco m :b 2 {:a 1 :b 2}))         ;;=> ({:a 1} {:a 1, :b _0})
(run* [k v] (assoco {:a 1} k v {:a 1 :b 2}))   ;;=> ([:b 2])
```

The second answer matters. `m` either had no `:b`, or had `:b` with any value
that `assoc` overwrote. Both are real answers, and a relational `assoc` that
returned only the first would be wrong.

`dissoco` is `dissoc`, the same way round:

```clojure
(run* [out] (dissoco {:a 1 :b 2} :a out))  ;;=> ({:b 2})
(run* [m] (dissoco m :a {:b 2}))           ;;=> ({:b 2} {:b 2, :a _0})
(run* [k] (dissoco {:a 1 :b 2} k {:b 2}))  ;;=> (:a)
```

`mergeo` is `merge`. Backwards it splits a map every way `merge` could have
built it, including the overwritten values:

```clojure
(run* [m1] (mergeo m1 {:b 2} {:a 1 :b 2}))
;;=> ({:a 1} {:a 1, :b _0})
```

The rest of the API:

| Relation | Means |
|---|---|
| `(keyso m ks)` / `(valso m vs)` | the keys / values of `m`, in any order |
| `(selectso m ks out)` | `out` is `(select-keys m ks)` |
| `(lmapo m entries rest)` | `m` is `entries` plus a map `rest` without their keys |
| `(lacks-keyo m & ks)` | `m` has none of the keys `ks` |

```clojure
(run* [ks] (keyso {:a 1 :b 2} ks))                  ;;=> ((:a :b) (:b :a))
(run* [x r] (lmapo {:a 1 :b 2 :c 3} {:a x} r))      ;;=> ([1 {:b 2, :c 3}])
(run* [out] (selectso {:a 1 :b 2 :c 3} [:a :c] out)) ;;=> ({:c 3, :a 1})
```

`keyso` lists every order because Clojure doesn't promise one. A relation that
returned only `(:a :b)` would fail on a query asking for `(:b :a)`, which is a
perfectly good key list.

## Plain maps with unknown keys

The part I'm happiest with: you don't need any of the relations to get
relational maps. Plain Clojure maps unify relationally, even when their keys
are logic variables:

```clojure
(run* [k] (== {k 1 :b 2} {:a 1 :b 2}))          ;;=> (:a)
(run* [k1 k2] (== {k1 1 k2 2} {:a 1 :b 2}))     ;;=> ([:a :b])
(run* [k1 k2 v] (== {k1 v k2 v} {:a 1 :b 1}))   ;;=> ([:a :b 1] [:b :a 1])
```

The last one has two answers because both pairings are real. Upstream
core.logic would treat `k1` and `k2` as keys that happen to be symbols, and
fail.

A Clojure map can't have two equal keys, and that holds here too, even if the
keys only become equal later:

```clojure
(run* [k1 k2] (== {k1 1 k2 1} {:a 1}))                ;;=> ()
(run* [k1 k2] (== k1 k2) (== {k1 1 k2 2} {:a 1 :b 2}))  ;;=> ()
(run* [k1 k2]
  (fresh [m] (== m {k1 1 k2 2}) (== k1 :a) (== k2 :a)))  ;;=> ()
```

The last query is the hard case: the map was built when its keys were still
distinct variables, and only afterwards were both bound to `:a`. The
[next post](02-no-unsupported-behaviour.md) is about how that is caught without
making everything else slow.

## When it can't decide yet

Some queries have no finite answer yet. "Some map holds `1` under some
key" is one. Instead of guessing, the goal waits and shows up in the answer as
a constraint:

```clojure
(run* [m] (fresh [k] (geto m k 1)))
;;=> ((_0 :- (clojure.core.logic/geto _0 _1 1)))
```

That is the rule this fork is built on: a relation either answers correctly,
or it says what it is still waiting for. It never quietly answers wrong.

## Constraints between them

Absence is a real constraint, and it holds no matter which goal runs first:

```clojure
(run* [m] (lacks-keyo m :a) (geto m :a 1))                    ;;=> ()
(run* [q] (fresh [m] (lacks-keyo m :a) (== m {:a 1})) (== q 1)) ;;=> ()
```

Next: [No unsupported behaviour](02-no-unsupported-behaviour.md), on the
design behind all this.
