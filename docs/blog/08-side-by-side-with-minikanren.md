# Side by side with miniKanren

*Part 8 of a series on my core.logic fork. [Overview](../../README.md) ·
[Part 7](07-sets.md)*

faster-miniKanren is the reference miniKanren: the one used for the quine
papers, program synthesis and *The Reasoned Schemer*'s second edition. This
post asks two questions:

- Where core.logic and miniKanren overlap, do they give the same answers?
- Where this fork goes further (maps, vectors, sets), what does the
  miniKanren program look like, and what does it answer?

Every output below comes from running the code: miniKanren with
faster-miniKanren under Racket, core.logic on the JVM.

## Running miniKanren's own tests

`script/fmk_tests.py` translates faster-miniKanren's test suite to
core.logic: 355 tests of `==`, `=/=`, `symbolo`, `numbero`, `stringo`,
`absento`, type inference, and the arithmetic of *The Reasoned Schemer*. The
two systems print answers differently, so both sides are normalised before
comparing (`_.0` and `_0`, `=/=` and `!=`, variable numbering, constraint
order).

On the first run, 202 of 355 agreed. The rest came down to seven bugs and one
missing feature.

| Bug | Since |
|---|---|
| `!=` between two improper lists threw an exception. | upstream |
| `(!= (lcons 1 x) [1 2])` said "always different", losing `x ≠ (2)`. | upstream |
| `(!= [q q] [p r])` kept only `q ≠ r`: the second pairing of `q` overwrote the first. So `q=1, p=2, r=1` was wrongly rejected. | upstream |
| Re-checking `!=` used `=` on lists, which treats logic variables as wildcards. `(!= q (a . b))` followed by `q = (3 . 4)` failed. | upstream |
| A constrained variable walks to a copy of itself; `!=` compared by identity and stored the impossible `a ≠ a`. | upstream |
| The variables inside nested improper lists went unwatched, so `!=` on them never woke up. | upstream |
| `absento` waited for its first argument to be ground, so `(absento q q)` succeeded. | this fork |

All but the first give wrong answers: either answers that aren't
solutions, or missing solutions. All are fixed, and each has its own
regression test.

The missing feature was answer cleanup. faster-miniKanren leaves out
constraints that can't matter to the answer. That's any constraint on a
variable the answer doesn't show, `x ≠ 5` when `x` is a symbol, `x ≠ y` when
`(absento x y)` is there, and so on. core.logic printed them all. It now
simplifies the same way:

```scheme
;; miniKanren
(run* (q) (fresh (x) (== q `(,x)) (symbolo x) (=/= x 'lambda)))
;;=> (((_.0) (=/= ((_.0 lambda))) (sym _.0)))
```

```clojure
;; core.logic
(run* [q] (fresh [x] (== q [x]) (symbolo x) (!= x 'lambda)))
;;=> (([_0] :- (!= (_0 lambda)) (clojure.core.logic/symbolo _0)))
```

Now 352 of 355 agree, and all of them run with `lein test`, in about three
seconds. The three skipped tests are documented in the script:

- **Search order:** one is `run 12` on an infinite stream, where a
  different search order gives a different first twelve.
- **Equivalent form:** one prints the same constraint in another normal
  form: `(!= (_0 _1) (_1 _2))` where miniKanren writes `((_.0 _.1) (_.0 _.2))`.
- **Redundant constraint:** one shows an extra constraint that a
  disequality already implies.

## The same program gives the same answers

Programs that only use lists translate line by line:

```scheme
;; miniKanren
(defrel (appendo l s out)
  (conde
    [(== '() l) (== s out)]
    [(fresh (a d res)
       (== `(,a . ,d) l)
       (== `(,a . ,res) out)
       (appendo d s res))]))

(run* (x y) (appendo x y '(1 2 3)))
;;=> ((() (1 2 3)) ((1) (2 3)) ((1 2) (3)) ((1 2 3) ()))
```

```clojure
;; core.logic
(defrel appendo [l s out]
  (conde
    [(== '() l) (== s out)]
    [(fresh [a d res]
       (== (lcons a d) l)
       (== (lcons a res) out)
       (appendo d s res))]))

(run* [x y] (appendo x y '(1 2 3)))
;;=> ([() (1 2 3)] [(1) (2 3)] [(1 2) (3)] [(1 2 3) ()])
```

The rest of this post is about data that miniKanren has to encode as lists.

## Maps: association lists versus `geto`

miniKanren has no maps. The usual encoding is an association list, as in the
relational interpreter's environment:

```scheme
(defrel (lookupo k m v)
  (fresh (k2 v2 rest)
    (== `((,k2 . ,v2) . ,rest) m)
    (conde
      [(== k k2) (== v v2)]
      [(=/= k k2) (lookupo k rest v)])))
```

Looking up a key works the same in both, forwards and backwards:

```scheme
(run* (k) (lookupo k '((a . 1) (b . 2)) 2))   ;;=> (b)
```

```clojure
(run* [k] (geto {:a 1 :b 2} k 2))              ;;=> (:b)
```

Asking for a map that holds two entries is where they part. One map has
infinitely many association lists: any order, any other keys in between.
So miniKanren enumerates them, forever:

```scheme
(run 4 (m) (lookupo 'a m 1) (lookupo 'b m 2))
;;=> (((a . 1) (b . 2) . _.0)
;;    ((b . 2) (a . 1) . _.0)
;;    (((a . 1) (_.0 . _.1) (b . 2) . _.2) (=/= ((_.0 b))))
;;    (((a . 1) (_.0 . _.1) (_.2 . _.3) (b . 2) . _.4) (=/= ((_.0 b)) ((_.2 b)))))
;;   run* never returns
```

core.logic answers once, with an open map, and stops:

```clojure
(run* [m] (geto m :a 1) (geto m :b 2))
;;=> ((lmap {:b 2, :a 1} | _0))
```

Equality is the other difference. Two association lists in different orders
don't unify, though they mean the same map:

```scheme
(run* (q) (== '((a . 1) (b . 2)) '((b . 2) (a . 1))))   ;;=> ()
```

```clojure
(run* [q] (== {:a 1 :b 2} {:b 2 :a 1}))   ;;=> (_0)
(run* [x k] (== {:a x :b 2} {k 2 :a 1}))  ;;=> ([1 :b])
```

## Sets: lists versus `containso`

The same pattern repeats for sets. With lists and `membero`, every order and
every padding is another answer:

```scheme
(run 4 (s) (membero 1 s) (membero 2 s))
;;=> ((1 2 . _.0) (2 1 . _.0) (1 _.0 2 . _.1) (1 _.0 _.1 2 . _.2))
```

```clojure
(run* [s] (containso s 1) (containso s 2))
;;=> ((lset #{1 2} | _0))
```

Set equality and set algebra run in every direction:

```clojure
(run* [x y] (== #{x y} #{1 2}))           ;;=> ([1 2] [2 1])
(count (run* [a b] (uniono a b #{1 2})))  ;;=> 9, each element in a, b or both
```

## Vectors: `appendo` versus `concato`

`appendo` only looks at elements. When both lists are unknown it generates
lengths one by one, and if the answer depends on lengths, it never finds out:

```scheme
(run 1 (x) (appendo x '(1) x))
;;   no answer within 20 seconds: it tries ever longer x

(run 1 (x) (fresh (l r) (appendo x '(1) l) (appendo '(1) x r) (appendo r '(2) l)))
;;   no answer within 20 seconds

(run 3 (x) (fresh (y) (appendo x '(1) y) (appendo '(1) x y)))
;;   (() (1)) for run 2; the third answer doesn't come within 15 seconds
```

The fork's vectors solve lengths first ([part 4](04-vectors.md)), so the
first two fail at once and the third enumerates:

```clojure
(run* [x] (concato x [1] x))
;;=> ()        ;; |x| + 1 ≠ |x|

(run* [x] (fresh [l r] (concato x [1] l) (concato [1] x r) (concato r [2] l)))
;;=> ()        ;; |x| + 1 ≠ |x| + 2

(run 3 [x] (fresh [y] (concato x [1] y) (concato [1] x y)))
;;=> ([] [1] [1 1])
```

Length reasoning doesn't make every word equation finite. When the lengths
agree, as in `x ++ [1] = [2] ++ x`, only the elements show the conflict, and
the fork enumerates forever too ([part 5](05-literature-and-parity.md)).

Indexing and paths have no direct miniKanren counterpart. They'd need Peano
numerals and a chain of lookups:

```clojure
(run* [i] (ntho [:a :b :a] i :a))                                  ;;=> (0 2)
(run* [p] (get-ino {:users [{:name "ada"} {:name "bob"}]} p "bob"))
;;=> ((:users 1 :name))
```

## What is still different

- **Notation:** `_0` for `_.0`, `!=` for `=/=`, `symbolo` for `sym`, and
  answers as `(value :- constraints)`.
- **Search order:** `conde`, `fresh` and `defrel` interleave differently, so
  `run n` can give a different first `n` answers. `run*` gives the same set.
- **ClojureScript:** none of this works there yet; see
  [future work](../future-work.md).
