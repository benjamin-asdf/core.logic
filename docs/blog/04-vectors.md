# Vectors

*My core.logic fork, part 4 of 8.* [Index](README.md) · [← Making it fast](03-making-it-fast.md) · [Where this sits: the literature, and parity with miniKanren →](05-literature-and-parity.md)

After maps, vectors. Same rule as for maps: every relation correct in every
mode, or waiting visibly.

## What upstream core.logic does

Vectors, lists and partial lists already unify with each other as sequences.
`(== [a b] (lcons 1 r))` works. What's missing is everything that makes a
vector a vector:

- The only partly known sequence is a known front plus an unknown tail,
  `(1 2 . _0)`. Nothing can be known about the *end* of a sequence whose
  length is unknown.
- Answers built from partial lists come back as lists, not vectors.
- No relations for positions (`nth`), length (`count`), the end (`conj`,
  `peek`, `pop`), slices (`subvec`) or concatenation that know about vectors.

## The term: front, middle, back

A partly known vector is a known front, an unknown middle and a known back.
In answers it prints as

```clojure
(lvec [a b] | _0 | [y z])
```

The middle is an unbound variable standing for a vector of any length,
including zero. A partial list `(a b . t)` is the special case with an empty
back.

Why the back: Clojure vectors grow at the end. `conj`, `peek` and `pop` act on
the last element. With only a front and a tail, every one of those has to
search over the unknown length. With a back, they're direct:

```clojure
(conjo v x out)   ;; out is [f | m | b x]: no search
(peeko v x)       ;; the last of b, if b isn't empty
```

When `b` is empty, `peeko` has two cases: the middle is not empty (then
`m = [| m' | x]`, one general answer), or it is empty and `x` is the last of the
front. Finitely many branches, never an unbounded search.

It's the same idea as Prolog's difference lists, which make the end of a
list reachable, extended to both ends.

## Unification

Unifying `[f1 | m1 | b1]` with `[f2 | m2 | b2]`:

1. Unify the fronts element by element, as far as both go. Same for the backs,
   from the end.
2. What's left has at most one side with a front left over, and at most one
   with a back left over.
3. If one side has nothing left over, its middle *is* the other side: a
   single binding.
4. Otherwise it's `m1 ++ B = F ++ m2`: the two middles overlap in an unknown
   way. There are `|F| + 1` cases: `m1` covers all of `F` (one general answer
   with a fresh middle), or ends inside `F` at one of `|F|` places.

With two different middles, case 4 is finite, so it uses the same
mechanism as map unification with unknown keys: try it, commit if exactly one
case survives, otherwise keep it pending, and enumerate only before reifying.

With the *same* middle on both sides it is not. `[| x | 1] = [2 | x |]`,
that is `x ++ [1] = [2] ++ x`, has no solution, but every length passes the
length check (`|x| + 1` on both sides), so enumerating never ends. This is a
genuine word equation. The relation can list every answer, but it can't
always fail in finite time.
([Part 5](05-literature-and-parity.md) has the theory.)

The full problem, any number of unknown pieces concatenated, is solving word
equations. That's decidable but very hard, which is why the term has exactly
one unknown part. Concatenation of two open vectors (`concato`) is a relation
that waits, not a term.

## Lengths and positions

Every open vector has a length, and lengths are reasoned about **exactly,
before anything is enumerated**. A length is a constant plus a sum of the
lengths of unknown middles. `concato` posts `|out| = |a| + |b|`, unifying two
vectors equates their lengths, and these linear equations are solved by
elimination, with every length at least 0. Impossible length systems then fail
at once: `x ++ [1] = [1] ++ x ++ [2]` fails on `|x| + 1 ≠ |x| + 2` without
trying a single length. ([Part 5](05-literature-and-parity.md) is why lengths
get this treatment.)

Why not core.logic's FD solver? It narrows intervals one step at a time.
Lengths have no upper bound, and on `|x| + 1 = |x| + 2` with lengths up to
10,000 it overflows the stack before it notices the contradiction. FD
variables still work with `counto`: a length relation waits until an FD
variable is labeled, and FD labeling then enumerates only its domain.

When a length or position is still unknown at the end, relations enumerate:

```clojure
(run 3 [i v] (ntho v i :x))
;;=> ([0 (lvec [:x] | _0 | [])]
;;    [1 (lvec [_0 :x] | _1 | [])]
;;    [2 (lvec [_0 _1 :x] | _2 | [])])
```

The middle stays open in each answer: nothing ties its length to anything. On
an open vector that's infinitely many answers, which is what `membero` already
does on a partial list. With a finite FD domain, only that domain is
enumerated:

```clojure
(run* [v n] (fd/in n (fd/interval 1 2)) (counto v n) (ntho v 0 :a))
;;=> ([[:a] 1] [[:a _0] 2])
```

A known length closes the vector, filling the middle with fresh variables:

```clojure
(run* [q] (fresh [v] (ntho v 0 :a) (ntho v 2 :c) (counto v 3) (== q v)))
;;=> ([:a _0 :c])
```

And lengths that can't match fail before any enumeration. Here
`|a| = |x| + 1 = |b|`, but also `|a| = |b| + 1`:

```clojure
(run* [q] (fresh [x a b]
            (concato x [1] a) (concato [1] x b) (concato b [2] a)
            (== q 1)))
;;=> ()
```

## Relations

| Relation | Means |
|---|---|
| `(ntho v i x)` | `(nth v i)` is `x` |
| `(counto c n)` | `(count c)` is `n`, for vectors and maps |
| `(conjo c x out)` | `out` is `(conj c x)`: at the back of a vector, the front of a list |
| `(peeko c x)` / `(popo c out)` | `(peek c)` / `(pop c)`, at the same end as `conj` |
| `(subveco v start end out)` | `out` is `(subvec v start end)` |
| `(concato a b out)` | `out` is the elements of `a`, then those of `b` |
| `(geto v i x)`, `(assoco v i x out)` | as `get`/`assoc` on vectors |

```clojure
(run* [a b] (concato a b [1 2 3]))
;;=> ([[] [1 2 3]] [[1] [2 3]] [[1 2] [3]] [[1 2 3] []])

(run* [v] (assoco v 1 :x [1 :x 3]))
;;=> ([1 _0 3])        ;; v had anything at index 1
```

`geto` and `assoco` work on both maps and vectors, like `get` and `assoc` in
Clojure, so paths through nested data work:

```clojure
(run* [x] (fresh [u e]
            (geto {:users [{:name "a"} {:name "b"}]} :users u)
            (geto u 1 e)
            (geto e :name x)))
;;=> ("b")
```

When it's not yet known whether something is a map or a vector and the key
is an index, the relation waits, and tries both before the answer comes out:

```clojure
(run* [m] (geto m 0 1))
;;=> ((lmap {0 1} | _0) (lvec [1] | _0 | []))
```

## Vectors and lists

`(= [1 2] '(1 2))` is true in Clojure, and core.logic already unifies them.
That stays. Answers built by the vector relations come back as vectors.

## Where it waits, and where it can't finish

- **Unknown kind.** `conj`, `peek` and `pop` work at different ends of vectors
  and lists, and `count` of an unknown map has no finite answer. So `conjo`,
  `peeko`, `popo` and `counto` on a collection whose kind is still unknown
  wait, and appear in the answer as constraints, e.g.
  `(_0 :- (counto _0 3))`.
- **Infinite answers.** `ntho` with an unknown index, or `counto` with an
  unknown length, on an open vector has infinitely many answers. Use `run n`.
  Positions are enumerated fairly: answer k covers position k in the middle
  and every position in the back that a middle of matching length allows.
- **Word equations.** A middle with elements around it equated with itself
  with *other* elements around it, `x ++ [1] = [2] ++ x`, is enumerated by
  the length of `x`. It finds every answer, but when there is none it does not
  stop.

Next: [Literature and miniKanren parity](05-literature-and-parity.md).
