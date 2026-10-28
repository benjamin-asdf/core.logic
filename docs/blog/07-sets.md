# Sets

*My core.logic fork, part 7 of 9.* [Index](README.md) · [← Towards relational hyperdimensional computing](06-relational-hdc.md) · [Side by side with miniKanren →](08-side-by-side-with-minikanren.md)

Upstream core.logic doesn't know sets. A set is just a value to it: a logic
variable inside `#{x}` is never bound, never reified, and `#{x}` unifies
with nothing but an identical set. This fork makes sets relational, and it
does so almost for free, because a set is a map without values.

## Same design as maps

Everything from [part 2](02-no-unsupported-behaviour.md) carries over, with
"element" for "key":

- **Open sets** are known elements plus an unknown rest, `(lset #{1 2} | _0)`.
  The rest is constrained to lack the known elements. Like the keys of an
  open map, the elements of an open set are always known. That restriction
  keeps open sets cheap: they never branch.
- **Set literals may hold unknown elements**, and those stay pairwise
  distinct. `#{x y}` is a set of two, and fails once `x` and `y` become equal,
  even if that happens long after the set was built. The check rides on the
  occurs check, exactly as for map keys.
- **Unifying sets with unknown elements branches** over which elements pair
  up, committing when one pairing is left and waiting otherwise.

```clojure
(run* [s] (containso s 1) (containso s 2))
;;=> ((lset #{1 2} | _0))

(run* [x y] (== #{x y} #{1 2}))
;;=> ([1 2] [2 1])

(run* [x y] (== #{x y} #{1}))
;;=> ()
```

## Relations

`containso`, `lackso`, `conjo`, `disjo` and `lseto` are the set versions of
`geto`, `lacks-keyo`, `assoco`, `dissoco` and `lmapo` (`lseto` is the set's
basic form: `conj` of elements that weren't there yet), and every one runs in
every direction:

```clojure
(run* [s] (disjo s 1 #{2}))
;;=> (#{1 2} #{2})                ;; s had 1, or it didn't

(run* [x r] (lseto #{1 2 3} #{x} r))
;;=> ([1 #{3 2}] [3 #{1 2}] [2 #{1 3}])
```

A membership question on an open set gets every honest answer, including
"some element of the rest I don't know yet":

```clojure
(run* [x] (fresh [s] (lseto s #{1 2} (lvar)) (containso s x)))
;;=> (1 2 (_0 :- (clojure.core.logic/containso (lset #{1 2} | _1) _0) (!= (_0 1)) (!= (_0 2))))
```

## Set algebra

`uniono`, `intersectiono`, `differenceo`, `subseto` and `disjointo` act as
soon as one side is closed, and wait otherwise, like `mergeo`. Backwards they
enumerate exactly the possibilities:

```clojure
(run* [a b] (uniono a b #{1 2}))
;;=> 9 answers: each element in a, in b, or in both

(run* [a] (differenceo a #{2 3} #{1}))
;;=> (#{1 3 2} #{1 2} #{1 3} #{1})

(run* [a] (subseto a #{1 2}))
;;=> (#{1 2} #{2} #{1} #{})
```

On sets of plain values they are a single `clojure.set` call: union and
intersection of two 500-element sets take under a millisecond.

## What theory says

Set unification is NP-complete (Kapur and Narendran, 1986), so branching on
unknown elements can't be avoided in general; [part
5](05-literature-and-parity.md) has the details. {log} (Dovier, Omodeo,
Pontelli, Rossi) allows unknown elements in open sets too, and pays with
four-way branching on every open-set unification and redundant answers. This
fork makes the same trade as for maps: open sets have known elements, and
the hard cases are confined to closed literals, where the branching is a
bijection and produces each answer once.

## One deliberate difference from Clojure

`(get #{1} 1)` is `1` in Clojure, but `geto` doesn't work on sets. Allowing
it would make every `geto` on a collection of unknown kind also consider "a
set holding the key, with the value equal to the key". That would change map
answers that have nothing to do with sets. Use `containso` for sets.
