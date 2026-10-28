# My core.logic fork

A series on making Clojure's maps, vectors and sets relational in core.logic:
every relation runs in every direction, and anything it can't decide yet, it
waits on visibly instead of guessing. The code and an overview are in the
[repository README](../../README.md).

## Why this is the core.logic thing

A logic language takes its terms from its host. miniKanren's term is the
Scheme pair, because Scheme's data is the pair: `appendo` and `membero` work
so well because a partly known list has a natural shape, a known front and an
unbound tail. core.logic brought miniKanren to Clojure, and the pair came
along. Clojure's own data came in second class: two maps unified only if they
had exactly the same keys, and apart from `featurec` reading values at known
keys, nothing could take a map apart or build one.

But the data is what Clojure is. Literal, immutable maps, vectors and sets,
used for everything: "just use maps", data over functions over macros, a
program is a pipeline of `get`, `assoc`, `merge`, `conj` and `union`. Clojure
programmers don't encode a record as an association list or a set as a list
with no duplicates; they write `{:name "ada"}` and `#{1 2}`.

So a relational Clojure should be relational over *that*. This series makes
it so: `get`, `assoc`, `merge`, `nth`, `concat`, `union` and friends, each as
a relation that runs backwards. A query can ask which map an `assoc` came
from, which key path leads to a value, or which two sets have this union, on
the same data the rest of the program uses. That's the part of core.logic only
Clojure can have, and what miniKanren-on-lists can only encode.

This isn't a new wish. In 2013 David Nolen put it on core.logic's own
roadmap. The wiki page
[Constraints & modes](https://github.com/clojure/core.logic/wiki/Constraints-&-modes)
opens: "core.logic unfortunately to this day continues to emphasize operating
on sequence-like data structures due to its Prolog & Scheme roots", and asks
for "constraint versions of Clojure functions". It sketches an `assocc`, finds
that running it backwards branches, and settles on `conjo` as the test case:

```clojure
(run* [q]
  (fresh [v o]
    (== o {:foo 1})
    (conjo q [:foo v] o)))
```

"So we should see the following results: `({} {:foo _0})`." That is exactly
what the fork answers. The companion page
[CLP(Set)](https://github.com/clojure/core.logic/wiki/CLP(Set)) asks for sets
with unknown elements, `(unionc #{:cat x y} #{:dog :bird z} o)`, and notes
that such a union branches over which elements pair up. The fork runs that one
too: with `o` = `#{:cat :dog :bird}`, `x` and `y` are `:dog` and `:bird` in
either order and `z` is `:cat`. (Writing this found a bug: the fork used to
let `x` be `:cat` too. Fixed.) Both pages are still on the wiki's roadmap,
under "Immediate", and were never built. The machinery they sketch is not what
this series builds (a `defc` with mode declarations, set domains like the FD
domains), but their test cases are what it answers.

It also sets the bar. A relation that only works in some directions is a
function with extra steps, so the series holds every relation to one rule: it
answers correctly in every mode, or waits until it can
([part 2](02-no-unsupported-behaviour.md)).

1. [Relational maps](01-relational-maps.md): a tour of the API.
2. [No unsupported behaviour](02-no-unsupported-behaviour.md): why the design
   had to be redone, and how unknown keys, lazy checks and suspended goals fit
   together.
3. [Making it fast](03-making-it-fast.md): from 33 s to 8 ms, and what was
   slow.
4. [Vectors](04-vectors.md): open vectors, lengths solved exactly, and
   `get-in` as a query language.
5. [Literature and miniKanren parity](05-literature-and-parity.md): where this
   sits in the research, and what core.logic still lacks.
6. [Towards relational hyperdimensional computing](06-relational-hdc.md): the
   same data structures, encoded as hypervectors.
7. [Sets](07-sets.md): maps without values, and what that buys.
8. [Side by side with miniKanren](08-side-by-side-with-minikanren.md):
   faster-miniKanren's test suite run on core.logic, the bugs it found, and
   maps, sets and vectors next to their miniKanren encodings.
9. [A relational Clojure interpreter](09-a-relational-clojure-interpreter.md):
   `evalo` for a Clojure subset, with relational maps as environments; what
   it runs backwards, and where its search is still slow.

Next, maybe: records as types, and ClojureScript. See
[future work](../future-work.md).
