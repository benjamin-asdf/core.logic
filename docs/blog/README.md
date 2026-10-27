# My core.logic fork

A series on making Clojure's maps, vectors and sets relational in core.logic:
every relation runs in every direction, and anything it can't decide yet, it
waits on visibly instead of guessing. The code and an overview are in the
[repository README](../../README.md).

1. [Relational maps](01-relational-maps.md): a tour of the API.
2. [No unsupported behaviour](02-no-unsupported-behaviour.md): why the design
   had to be redone, and how unknown keys, lazy checks and suspended goals fit
   together.
3. [Making it fast](03-making-it-fast.md): from 33 s to 8 ms, and what was
   slow.
4. [Vectors](04-vectors.md): open vectors, and lengths solved exactly.
5. [Literature and miniKanren parity](05-literature-and-parity.md): where this
   sits in the research, and what core.logic still lacks.
6. [Towards relational hyperdimensional computing](06-relational-hdc.md): the
   same data structures, encoded as hypervectors.
7. [Sets](07-sets.md): maps without values, and what that buys.
8. [Side by side with miniKanren](08-side-by-side-with-minikanren.md):
   faster-miniKanren's test suite run on core.logic, the bugs it found, and
   maps, sets and vectors next to their miniKanren encodings.

Next, maybe: records as types, and ClojureScript. See
[future work](../future-work.md).
