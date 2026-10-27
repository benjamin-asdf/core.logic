# core.logic — relational data fork

Benjamin's fork making Clojure maps, vectors and sets relational. What exists: README.md; blog series "My core.logic fork": docs/blog/ (index README.md; 01 maps … 08 side by side with miniKanren); parked work: docs/future-work.md.

## Hard rule

No unsupported behaviour: every relation is correct in every mode (answers, fails, or visibly waits). If that is slow, redesign rather than relax. Build new collection relations to the same rule and API style; ask before deviating.

## Decided designs (2026-10-26/27)

- Maps: goal-based API, all key permutations; plain maps are relational, distinct keys checked lazily, piggybacking on the occurs check. JVM first, cljs later.
- Vectors (`LVec`): front + unknown middle + back. Lengths reasoned exactly by the fork's own linear solver (constant + sum of middle lengths, elimination, all ≥ 0) before enumeration. core.logic FD was rejected (stack overflow on unbounded lengths); FD vars interoperate by waiting for labeling. Vectors live in the core ns, keep unifying with lists (Clojure `=`). `geto`/`assoco` are shared between maps and vectors and wait while the type is unknown.
- Done: `get-ino`/`assoc-ino`, `defrel`, type constraints, `absento` (faster-miniKanren's quine interpreter ported as a test), sets — open sets hold known elements only; `geto` deliberately not on sets.
- FD answers: opt-in `(fd/residual)` shows domains and FD constraints instead of labeling, only if a solution exists; labeling stays the default.
- Parity: faster-miniKanren's test suite is generated into src/test (script/fmk_tests.py, needs a faster-miniKanren checkout); 352/355 agree, 3 skips documented in the script.
- Open: records as data-level type terms (schema inference, pldb registry), ClojureScript port; both in docs/future-work.md.

Benjamin's own field is hyperdimensional computing (HDC/VSA); a relational HDC framework on top of this is of interest.
