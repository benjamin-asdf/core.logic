# Future work

*Part of my core.logic fork. [Overview](../README.md)*

Two larger items are parked here. Both need design decisions before any code.

## ClojureScript port

**State.** The cljs side is an old, separate copy: `cljs/core/logic.cljs`
(about 950 lines) and its macros in `cljs/core/logic.clj` (about 460), against
5,500 lines in the JVM namespace. It has unification, `conde`, `fresh` and
`run`, but no constraint store. So it has no `!=`, no CLP(FD), no nominal
logic, no tabling, and none of this fork's maps, vectors, sets, type
constraints or `absento`.

**Why it is big.** Everything this fork adds sits on the cKanren constraint
store (`cgoal`, `-step`, `run-constraints*`, domains, `reifyg`). Porting the
data structures means porting that machinery first. Copying it a second time
would double the maintenance of every future change.

**Plan.**

1. Consolidate into `.cljc`: one `clojure.core.logic` namespace with
   reader conditionals for the host-specific bits (deftype interfaces like
   `clojure.lang.IPersistentMap` versus cljs protocols, `Long` versus
   number, `Object` versus `default`, macros in a `.cljc` macro namespace).
2. Port the constraint store and its tests, then `fd` and `nominal`.
3. Then maps, vectors, sets, paths and the parity relations come along
   unchanged, since they are written against the store.
4. Run the existing cljs test file plus the JVM test suite under cljs, so the
   two hosts agree answer for answer.

**Risks.** Performance tricks that rely on JVM specifics (transients,
`identical?` on boxed numbers, mutable fields in deftypes) need checking.
cljs has no stack-overflow headroom to spare, so the lazy `or-goals` and
other deep recursion need testing on large inputs. Advanced compilation can
break printing of residual constraints that relies on var names.

**Decisions needed.** Whether to replace the old cljs namespace outright
(answer shapes change, as they did on the JVM) or keep it as legacy; and
whether a `.cljc` merge is acceptable even though it makes the diff against
upstream unreadable.

## Records as types

**State.** core.logic already unifies two records of the same class field by
field (`unify-with-record`). Records don't take part in anything this fork
adds: an LMap never unifies with a record, and `geto` on a record isn't
covered by tests.

**Small part: honour Clojure's equality.** `(= (->Point 1 2) {:x 1 :y 2})` is
false, so a record must never unify with a plain map or an LMap. `assoco` of
an extra key keeps the record type; `dissoco` of a declared field turns it
into a plain map. Relationally, that last rule is a constraint between the
result's type and which keys it still has. This part is cheap and fits the
"no unsupported behaviour" rule.

**Interesting part: the type as data.** A `defrecord` is a JVM class and
can't be searched. Make the type a term instead, `{:name Point :fields #{:x :y}}`,
with a relation `(recordo r T m)`: `r` is an instance of type `T` with
contents `m`. Each argument may be unknown:

| Known | Unknown | Gives |
|---|---|---|
| `T`, `m` | `r` | a constructor |
| `r` | `T`, `m` | destructuring |
| a partial map | `T` | classification against the known types |
| some instances | `T` | schema inference |

The list of known types is just a relation, a `pldb` fact like
`(record-type name fields)`, so no JVM registry is needed. Field lists are
sets, which the fork now has. The prior art is Aït-Kaci's ψ-terms and OSF
unification: a record type is a sort, and unification takes the meet of
sorts ([part 5](blog/05-literature-and-parity.md)).

**Decisions needed.**

- **Picking one schema.** Every subset of the shared keys is a valid field
  list for "infer the type from these instances". Choose smallest, largest,
  or keep it as a constraint and enumerate only on demand.
- **What answers look like.** Real record instances only when the type is
  ground and a class exists (or generate the `defrecord` then), typed maps
  `{:type Point ...}` otherwise.
- **Sort hierarchy or flat types.** ψ-term style subtyping (a type with more
  fields is a subsort) is more expressive and costs a lattice meet in
  unification.
- **Protocol dispatch.** A goal that waits for the type and then runs that
  type's implementation, or enumerates the types implementing a protocol.
  This is type-class resolution by search, a research project in itself.
