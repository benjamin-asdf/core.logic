# Where this sits: the literature, and parity with miniKanren

*My core.logic fork, part 5 of 9.* [Index](README.md) · [← Vectors](04-vectors.md) · [Towards relational hyperdimensional computing →](06-relational-hdc.md)

Relational maps are new to miniKanren, but not to logic programming. Records
with features, rows with lacks constraints, sets with rests and words with
unknown pieces all have decades of theory behind them. This post checks the
fork against that theory, and then checks core.logic itself against
miniKanren.

The nearest prior work is core.logic's own roadmap. In 2013 David Nolen's wiki
pages [Constraints & modes](https://github.com/clojure/core.logic/wiki/Constraints-&-modes)
and [CLP(Set)](https://github.com/clojure/core.logic/wiki/CLP(Set)) asked for
relational versions of Clojure's map and set functions, worked through `conjo`
and `unionc` on partly known data, and left them as future work. The
[series index](README.md#why-this-is-the-corelogic-thing) compares their
predictions with what the fork answers.

## Maps are feature logic

Smolka and Treinen's **CFT** ("Records for Logic Programming", *JLP* 1994)
is a logic of records: trees whose edges are labelled by features (keys). It
has feature constraints ("`y` is the child of `x` at `f`"), arity constraints
("`x` has exactly these features") and equations. Satisfiability is
polynomial. It's the record system underneath Oz.

An open map with ground keys is CFT without arity. A closed Clojure map is CFT
with arity. Our lacks constraint is CFT's negated feature atom. So the
ground-key part of this fork sits in a **polynomial** fragment: unifying two
open maps with known keys should never branch. The fork's tests now check that:

```clojure
(run* [q] (fresh [m1 m2 r1 r2]
            (lmapo m1 {:a 1} r1) (lmapo m2 {:b 2} r2)
            (== m1 m2) (== q m1)))
;;=> ((lmap {:b 2, :a 1} | _0))     ;; one answer, nothing left pending
```

Unknown keys are a different story. Treinen's "Feature Constraints with
First-Class Features" (MFCS 1993) lets features be variables. With arity
constraints, satisfiability becomes **NP-complete**. Without them it is
decidable by a simpler algorithm. And the ∀∃ fragment of the first-order
theory is undecidable.

That's exactly our plain maps with unknown keys: closed (arity) plus variable
keys. So the branching over pairings in [part 2](02-no-unsupported-behaviour.md)
isn't a weakness of the implementation. It's inherent, unless P = NP. It also
says *when* it's inherent: only once a closed map or a lacks constraint fixes
the exact key set. Before that, the fork splits at most into "this key" or "a
different key" and leaves the rest pending; it enumerates pairings only once
the key set is fixed.

Aït-Kaci's ψ-terms and OSF unification (LIFE; Aït-Kaci and Podelski, *JLP*
1993) add sorts from a lattice to such records, and unify by taking the meet
of sorts. That's the prior art for the planned records-as-types: a record
type should be a sort, not a key.

## Maps are rows

Type systems for extensible records solved the same unification problem:
Wand (LICS 1987), Rémy (1993), Gaster and Jones (1996), Leijen ("Extensible
Records with Scoped Labels", TFP 2005). Row unification with ground labels has
a single most general unifier: unify `{l: a | r1}` with `{l': b | r2}` by
inventing a fresh `r3`. Gaster and Jones's `lacks` predicate is our
`lacks-keyo`, with the same propagation rule.

The classic trap is two rows sharing a tail: `{:a 1 | r}` against
`{:b 2 | r}` has no solution, and a naive unifier extends `r` forever. The
fork fails it straight away, and now has a test for it.

## Maps are sets of pairs

A map is a set of pairs where no two pairs share a key. Set unification is
NP-complete (Kapur and Narendran, CADE 1986). {log} represents sets with
rests, `{x | s}`, the same shape as our open maps (Dovier, Omodeo, Pontelli
and Rossi, *JLP* 1996; Dovier, Piazza, Pontelli and Rossi, *TOPLAS* 2000; and
the survey by Dovier, Pontelli and Rossi, *TPLP* 2006). Cristiá, Rossi and Frydman
added partial functions to it (*TPLP* 2015), which is the closest match to
maps with unknown keys.

Distinct keys help: matching two closed maps is a bijection, so there are no
duplicate answers of the kind general set unification produces. The tests now
check that each pairing comes out exactly once. For sets later, {log}'s design
carries over directly: rests, a `∉` constraint, and residual constraints
instead of enumeration.

The closest prior art inside miniKanren is very recent: **{Kanren}** (read
"set-Kanren"), from Sanna, Byrd and Amin ("Beyond Cons: Purely Relational
Data Structures", miniKanren Workshop 2025). It has first-class sets, and
constraints for association lists with shadowing and scoped lookup.
Their **chrKanren** (ICLP 2026) builds Constraint Handling Rules into
miniKanren, with semantic unification of user-defined data as an
application. That's an alternative to the hand-written constraints in this fork.
Both are on my reading list before vectors and sets add more of those.

## Vectors are words

Vectors with unknown pieces are word equations. Makanin (1977) showed them
decidable, Plandowski (*JACM* 2004) put them in PSPACE, and Jeż's
recompression (*JACM* 2016) made the algorithm simple. None of that is
practical inside a search like miniKanren's. With length constraints added,
decidability is an **open problem** (Ganesh et al., HVC 2012).

For the [vector design](04-vectors.md) this means:

- One unknown middle per vector, and unification peeling known elements off
  both ends, is cheap. Two *different* middles overlapping is a finite case
  split.
- The *same* middle on both sides is a real word equation:
  `x ++ [1] = [2] ++ x` has no solution, but enumerating lengths never finds
  that out. The lengths agree (`|x| + 1` on both sides), so only the elements
  show the conflict. A relation like `concato` can enumerate every answer.
  It can't always fail in finite time.
- Length reasoning should run first: `x ++ [1] = [1] ++ x ++ [2]` should fail
  on `|x| + 1 ≠ |x| + 2` without enumerating anything. The research
  recommends making lengths FD constraints, not just enumerating them.
- cvc5's theory of sequences (Sheng et al., IJCAR 2022) handles `nth`, update,
  length and concatenation together, and is the best blueprint for the vector
  relations.

## Parity with miniKanren

Compared with faster-miniKanren and *The Reasoned Schemer* (2nd ed.),
core.logic is **ahead** on tabling, nominal logic (αKanren), CLP(FD) and the
fact database. It **matches** on `==`, `fresh`, `conde` interleaving,
`conda`/`condu`, `project`, pattern matching, disequality and the default
occurs check. It was **behind** on these, most important first. The fork has closed
all but the third:

1. ~~`symbolo`, `numbero`, `stringo` are not real type constraints.~~ They
   are now. A constrained variable carries its type, so `(symbolo x)` with
   `(numbero x)` fails while `x` is still unbound, as does unifying a
   symbol-typed variable with a number-typed one.
2. ~~No native `absento`.~~ `(absento t x)` now waits on each unbound part
   of `x`, and keys of maps count as parts.
3. **ClojureScript has no constraints at all**: no `!=`, FD, nominal, tabling
   or maps. The cljs core is an old separate copy, not shared code.
4. ~~No `defrel`.~~ `defrel` defines a relation whose body is suspended until
   it is searched, as in *The Reasoned Schemer*.
5. ~~No port of faster-miniKanren's interpreter and quine benchmarks.~~
   The simple relational interpreter now runs as a test. It finds the classic
   quine `((lambda (x) (list x (list 'quote x))) '(lambda (x) (list x (list 'quote x))))`
   in about 30 ms and a twine in about 0.3 s on the JVM.
6. ~~FD domains aren't reified.~~ With `(fd/residual)` in a `run`, answers
   keep their FD variables unlabeled and show the domains and FD constraints
   left on them, like Prolog's CLP(FD). An answer is only given if labeling
   would find a solution, since narrowing domains alone can't tell.
7. ~~`!=` on maps with unknown keys~~ works, and is now tested. Its leftover
   constraint keeps the two maps as one pair, `(!= ({_0 1} {:a 1}))`, in the
   same `(!= (lhs rhs))` form core.logic uses for every disequality.

What remains is ClojureScript, written up in [future work](../future-work.md).

Since then, faster-miniKanren's own test suite runs on core.logic: 352 of
355 tests agree, after fixing seven `!=` and `absento` bugs it found. See
[part 8](08-side-by-side-with-minikanren.md).

## References

Checked for title, authors, venue and year unless marked *(unchecked)*.

- G. Smolka, R. Treinen, "Records for Logic Programming", *J. Logic
  Programming* 18(3), 1994.
- R. Treinen, "Feature Constraints with First-Class Features", MFCS 1993,
  LNCS 711.
- R. Backofen, G. Smolka, "A complete and recursive feature theory", *TCS*
  146, 1995.
- H. Aït-Kaci, A. Podelski, "Towards a Meaning of LIFE", *J. Logic
  Programming* 16(3), 1993.
- M. Wand, "Complete Type Inference for Simple Objects", LICS 1987.
- D. Rémy, "Type Inference for Records in a Natural Extension of ML", in
  *Theoretical Aspects of Object-Oriented Programming*, MIT Press, 1993.
- B. R. Gaster, M. P. Jones, "A Polymorphic Type System for Extensible Records
  and Variants", Tech. rep. NOTTCS-TR-96-3, Nottingham, 1996.
- D. Leijen, "Extensible Records with Scoped Labels", TFP 2005.
- D. Kapur, P. Narendran, "NP-completeness of the set unification and matching
  problems", CADE-8, 1986.
- A. Dovier, E. G. Omodeo, E. Pontelli, G. Rossi, "{log}: A language for
  programming in logic with finite sets", *J. Logic Programming* 28(1), 1996.
- A. Dovier, C. Piazza, E. Pontelli, G. Rossi, "Sets and Constraint Logic
  Programming", *ACM TOPLAS* 22(5), 2000.
- A. Dovier, E. Pontelli, G. Rossi, "Set Unification", *TPLP* 6, 2006.
- M. Cristiá, G. Rossi, C. Frydman, "Adding Partial Functions to Constraint
  Logic Programming with Sets", *TPLP* 15, 2015.
- G. S. Makanin, "The problem of solvability of equations in a free
  semigroup", *Math. USSR-Sbornik* 32(2), 1977.
- W. Plandowski, "Satisfiability of word equations with constants is in
  PSPACE", *JACM* 51(3), 2004.
- A. Jeż, "Recompression: a simple and powerful technique for word equations",
  *JACM*, 2016.
- V. Ganesh, M. Minnes, A. Solar-Lezama, M. Rinard, "Word Equations with Length
  Constraints: What's Decidable?", HVC 2012.
- K. Schulz, "On Existential Theories of List Concatenation", CSL 1994.
- Y. Sheng et al., "Reasoning About Vectors Using an SMT Theory of Sequences",
  IJCAR 2022.
- C. Alvis et al., "cKanren: miniKanren with Constraints", Scheme Workshop 2011.
- W. E. Byrd, E. Holk, D. P. Friedman, "miniKanren, Live and Untagged: Quine
  Generation via Relational Interpreters", Scheme Workshop 2012.
- W. E. Byrd, M. Ballantyne, G. Rosenblatt, M. Might, "A Unified Approach to
  Solving Seven Programming Problems", ICFP 2017.
- D. P. Friedman, W. E. Byrd, O. Kiselyov, J. Hemann, *The Reasoned Schemer*,
  2nd ed., MIT Press, 2018.
- L. Zhang et al., "Neural Guided Constraint Logic Programming for Program
  Synthesis", NeurIPS 2018.
- D. Rozplokhas, A. Vyatkin, D. Boulytchev, "Certified Semantics for
  Relational Programming", APLAS 2020.
- A. Sanna, W. E. Byrd, N. Amin, "Beyond Cons: Purely Relational Data
  Structures", miniKanren Workshop 2025.
- A. Sanna, W. E. Byrd, N. Amin, "chrKanren: Constraint Handling Rules in a
  Relational Language", ICLP 2026.
- D. Nolen, "Constraints & modes" and "CLP(Set)", core.logic wiki, 2013,
  https://github.com/clojure/core.logic/wiki.
- Difference lists: L. Sterling, E. Shapiro, *The Art of Prolog* *(unchecked)*.
