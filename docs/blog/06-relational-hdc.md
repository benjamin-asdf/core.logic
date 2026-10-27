# Towards relational hyperdimensional computing

*My core.logic fork, part 6 of 8.* [Index](README.md) · [← Where this sits: the literature, and parity with miniKanren](05-literature-and-parity.md) · [Sets →](07-sets.md)

> Draft. This is a design sketch, not an implementation.

The data structures this fork makes relational are maps, sequences and,
later, sets. They're also exactly the structures that hyperdimensional
computing (HDC, or vector symbolic architectures) knows how to encode:

| Structure | Logic term in this fork | Hypervector encoding |
|---|---|---|
| set | (planned) | bundle: `a + b + c` |
| map / record | `(lmap {k v ...} \| r)` | bundle of bindings: `k1⊗v1 + k2⊗v2 + ...` |
| sequence | `[f \| m \| b]` | bundle of permuted items: `ρ⁰(x0) + ρ¹(x1) + ...`, or nested binding with position vectors |
| open part | rest variable | an unknown summand: noise you haven't identified |

`get` on a record is unbinding and cleanup: `k⊗(k1⊗v1 + k2⊗v2) ≈ v1 + noise`
when `k = k1` and binding is self-inverse, and a nearest-neighbour search
against the codebook recovers `v1`. That is already a lookup that runs in
more than one direction: you can unbind by the value to ask which key holds
it. HDC's operations are naturally relational. What's missing is a
framework that treats them that way.

## The operations as relations

**Binding** is the clean case. With a self-inverse binding (elementwise
multiplication of bipolar vectors in MAP, XOR in binary spatter codes),
`c = a ⊗ b` determines any one of the three from the other two, exactly. So
`(bindo a b c)` is a relation in every mode with two known arguments, the way
`pluso` is in CLP(FD). With one or none known it waits. In HRR (circular
convolution) the inverse is approximate, and the relation with it.

**Permutation** is a bijection, so `(permo x n y)` is exact in all modes with
`n` known, and with `n` unknown enumerates or waits.

**Bundling** is the interesting one. `s = a + b + c` doesn't determine its
summands. Run backwards, `(bundleo xs s)` asks "which items are in this
superposition?". That's a search. The answers are candidates ranked by
similarity, not a fixed set.

**Cleanup**, `(cleanupo codebook noisy x)`, relates a noisy vector to the
codebook items it's close to. It enumerates them in order of similarity.

**Factorisation**, `s = a ⊗ b ⊗ c` with all three unknown but each from a
codebook, is what resonator networks solve (Frady, Kent, Olshausen and
Sommer, 2020). In logic terms a resonator network is a *constraint solver*
for a conjunction of `bindo` and `cleanupo` goals: it propagates estimates
until they settle. That suggests plugging it in the way CLP(FD) is plugged
into core.logic: a constraint domain with its own propagator.

## Two designs

**A. Hypervectors as a constraint domain.** Logic variables range over
hypervectors, like FD variables range over integers. `bindo`, `permo` and
`bundleo` are constraints. Exact operations propagate as soon as enough is
known. Approximate ones (bundling backwards, cleanup, factorisation) branch
over ranked candidates, or run a resonator network as the domain's solver.

**B. Hypervectors as an oracle for symbolic search.** The symbolic terms
stay the truth: maps, vectors, exact unification. Every term also has an
encoding, `(encodeo term hv)`, and the search uses similarity to *order*
its branches: `geto` on an unknown key tries keys in order of how well they
unbind against a hypervector you hold. Answers are still verified
symbolically, so they're never wrong, only found sooner or later. This is
the same move as neural-guided miniKanren, with HDC as the guide.

B is the safer first step. It keeps this fork's rule, that answers are
never silently wrong, because HDC only decides *order*. A changes the
semantics: equality becomes similarity above a threshold, and that isn't
transitive. `a ≈ b` and `b ≈ c` don't give `a ≈ c`, so it can't be the
equivalence a substitution needs. A needs a separate notion of answer, such
as answers that are approximately true with a confidence attached.

## Where the open maps fit

An open map `(lmap {:a 1} | r)` and a record hypervector with an unknown
remainder have the same shape: known bindings, plus a summand you haven't
identified. In HDC the remainder shows up as noise when you unbind a
known key. The lacks constraint ("`r` has no `:a`") becomes "unbinding `r` by
`:a` gives nothing close to any codebook item": a probabilistic absence.

Capacity is the price. A bundle of `n` items in `D` dimensions recovers
items reliably only while `n` is small relative to `D`, so "the rest holds
anything" isn't free the way an unbound variable is.

## Search that knows how close it is

miniKanren's interleaving search is fair but blind: it takes branches in
order. HDC gives every branch a score. A relational HDC framework would want
streams of answers ordered by score, best-first rather than breadth-first,
with miniKanren's completeness kept as a fallback: low-scored branches are
postponed, never dropped.

## Questions to settle

- **Which family?** MAP or BSC, with exact self-inverse binding, makes
  `bindo` exact. HRR and FHRR give continuous similarity but approximate
  inverses.
- **Codebooks as relations.** A codebook is a fact table: a `pldb` relation
  from symbols to hypervectors. Seeded, so reruns are reproducible.
- **Learning.** Asking which codebook makes these encodings match is
  relational learning run backwards. Is that in scope, or does the framework
  assume fixed codebooks?
- **Exact vs approximate answers.** Design B keeps answers exact. Design A
  needs graded answers. Can both live in one `run`?
- **Who orders the search?** Design B can order branches inside a goal,
  for example by sorting the alternatives of a `conde` by score. A global
  best-first search over all open branches needs the search tree as data. In
  core.logic the stream is made of closures, which an outside guide can't
  inspect, and neural-guided miniKanren ran into the same constraint.
- **Where resonator networks sit.** As a core.logic constraint domain, a
  custom stream, or an external solver behind a single goal?

## References

- T. A. Plate, *Holographic Reduced Representations*, CSLI Publications, 2003.
- P. Kanerva, "Hyperdimensional Computing: An Introduction to Computing in
  Distributed Representation with High-Dimensional Random Vectors",
  *Cognitive Computation* 1, 2009.
- R. W. Gayler, "Vector Symbolic Architectures answer Jackendoff's challenges
  for cognitive neuroscience", ICCS/ASCS Joint International Conference on
  Cognitive Science, 2003.
- E. P. Frady, S. J. Kent, B. A. Olshausen, F. T. Sommer, "Resonator Networks,
  1: An Efficient Solution for Factoring High-Dimensional, Distributed
  Representations of Data Structures", *Neural Computation* 32(12), 2020.
- D. Kleyko, D. A. Rachkovskij, E. Osipov, A. Rahimi, "A Survey on
  Hyperdimensional Computing aka Vector Symbolic Architectures", *ACM
  Computing Surveys*, 2022/2023 (two parts).
