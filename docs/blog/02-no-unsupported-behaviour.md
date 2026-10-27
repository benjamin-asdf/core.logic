# No unsupported behaviour

*My core.logic fork, part 2 of 8.* [Index](README.md) · [← Relational maps for core.logic](01-relational-maps.md) · [Making it fast →](03-making-it-fast.md)

The first version of relational maps in this fork worked for the queries I
had in mind. When I went through it systematically, mode by mode, it had gaps:
combinations of known and unknown arguments where a relation gave up, or
answered for one case and silently dropped the others.

In a relational library that's not a small problem. The whole point of a
relation is that you don't have to know which direction it runs in. If
`assoco` works backwards *except when*, every caller has to know the
exception, and then it isn't a relation, it's a function with a few extra
modes.

So the rule became: **no unsupported behaviour.** Each relation is correct in
every mode: it answers, fails, or waits and says what it's waiting for. If
that made everything slow, the design had to change, not the rule.

It did change. This post is about the design that came out.

## Three kinds of map

There are three things a map can be in a query, and keeping them apart is
most of the design.

1. **A plain map with plain keys**: `{:a x :b 2}`. Values may be unknown, keys
   are fixed values. That's the common case and it has to stay as fast as
   upstream.
2. **A plain map with unknown keys**: `{k 1 :b 2}`. Clojure allows any value
   as a key, so in a query a key can be a logic variable, or a term
   containing one. Such a map is *closed*: it has exactly these entries.
3. **An open map**, `(lmap {:a 1} | r)`: known entries plus an unknown rest.

The key invariant: **open maps only have ground keys.** Users never write
open maps directly; only the library's relations create them, and they only
put fixed keys in. Unknown keys exist only in closed plain maps.

That one restriction removes the hardest case: an open map whose keys are
unknown would mean every unknown key might match any entry of any rest, an
unbounded search. With the restriction, open maps are cheap: lookups are
hash lookups, and the rest only grows at the end.

Every open map's rest carries a *lacks* constraint: the rest of
`(lmap {:a 1} | r)` must never get `:a`. That's what keeps "entries plus rest" a
disjoint union, and what makes `(lacks-keyo m :a)` mean something even
before `m` is known.

## Unifying maps with unknown keys

`(== {k1 v k2 v} {:a 1 :b 1})` has two answers: `k1 = :a, k2 = :b` and the
other way round. Unification in core.logic is a function from a substitution
to a substitution or `nil`. It can't return two.

The options were to push the branching into the search (turn unification
into a goal), or to keep unification a function and defer. I did both,
depending on the case:

- Run the matching as a goal on a clean copy of the state and ask for **two**
  answers.
- **None:** unification fails.
- **One:** commit to it. That's the common case, `{k 1 :b 2}` against `{:a 1 :b 2}`,
  and it costs no search at all: no choice point is left behind.
- **Two or more:** the unification really is ambiguous. Keep it as a
  pending constraint that re-runs when one of its variables is bound. Before
  an answer is reified, any constraint still ambiguous is *forced*: its
  alternatives are enumerated as ordinary search branches.

So deterministic cases stay deterministic, and ambiguity becomes search
only when it can't be avoided. Waiting also means later goals often
decide which pairing holds, and the other branches are never explored.

The same mechanism handles relations that can't proceed. `geto` on an
unknown map with an unknown key has infinitely many answers, so it suspends
until the map or the key becomes known. If neither happens, it comes out in
the answer as a constraint.

## Keys must stay distinct

A Clojure map never has two equal keys. In a query it can get them: build
`{k1 1 k2 2}` while `k1` and `k2` are unbound, then bind both to `:a`. Now the
"map" has `:a` twice, which no Clojure map can, so that branch has to fail.

The obvious fix, a constraint on every map with unknown keys re-checked on
every binding, was expensive: every unification would have to ask whether it
touched such a map.

The trick: core.logic **already walks every term it binds a variable to**,
for the occurs check. That walk now also notes any map with non-plain keys
it passes, by bumping a counter, which costs nearly nothing on the common
path. After binding, if the counter moved, those maps get their keys checked,
and a constraint keeps them distinct from then on.

In `run-nc` (no occurs check) the walk doesn't happen. There, collisions are
caught when the answer is reified: walking the map back into a Clojure map
would merge equal keys, so the reified map comes out smaller than the term,
and that answer is dropped. The trade-off is that `run-nc` only checks the
maps that appear in an answer. That's in keeping with what `run-nc` already
is: an opt-out of checks for speed, trusted to be used on terms where it's
safe.

## Rests that are copied

Tabling and `copy-term` copy terms with fresh variables. An open map's rest
copied to a fresh variable would lose its lacks constraint, and with it the
disjointness. Both now re-attach the constraints to copied rests.

## What it costs

Upstream benchmarks (zebra, nrev, n-queens, sudoku and others) run within
noise of upstream. One microbenchmark of unifying tiny maps is a few percent
slower. The relations themselves had problems of their own:
[Making it fast](03-making-it-fast.md).
