# Making it fast

*My core.logic fork, part 3 of 8.* [Index](README.md) · [← No unsupported behaviour](02-no-unsupported-behaviour.md) · [Vectors →](04-vectors.md)

Once the relations were correct in every mode, I benchmarked each of them at
map sizes 10, 100 and 1000. Some were fine. Some were not:

| Operation, n = 1000 | Before | After |
|---|---|---|
| n × `geto` building an unknown map | 33 s | 8.2 ms |
| `keyso` / `valso` with a given key list | factorial: did not finish at n = 10 | 0.4 ms |
| `mergeo m m` | 465 ms | 0.5 ms |
| `==` with an unknown key into a large map | 97 ms | 1.5 ms |
| `geto` enumerating all keys | 49 ms | 2.3 ms |
| `geto` with a known key | 0.26 ms | 0.013 ms, constant in n |
| `geto` with a missing key | 0.31 ms | 0.05 ms |
| `selectso`, 5 keys | 1.4 ms | 0.17 ms |
| chain of 1000 `assoco` (`run-nc`) | 267 ms | 35–38 ms |

None of the fixes changed what the relations mean. Each one is a case
where the code did the general thing although a cheaper exact thing was
available.

## Constraints that piled up

Each `geto` on an unknown map adds a key to its open part, and the new rest
must lack every key so far. The first version added one constraint per key
to every rest. After n lookups that's O(n²) constraints, each re-checked on
binding: cubic overall, and 33 seconds at n = 1000.

Now every variable carries at most one lacks constraint, holding a persistent
set of keys. A new rest takes over the set and adds one key, so the constraint
store stays linear.

## Factorial when it should be linear

`keyso` says "these are the keys, in any order", and the obvious relational
definition is `permuteo`. With the key list given, `permuteo` searches orderings:
factorial in the length: bare `permuteo` takes seconds at ten keys, and the old
`keyso` built on it didn't finish.

When everything is known, the question is just "same multiset?", one
frequency count. When some elements are unknown, removing them one at a time
branches only where an element is unknown. `permuteo` is left for the one
case that needs it: the key list itself unknown, where every ordering is a
separate answer.

## Not computing what nobody asked for

`geto` was defined through a general "pick" primitive: `m` is `m'` plus
`k → v`. That builds `m'`, the map without `k`. `geto` throws `m'` away. At
n = 1000 that's a 1000-entry copy per lookup. Now the primitive takes "no
remainder wanted" and skips it, and a known key in a plain map is just a
hash lookup.

Splitting a map into known entries and rest copied the entries every time; now
it returns the existing map when nothing changes and merges the smaller side
into the larger otherwise. `mergeo` of two fully known maps is now a plain
`merge`. Unification with unknown keys matches all the known keys in one
pass, and only searches over the unknown ones.

## Chains

The last one was the most interesting. Growing an open map one key at a time
builds a chain:

```
m → (lmap {:k0 0} | r1)
r1 → (lmap {:k1 1} | r2)
r2 → (lmap {:k2 2} | r3)
...
```

Every later lookup on `m` walks the whole chain to see all the keys. n
lookups, each walking up to n links, is quadratic: 176 ms at n = 1000.

This is *path compression*, the old union-find trick. When a lookup walks a
chain longer than one link, it rebinds `m` to the flattened map it just
computed: `m → (lmap {:k0 0 :k1 1 ... :kn n} | rn)`. That's not a new fact, the
two terms are equal under the current substitution, so no constraint needs
to re-run. The next lookup walks one link and one new entry. 176 ms became
8.2 ms, and the growth is linear again.

The intermediate rests stay bound as they were, so anything else that
refers to `r1` still sees the same map.

## What upstream code pays

Little. Programs that never use maps don't reach the relations' code, and
most upstream benchmarks run within noise; queries with many answers pay per
answer ([part 2](02-no-unsupported-behaviour.md)). The occurs-check piggyback
adds two counter reads per binding when the occurs check is on.

Next: [Vectors](04-vectors.md).
