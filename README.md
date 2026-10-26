core.logic — relational data fork
====

This is my fork of [clojure/core.logic](https://github.com/clojure/core.logic).
It is about one thing: **making Clojure's own data relational**. miniKanren is at
its best on lists and trees; idiomatic Clojure lives in maps and vectors. This
fork makes maps and vectors first-class relational terms, and keeps a strict
rule: no operation may silently give up. Everything either answers correctly in
every mode, or waits until it can.

The full upstream test suite still passes. Where the fork changes upstream
behaviour, it is listed under [Changes from upstream](#changes-from-upstream).

What's here
----

**Relational maps (done, JVM).** A map in a query can be partly unknown. Every
map relation runs in every direction:

```clojure
(run* [m] (geto m :a 1) (geto m :b 2))
;;=> ((lmap {:b 2, :a 1} | _0))     ;; an open map: these entries, plus unknowns

(run* [m] (assoco m :b 2 {:a 1 :b 2}))
;;=> ({:a 1} {:a 1, :b _0})          ;; m had no :b, or had :b with some value

(run* [m1 m2] (mergeo m1 m2 {:a 1}))
;;=> ([{:a 1} {}] [{} {:a 1}] [{:a _0} {:a 1}])

(run* [k1 k2 v] (== {k1 v k2 v} {:a 1 :b 1}))
;;=> ([:a :b 1] [:b :a 1])           ;; plain maps with unknown keys unify too
```

| Relation | Means |
|---|---|
| `(geto m k v)` | `(get m k)` is `v` |
| `(assoco m k v out)` | `out` is `(assoc m k v)` |
| `(dissoco m k out)` | `out` is `(dissoc m k)` |
| `(mergeo m1 m2 out)` | `out` is `(merge m1 m2)` |
| `(keyso m ks)` / `(valso m vs)` | the keys / values of `m`, in any order |
| `(selectso m ks out)` | `out` is `(select-keys m ks)` |
| `(lmapo m entries rest)` | `m` is `entries` plus a map `rest` without their keys |
| `(lacks-keyo m & ks)` | `m` has none of the keys `ks` |

Plain Clojure maps are relational too: `(== {k 1} {:a 1})` binds `k` to
`:a`, and maps never end up with two equal keys, even when the keys only
become equal later.

**Relational vectors (done, JVM).** A vector that is partly known has a known
front, an unknown middle and a known back, so `conjo`, `peeko` and `popo` work
on the end without searching. Lengths are solved exactly, so vectors whose
lengths can't match fail at once:

```clojure
(run 3 [i v] (ntho v i :x))
;;=> ([0 (lvec [:x] | _0 | [])] [1 (lvec [_0 :x] | _1 | [])] [2 (lvec [_0 _1 :x] | _2 | [])])

(run* [a b] (concato a b [1 2 3]))
;;=> ([[] [1 2 3]] [[1] [2 3]] [[1 2] [3]] [[1 2 3] []])

(run* [x] (fresh [u e]
            (geto {:users [{:name "a"} {:name "b"}]} :users u)
            (geto u 1 e)
            (geto e :name x)))
;;=> ("b")
```

| Relation | Means |
|---|---|
| `(ntho v i x)` | `(nth v i)` is `x` |
| `(counto c n)` | `(count c)` is `n`, for vectors and maps |
| `(conjo c x out)` | `out` is `(conj c x)`: at the back of a vector, the front of a list |
| `(peeko c x)` / `(popo c out)` | `(peek c)` / `(pop c)` |
| `(concato a b out)` | `out` is `a`'s elements, then `b`'s |
| `(subveco v start end out)` | `out` is `(subvec v start end)` |
| `geto`, `assoco` | also on vectors, with an index as key, like `get` and `assoc` |

Vectors keep unifying with lists, as they are `=` in Clojure. See
[the vectors post](docs/blog/04-vectors.md).

**Paths (done, JVM).** `get-in` and `assoc-in` through any mix of maps and
vectors, in every direction:

```clojure
(run* [p] (get-ino {:a {:b 1} :c [1 {:d 1}]} p 1))
;;=> ((:a :b) (:c 0) (:c 1 :d))       ;; every path to 1

(run* [m] (assoc-ino m [:a :b] 1 {:a {:b 1}}))
;;=> (nil {} {:a nil} {:a {}} {:a {:b _0}})   ;; every m assoc-in could start from
```

| Relation | Means |
|---|---|
| `(get-ino m ks v)` | `(get-in m ks)` is `v`, and the path `ks` exists |
| `(assoc-ino m ks v out)` | `out` is `(assoc-in m ks v)`; missing levels become maps, as in Clojure |

**miniKanren parity.** `defrel`, the type constraints `symbolo`, `numbero` and
`stringo`, and `absento`, with faster-miniKanren's semantics: conflicting
types fail while the variable is still unbound.

**Later:** records as data-level types (schema inference run backwards), relational sets, and the
ClojureScript port.

The posts
----

1. [Relational maps](docs/blog/01-relational-maps.md): a tour of the API.
2. [No unsupported behaviour](docs/blog/02-no-unsupported-behaviour.md): why
   the design had to be redone, and how unknown keys, lazy checks and
   suspended goals fit together.
3. [Making it fast](docs/blog/03-making-it-fast.md): from 33 s to 8 ms, and
   what was slow.
4. [Vectors](docs/blog/04-vectors.md): open vectors, and lengths solved
   exactly.
5. [Literature and miniKanren parity](docs/blog/05-literature-and-parity.md):
   where this sits in the research, and what core.logic still lacks.
6. [Towards relational hyperdimensional computing](docs/blog/06-relational-hdc.md):
   the same data structures, encoded as hypervectors.

Using it
----

The fork is not published; it keeps upstream's coordinates. Install it locally:

```
lein install
```

then depend on `[org.clojure/core.logic "1.1.0-SNAPSHOT"]` (or the
`:mvn/version` equivalent). The map relations live in `clojure.core.logic`
itself.

Status: JVM only for now. The ClojureScript namespace does not have the
map or vector relations yet.

Changes from upstream
----

- `conjo` is a relation now, not a constraint that waits for two of its three
  arguments. Run backwards on a map, it also finds the map whose value
  `conj` overwrote: `(conjo p [:b 2] {:a 1 :b 2})` gives `p = {:a 1}` and
  `p = {:a 1 :b _0}`. The variadic form `(conjo c x y ... out)` still works.
- `geto` and `assoco` with an index as key, on a collection whose kind isn't
  known yet, answer for both a map and a vector: `(run* [m] (geto m 0 1))`
  gives `(lmap {0 1} | _0)` and `(lvec [1] | _0 | [])`.
- Plain maps with logic variables as keys unify relationally; upstream
  treated such keys as plain values.

----

Upstream README
====

core.logic
====

A logic programming library for Clojure & ClojureScript. core.logic
offers Prolog-like relational programming, constraint logic
programming, and nominal logic programming for Clojure. At its heart
is an original implementation of miniKanren as described in William
Byrd's dissertation
[Relational Programming in miniKanren: Techniques, Applications, and Implementations](https://www.proquest.com/docview/304903505/E30282E6EF13453CPQ/1)
as well as the extensions described in
[cKanren](https://www.schemeworkshop.org/2011/papers/Alvis2011.pdf) and
[αKanren](http://webyrd.net/alphamk/alphamk.pdf). It
is designed to be easily extended to forms of logic programming beyond
the ones provided.

Releases and dependency information
----

This project follows the version scheme MAJOR.MINOR.PATCH where each component provides some relative indication of the size of the change, but does not follow semantic versioning. In general, all changes endeavor to be non-breaking (by moving to new names rather than by breaking existing names).

Latest stable release: 1.1.1

* [All released versions](https://search.maven.org/#search%7Cgav%7C1%7Cg%3A%22org.clojure%22%20AND%20a%3A%22core.logic%22)
* [Development snapshot version](https://oss.sonatype.org/index.html#nexus-search;gav~org.clojure~core.logic~~~)

[CLI/`deps.edn`](https://clojure.org/reference/deps_and_cli) dependency information:
```clojure
org.clojure/core.logic {:mvn/version "1.1.1"}
```

[Leiningen](https://github.com/technomancy/leiningen/) dependency information:

```
[org.clojure/core.logic "1.1.1"]
```

[Maven](https://maven.apache.org) dependency information:

```
<dependency>
  <groupId>org.clojure</groupId>
  <artifactId>core.logic</artifactId>
  <version>1.1.1</version>
</dependency>
```

Example usage
----

```clojure
(use 'clojure.core.logic)

(run* [q]
  (== q true))  
;;=> (true)
```

Running the tests
----

Assuming you have V8 installed from source:

```
lein cljsbuild once adv
d8 resources/tests.js
```

If you have another JS engine installed use that instead.

Reasoned Schemer
----

If you wish to work through
[The Reasoned Schemer](https://mitpress.mit.edu/books/reasoned-schemer-second-edition) with
core.logic make sure to look over
[this](https://github.com/clojure/core.logic/wiki/Differences-from-The-Reasoned-Schemer)
first.

If you're interested in using core.logic from
[ClojureScript](https://github.com/clojure/clojurescript/) look
[here](https://github.com/clojure/core.logic/wiki/Using-core.logic-with-ClojureScript).

For more information & documentation please consult the
[wiki](https://github.com/clojure/core.logic/wiki).

Differences from core.unify
----

[core.unify](https://github.com/clojure/core.unify) provides a la carte
unification facilities that are not deeply tied into the operation of
a logic engine. While core.logic does provide a similar simple unifier
interface with support for specifying fine-grained constraints, if you
have no need for a logic programming system, core.unify may be a
better fit.

YourKit
----

<img src="https://www.yourkit.com/images/yklogo.png"></img>

YourKit has given an open source license for their profiler, greatly
simplifying the profiling of core.logic performance.

YourKit supports open source projects with its full-featured Java
Profiler.  YourKit, LLC is the creator of <a
href="https://www.yourkit.com/java/profiler/index.jsp">YourKit Java
Profiler</a> and <a
href="https://www.yourkit.com/.net/profiler/index.jsp">YourKit .NET
Profiler</a>, innovative and intelligent tools for profiling Java and
.NET applications.

Developer information
----

* [Bug Tracker](https://clojure.atlassian.net/browse/LOGIC)
* [Continuous Integration](https://github.com/clojure/core.logic/actions/workflows/test.yml)

Copyright and license
----

Copyright © David Nolen, Rich Hickey & contributors.

Licensed under the EPL (see the file epl.html).
