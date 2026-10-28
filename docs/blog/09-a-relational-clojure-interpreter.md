# A relational Clojure interpreter

*My core.logic fork, part 9 of 9.* [Index](README.md) · [← Side by side with miniKanren](08-side-by-side-with-minikanren.md)

miniKanren's most famous program is an interpreter. `evalo` relates an
expression to its value, and because it's a relation, it runs backwards:
give it a value and it writes programs. Give it the same unknown on both
sides, `(evalo q q)`, and it writes quines ("miniKanren, Live and
Untagged", Byrd, Holk and Friedman, 2012).

That interpreter is for a little Scheme, and its environment is an
association list. This post builds the same thing for Clojure, on the data
the series made relational: the environment is a relational map, and vector,
map and set literals evaluate to relational vectors, maps and sets. It lives
in `clojure.core.logic.evalo`.

## The language

`(eval-expo expr env val)` holds when `expr` evaluates to `val` in `env`, a
map from symbols to values. `(evalo expr val)` starts from `prim-env`, which
holds the primitives.

- numbers, strings, keywords, `true`, `false`, `nil` and `()` evaluate to
  themselves
- symbols are looked up in the environment
- `quote`, `if` (with or without an else)
- `fn` with one arity and one body, `let` with sequential bindings
- application of fns and primitives, and of keywords, maps and vectors as
  fns, as in Clojure
- vector literals, map literals with constant keys, set literals of
  constants
- primitives: `list`, `vector`, `get`, `assoc`, `conj`, `=`

Shadowing follows Clojure. `quote` and `if` are special forms, so a local
named `if` doesn't change what `(if ...)` means. `fn` and `let` are macros,
and a local of that name shadows them. Primitives are values in the
environment, so they shadow too, and can be passed around.

## Forwards

Every answer below is from running it. Times: one fresh JVM per query, best of 3 to 5 after a warmup run.

```clojure
(run* [v] (evalo '(let [x 1 y [x 2]] {:a y :b (get {:c 3} :c)}) v))
;;=> ({:a [1 2], :b 3})

(run* [v] (evalo '(:b {:a 1 :b 2}) v))     ;;=> (2)
(run* [v] (evalo '({:a 1} :a) v))          ;;=> (1)
```

## Backwards: inputs

Leave part of the environment unknown and the interpreter says what it must
have been. These are the map relations from [part 1](01-relational-maps.md)
doing the work, inside an interpreter:

```clojure
(run* [m] (eval-expo '(get m :a) (env-with {'m m}) 1))
;;=> ((lmap {:a 1} | _0))          ;; any map with 1 at :a

(run* [m] (eval-expo '(assoc m :b 2) (env-with {'m m}) {:a 1 :b 2}))
;;=> ({:a 1} {:a 1, :b _0})        ;; m had no :b, or some :b

(run* [x] (eval-expo '(if x :yes :no) (env-with {'x x}) :no))
;;=> (false nil)                   ;; Clojure's two false values

(run* [k1 k2]
  (keywordo k1) (keywordo k2)
  (eval-expo (list 'get (list 'get 'm k1) k2) (env-with {'m {:a {:b 1} :c 2}}) 1))
;;=> ([:a :b])                     ;; the key path to 1, in 2.5 ms
```

## Backwards: programs

Leave the expression unknown and it writes programs:

```clojure
(run 8 [q] (evalo q 6))
;;=> (6 (quote 6) (if () 6 _0) ((if _0 6 _1) :- (numbero _0))
;;    (if () (quote 6) _0) (let [] 6) ...)
```

`(if () 6 _0)` is right: in Clojure the empty list is true.

It can also find a fn from examples. Ask for a body such that `(fn [m]
body)` maps each input to its output:

| Examples | Body found | Time |
|---|---|---|
| `1` → `[1 1]`, `2` → `[2 2]` | `[m m]` | 36 ms |
| `{:a 1}` → `1`, `{:a 2}` → `2` | `(:a m)` | 33 ms |
| `{:a 1}` → `{:a 1 :b 2}`, `{:a 5}` → `{:a 5 :b 2}` | `('{{:a 1} {:a 1 :b 2}, {:a 5} {:a 5 :b 2}} m)` | 0.2 s |
| the same, with `(absento 1 body) (absento 5 body)` | `{:a (:a m) :b 2}` | 0.27 s |
| the same, also without `:a` | `(assoc m :b 2)` | 2.1 s |

The third answer is a lookup table of the examples: correct, and the
cheapest program there is. Barliman forbids copying the examples into the
program the same way, with `absento`. Given the shape of the call, the
last one takes 5 ms:

```clojure
(run 1 [b]
  (fresh [x y z] (== b (list 'assoc x y z)))
  (eval-expo b (env-with {'m {:a 1}}) {:a 1 :b 2})
  (absento 1 b))      ;; no copying 1 from the answer into a quote
;;=> ((assoc m :b 2))
```

## Quines

A quine in Clojure syntax runs forwards, and evaluates to itself:

```clojure
(def quine '((fn [x] (list x (list 'quote x)))
             '(fn [x] (list x (list 'quote x)))))
(run* [v] (evalo quine v))   ;;=> (quine), in 2.4 ms
```

Searching for one is where this interpreter falls behind:

| Search | Time to the first quine |
|---|---|
| faster-miniKanren's interpreter, in Racket | 2 ms |
| the same interpreter ported to core.logic ([part 5](05-literature-and-parity.md)) | 16 ms |
| this interpreter, body shaped as `(list e1 e2)` | 0.2 s |
| this interpreter, shape `((fn [x] b) 'B)` only | 2.5 s |
| this interpreter, `(evalo q q)` with `q` a call | none: runs out of a 4 GB heap |

Without "a call", `(evalo q q)` answers `()` at once: the empty list
evaluates to itself, as do `nil`, numbers and keywords.

The quine it finds with the shape given is the classic one, in Clojure
syntax, with `x` any symbol other than a primitive's name or `&`:

```clojure
((fn [_0] (list _0 (list (quote quote) _0)))
 (quote (fn [_0] (list _0 (list (quote quote) _0)))))
```

The interpreter in the quine paper, which faster-miniKanren keeps in its
tests, has five forms: `quote`,
`list`, symbols, one-argument application and one-argument `lambda`. This
one has many more ways to build each subexpression: six kinds of
constants, `if`, `let`, any number of arguments, literal vectors, maps and
sets, and data that can be called. A search for a program the size of a
quine pays for that at every node. Most of the extra ways are also cheap ways to cheat:
`({:k E} :k)` is `E` with extra steps, and the search tries those too.

## What the core needed

Building this found gaps in the fork itself, all now fixed with tests:

- **Lists and vectors are `=`, but code tells them apart.** `(f x)` is a
  call and `[f x]` is a vector. The type constraints that `symbolo` uses now
  also know list, vector, map and set, and a var given one of them can't
  later become a number or the other kind of sequence. The map and vector
  relations read the kind, so `geto` on an unknown var known to be a vector
  works on it as a vector.
- **`keywordo`**, next to `symbolo`, `numbero` and `stringo`.
- **Waiting answers that couldn't hold.** `geto` on an unknown map with an
  unknown key waits, because an open map only holds known keys
  ([part 2](02-no-unsupported-behaviour.md)). While waiting, it gave answers
  that have no solution, and the synthesis searches above were full of
  them:
  - two waiting `geto`s of the same key from the same map with different
    values
  - a map whose value at some key contains the map
  - `(absento 1 m)` together with a waiting `geto` that puts `1` into `m`

  Each of these now fails. A waiting `geto` also wakes when its map var is
  unified with another var, so that two waiting `geto`s of the same key
  meet.
- **Searches that never ended.** The first version of this post had fn
  bodies at 0.2–0.5 s, and neither the assoc examples nor the
  `((fn [x] b) 'B)` quine found within minutes. The interpreter barely
  changed for the numbers above. The relations under it had cases that ran
  forever, or overflowed the stack, where they should fail or act, and the
  searches were full of them:
  - an element at an unknown index of an open vector that would have to
    contain the vector, or something `absento` keeps out of it: every
    position was tried, forever
  - two lookups at the same unknown index giving different elements
  - `conjo` on a var already known to be a vector waited instead of
    acting, and chains of those overflowed the stack
  - an `assoc` at an unknown index into a known result gave its answers
    and then never ended
  - `absento` scanned every constraint in the store on every call

  Each now fails or acts at once, as the map relations already did. Every
  one broke the rule of [part 2](02-no-unsupported-behaviour.md), outside
  the interpreter too.

## What's slow or missing

- **The unshaped quine search.** `(evalo q q)` with only "q is a call"
  fills a 4 GB heap before it finds one. Every var under a `quote` carries
  a constraint that keeps fn values out of quoted data, and the search makes
  millions of them. faster-miniKanren's interpreters also get their speed
  from a small language and a carefully ordered search; this one has
  neither yet.
- **Answers that wait.** A program that applies a keyword not yet chosen to
  unknown quoted data, `(_0 '_1)`, gives an answer with a waiting `geto`, since neither the map
  nor the key is known. These are correct, as conditions, but they aren't
  programs you'd write.
- **Left out of the language:** `def`, `do`, `loop`/`recur`, multi-arity
  and variadic fns, destructuring, more than one body expression, map keys
  and set elements that aren't constants, chars, and the rest of
  `clojure.core`. An expression outside the subset fails in every mode.
- **Where it differs from Clojure,** it fails where Clojure returns nil:
  `get` with an index a vector lacks or a key on a vector that is neither
  an index nor a keyword, `get` on a list, `assoc` on nil.
  `=` fails on fns, which Clojure compares by identity.
