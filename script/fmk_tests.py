"""Generates src/test/clojure/clojure/core/logic/fmk_tests.clj from
faster-miniKanren's test suite (https://github.com/michaelballantyne/faster-minikanren,
MIT license).

Usage: python3 script/fmk_tests.py DIR, with DIR a checkout of faster-miniKanren.

Each test's Scheme code is translated to core.logic. Its expected answers are
kept as faster-miniKanren prints them, and compared after normalising both
sides, in clojure.core.logic.fmk-support."""
import re, sys, json

class Sym(str): pass
class Str(str): pass
class Dot: pass
DOT = Dot()

def tokenize(src):
    toks = re.findall(r'#;|#\\.|"(?:\\.|[^"\\])*"|;[^\n]*|,@|[()\[\]\'`,]|[^\s()\[\]\'`,";]+', src)
    return [t for t in toks if not t.startswith(';')]

def parse(toks):
    out = []
    i = 0
    def read():
        nonlocal i
        t = toks[i]; i += 1
        if t == '#;':
            read(); return read()
        if t in '([':
            lst = []
            while toks[i] not in ')]':
                if toks[i] == '#;':
                    i += 1; read(); continue
                lst.append(read())
            i += 1
            return lst
        if t == "'": return [Sym('quote'), read()]
        if t == '`': return [Sym('quasiquote'), read()]
        if t == ',': return [Sym('unquote'), read()]
        if t == ',@': return [Sym('unquote-splicing'), read()]
        if t.startswith('"'): return Str(json.loads(t))
        if t == '.': return DOT
        if re.fullmatch(r'-?\d+', t): return int(t)
        return Sym(t)
    while i < len(toks):
        if toks[i] == '#;':
            i += 1; read(); continue
        out.append(read())
    return out

RENAME = {'=/=': '!=', '/o': 'divo', '#t': 'true', '#f': 'false'}

def sym(s):
    return RENAME.get(s, s).replace('^', '-hat')

def clj_str(s):
    return json.dumps(s)

def data(x, quasi):
    """Code building the term for quoted (or quasiquoted) datum x."""
    if isinstance(x, list):
        if quasi and len(x) == 2 and x[0] == 'unquote':
            return expr(x[1])
        if len(x) == 0:
            return "'()"
        if DOT in x:
            k = x.index(DOT)
            tail = data(x[k + 1], quasi)
            for e in reversed(x[:k]):
                tail = f"(lcons {data(e, quasi)} {tail})"
            return tail
        if quasi and any(isinstance(e, list) and e and e[0] == 'unquote-splicing' for e in x):
            parts = [expr(e[1]) if isinstance(e, list) and e and e[0] == 'unquote-splicing'
                     else f"(list {data(e, quasi)})" for e in x]
            return f"(apply list (concat {' '.join(parts)}))"
        return "(list " + ' '.join(data(e, quasi) for e in x) + ")"
    if isinstance(x, Str): return clj_str(x)
    if isinstance(x, int): return str(x)
    if x in ('#t', '#f'): return sym(x)
    return f"'{x}"

def body(xs):
    return ' '.join(expr(e) for e in xs)

def expr(x):
    if isinstance(x, list):
        if not x: return "'()"
        h = x[0]
        if h == 'quote': return data(x[1], False)
        if h == 'quasiquote': return data(x[1], True)
        if h == 'run*':
            return f"(run* [{' '.join(map(sym, x[1]))}] {body(x[2:])})"
        if h == 'run':
            return f"(run {expr(x[1])} [{' '.join(map(sym, x[2]))}] {body(x[3:])})"
        if h == 'fresh':
            return f"(fresh [{' '.join(map(sym, x[1]))}] {body(x[2:])})"
        if h in ('conde', 'conda', 'condu'):
            return f"({h} " + ' '.join('[' + body(c) + ']' for c in x[1:]) + ")"
        if h == 'let':
            bs = ' '.join(f"{sym(b[0])} {expr(b[1])}" for b in x[1])
            return f"(let [{bs}] {body(x[2:])})"
        if h == 'defrel':
            return defrel(x)
        if h == 'cons':
            return f"(lcons {expr(x[1])} {expr(x[2])})"
        return "(" + ' '.join(expr(e) for e in x) + ")"
    if isinstance(x, Str): return clj_str(x)
    if isinstance(x, int): return str(x)
    return sym(x)

def defrel(x):
    name, *args = x[1]
    n = sym(name)
    return f"(defrel {n} [{' '.join(map(sym, args))}] {body(x[2:])})"

# --- canonical answers, as faster-miniKanren prints them

CKEYS = {'=/=', 'sym', 'num', 'str', 'absento'}

def show(x):
    if isinstance(x, list):
        if DOT in x:
            k = x.index(DOT)
            tail = x[k + 1]
            head = x[:k]
            # normalise (a . (b c)) to (a b c)
            if isinstance(tail, list):
                return show(head + tail)
            return '(' + ' '.join(show(e) for e in head) + ' . ' + show(tail) + ')'
        if len(x) == 2 and x[0] == 'quote':
            return "(quote " + show(x[1]) + ")"
        return '(' + ' '.join(show(e) for e in x) + ')'
    if isinstance(x, Str): return json.dumps(x)
    if x == '#t': return 'true'
    if x == '#f': return 'false'
    return str(x)

def canon_answer(a):
    if (isinstance(a, list) and len(a) >= 2 and DOT not in a
            and all(isinstance(c, list) and c and c[0] in CKEYS for c in a[1:])):
        v, cs = a[0], a[1:]
    else:
        v, cs = a, []
    atoms = []
    for c in cs:
        k = c[0]
        if k == '=/=':
            for disj in c[1:]:
                atoms.append(['=/='] + [sorted([show(p[0]), show(p[1])]) for p in disj])
        elif k == 'absento':
            for p in c[1:]:
                atoms.append(['absento', show(p[0]), show(p[1])])
        else:
            for v_ in c[1:]:
                atoms.append([k, show(v_)])
    return {'v': show(v), 'cs': atoms}


FILES = ['==-tests', 'symbolo-tests', 'numbero-tests', 'symbolo-numbero-tests',
         'stringo-tests', 'disequality-tests', 'absento-closure-tests',
         'absento-tests', 'test-infer', 'numbers', 'test-numbers']

# Known differences, each checked by hand.
SKIP = {
    'disequality-tests/lexicographic sorting in =/= reification':
        'equivalent constraint in another normal form: (!= (_0 _1) (_1 _2))',
    'absento-tests/test 5':
        'shows (!= (_0 3) (_1 3)) too, which (!= _0 _1) implies',
    'test-numbers/lots of programs to make a 6':
        'run 12 of an infinite stream: another search order gives other answers',
}
UNORDERED = {'disequality-tests/=/=-51'}

HEADER = """;; Generated by script/fmk_tests.py from faster-miniKanren's tests
;; (https://github.com/michaelballantyne/faster-minikanren). Don't edit.
;;
;; faster-miniKanren is MIT licensed, Copyright (c) 2015 William E. Byrd; the
;; arithmetic relations are from The Reasoned Schemer, 2nd ed., Copyright (c)
;; 2018 Daniel P. Friedman, William E. Byrd, Oleg Kiselyov and Jason Hemann.

(ns clojure.core.logic.fmk-tests
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic :exclude [NAMES]]
        [clojure.test :only [deftest]]
        [clojure.core.logic.fmk-support :only [check build-num]]))

(declare NAMES)

"""

def edn(x):
    if isinstance(x, dict):
        return '{' + ' '.join(f':{k} {edn(v)}' for k, v in x.items()) + '}'
    if isinstance(x, list):
        return '[' + ' '.join(edn(e) for e in x) + ']'
    return json.dumps(x)

def main(d, out):
    groups, prelude, names = [], [], set()
    for f in FILES:
        tests = []
        for form in parse(tokenize(open(f'{d}/{f}.scm').read())):
            if isinstance(form, list) and form and form[0] == 'test':
                title = f'{f}/{form[1]}'
                exp = form[3]
                if not (isinstance(exp, list) and exp and exp[0] == 'quote'):
                    tests.append(f';; skipped {title}: its expected answer is computed')
                    continue
                code = expr(form[2])
                names.update(re.findall(r"\(defrel (\S+)", code))
                if title in SKIP:
                    tests.append(f';; skipped {title}: {SKIP[title]}')
                    continue
                expected = edn([canon_answer(a) for a in exp[1]])
                extra = ' :unordered true' if title in UNORDERED else ''
                tests.append(f'(check {json.dumps(title)}\n    {code}\n    {expected}{extra})')
            elif isinstance(form, list) and form and form[0] == 'defrel':
                code = defrel(form)
                names.update(re.findall(r"\(defrel (\S+)", code))
                prelude.append(code)
            elif isinstance(form, list) and form and form[0] in ('load', 'printf', 'define'):
                pass
            else:
                prelude.append(expr(form))
        if tests:
            groups.append((f, tests))
    with open(out, 'w') as o:
        o.write(HEADER.replace('NAMES', ' '.join(sorted(names))))
        for p in prelude:
            o.write(p + '\n\n')
        for f, tests in groups:
            name = 'unify-tests' if f == '==-tests' else f
            close = '\n  )' if tests[-1].startswith(';;') else ')'
            o.write(f'(deftest {name}\n  ' + '\n\n  '.join(tests) + close + '\n\n')

if __name__ == '__main__':
    main(sys.argv[1], 'src/test/clojure/clojure/core/logic/fmk_tests.clj')
