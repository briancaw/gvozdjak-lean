"""Tiny parser for the constraint/affine syntax that isl prints, with emitters for Python and Lean."""
import re

TOK = re.compile(r"\s*(?:(\d+)|([A-Za-z_][A-Za-z_0-9]*)|(<=|>=|<|>|=|\+|-|\*|/|\(|\)))")

def tokenize(s):
    out = []; i = 0
    s = s.strip()
    while i < len(s):
        m = TOK.match(s, i)
        if not m: raise ValueError("tok %r at %d" % (s, i))
        if m.group(1): out.append(('num', int(m.group(1))))
        elif m.group(2): out.append(('id', m.group(2)))
        else: out.append(('op', m.group(3)))
        i = m.end()
    return out

class P:
    def __init__(self, toks): self.t = toks; self.i = 0
    def peek(self): return self.t[self.i] if self.i < len(self.t) else (None, None)
    def eat(self, kind=None, val=None):
        k, v = self.peek()
        if (kind and k != kind) or (val is not None and v != val): raise ValueError("expected %s %s got %s %s in %s" % (kind, val, k, v, self.t))
        self.i += 1; return v
    def expr(self):
        k, v = self.peek()
        if (k, v) == ('op', '-'):
            self.eat(); a = ('neg', self.term())
        else: a = self.term()
        while self.peek() in (('op', '+'), ('op', '-')):
            op = self.eat()
            b = self.term()
            a = ('add', a, b) if op == '+' else ('sub', a, b)
        return a
    def term(self):
        a = self.factor()
        while True:
            k, v = self.peek()
            if (k, v) == ('op', '*'):
                self.eat(); a = ('mul', a, self.factor())
            elif k == 'id' and v == 'mod':
                self.eat(); d = self.eat('num'); a = ('mod', a, d)
            elif (k == 'id' and v != 'mod' and v not in ('and', 'or')) or (k, v) == ('op', '('):
                a = ('mul', a, self.factor())
            else: break
        return a
    def factor(self):
        k, v = self.peek()
        if k == 'num': self.eat(); return ('num', v)
        if k == 'id' and v == 'floor':
            self.eat(); self.eat('op', '(')
            a = self.factor()
            self.eat('op', '/'); d = self.eat('num'); self.eat('op', ')')
            return ('fdiv', a, d)
        if k == 'id': self.eat(); return ('var', v)
        if (k, v) == ('op', '('):
            self.eat(); a = self.expr(); self.eat('op', ')'); return a
        raise ValueError("factor %s %s in %s" % (k, v, self.t))

def parse_expr(s):
    p = P(tokenize(s)); e = p.expr()
    # isl prints integer-valued rational affine forms as "(expr)/d": the division is exact
    while p.i + 1 < len(p.t) and p.t[p.i] == ('op', '/') and p.t[p.i + 1][0] == 'num':
        e = ('fdiv', e, p.t[p.i + 1][1]); p.i += 2
    if p.i != len(p.t): raise ValueError("trailing in %r" % s)
    return e

def parse_conjunct(s):
    """returns list of (lhs, op, rhs) for a possibly chained comparison"""
    toks = tokenize(s); parts = []; cur = []; ops = []; depth = 0
    for k, v in toks:
        if k == 'op' and v == '(': depth += 1
        if k == 'op' and v == ')': depth -= 1
        if depth == 0 and k == 'op' and v in ('<=', '>=', '<', '>', '='):
            parts.append(cur); cur = []; ops.append(v)
        else: cur.append((k, v))
    parts.append(cur)
    def pe(t):
        p = P(t); e = p.expr()
        if p.i != len(t): raise ValueError("trailing %s" % t)
        return e
    es = [pe(t) for t in parts]
    return [(es[i], ops[i], es[i + 1]) for i in range(len(ops))]

def split_top(s, sep):
    out = []; depth = 0; cur = ""; i = 0
    while i < len(s):
        ch = s[i]
        if ch in "([": depth += 1
        if ch in ")]": depth -= 1
        if depth == 0 and s.startswith(sep, i):
            out.append(cur); cur = ""; i += len(sep); continue
        cur += ch; i += 1
    out.append(cur); return [x.strip() for x in out]

def set_body(s):
    """'{ [q, x, y] : body }' -> body ('' if universe)"""
    s = s.strip(); assert s[0] == '{' and s[-1] == '}', s
    inner = s[1:-1].strip()
    if ':' not in inner: return ""
    return inner.split(':', 1)[1].strip()

def set_conjuncts(s):
    b = set_body(s)
    if b == "": return []
    if "exists" in b or " or " in b: raise ValueError("unsupported set: " + s)
    return split_top(b, " and ")

def ma_exprs(s):
    """'{ [q, x, y] -> [(e1), (e2)] }' -> [e1, e2] strings"""
    inner = s.strip()[1:-1]
    rhs = inner.split('->', 1)[1].strip()
    assert rhs[0] == '[' and rhs[-1] == ']', s
    return split_top(rhs[1:-1], ",")

def py(e):
    k = e[0]
    if k == 'num': return str(e[1])
    if k == 'var': return e[1]
    if k == 'neg': return "(-%s)" % py(e[1])
    if k == 'add': return "(%s + %s)" % (py(e[1]), py(e[2]))
    if k == 'sub': return "(%s - %s)" % (py(e[1]), py(e[2]))
    if k == 'mul': return "(%s * %s)" % (py(e[1]), py(e[2]))
    if k == 'fdiv': return "(%s // %d)" % (py(e[1]), e[2])
    if k == 'mod': return "(%s %% %d)" % (py(e[1]), e[2])
    raise ValueError(e)

def lean(e, ren=lambda v: v.upper()):
    k = e[0]
    if k == 'num': return str(e[1])
    if k == 'var': return ren(e[1])
    if k == 'neg': return "(-%s)" % lean(e[1], ren)
    if k == 'add': return "(%s + %s)" % (lean(e[1], ren), lean(e[2], ren))
    if k == 'sub': return "(%s - %s)" % (lean(e[1], ren), lean(e[2], ren))
    if k == 'mul': return "(%s * %s)" % (lean(e[1], ren), lean(e[2], ren))
    if k == 'fdiv': return "(%s / %d)" % (lean(e[1], ren), e[2])
    if k == 'mod': return "(%s %% %d)" % (lean(e[1], ren), e[2])
    raise ValueError(e)

PYOP = {'<=': '<=', '>=': '>=', '<': '<', '>': '>', '=': '=='}
LEANOP = {'<=': '≤', '>=': '≥', '<': '<', '>': '>', '=': '='}

def conj_py(s):
    return " and ".join("(%s %s %s)" % (py(a), PYOP[o], py(b)) for a, o, b in parse_conjunct(s))

def conj_lean(s):
    return " ∧ ".join("%s %s %s" % (lean(a), LEANOP[o], lean(b)) for a, o, b in parse_conjunct(s))

def atoms(s):
    """split a conjunct into atomic comparisons; equalities stay as one atom"""
    return [(a, o, b) for a, o, b in parse_conjunct(s)]
