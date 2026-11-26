"""Integer-affine witnesses for the moves: choose as many constraints as there are free layer sizes,
make them tight (up to a small slack), and solve for the layer sizes."""
import sys, os, itertools, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_common import *
import sympy as sp, numpy as np

n, a, b, q, x, y = sp.symbols('n a b q x y')
def lean2sym(sx, env):
    return sp.sympify(sx.replace("^", "**"), locals=env)

def move_sym(j):
    I = INFO[j]; P = I['params']; env = {p: sp.Symbol(p) for p in P}; env.update(n=n, a=a, b=b)
    eqs = []; 
    for c in I['cons']:
        if '≤' in c or '≠' in c: continue
        l, r = c.split(' = ')
        eqs.append(sp.Eq(lean2sym(l, env), lean2sym(r, env)))
    allp = [env[p] for p in P]
    # prefer the layer sizes as the free parameters: solve for the others first
    order = [env[p] for p in P if not p.startswith('k')] + [env[p] for p in P if p.startswith('k')]
    sol = sp.linsolve(eqs, order)
    assert len(sol) == 1, (j, sol)
    tup = list(sol)[0]
    val = {str(v): sp.expand(e) for v, e in zip(order, tup)}
    K = sorted(set().union(*[e.free_symbols for e in tup]) - {n, a, b}, key=str)
    G = []; NE = []
    types = I['types']
    for i, t in enumerate(types[:-1]):
        if t == 'O': G += [val[f"A{i}"], val[f"k{i}"] - val[f"A{i}"], val[f"k{i}"]]
        elif t in ('EL', 'EH'): G += [val[f"k{i}"] - 1, val[f"A{i}"], val[f"B{i}"]]; NE.append(val[f"A{i}"] - val[f"B{i}"])
        G.append(val[f"H{i}"])
    N, s, e = val['N'], val['s'], val['e']
    G += [N - 1, s, e, N - s, N - e, N + 1 - 2 * (s - e), N + 1 - 2 * (e - s), 2 * (s + e) - N, 3 * N - 2 * (s + e)]
    NE.append(s - e)
    return dict(P=P, K=K, val=val, G=[sp.expand(g) for g in G], NE=[sp.expand(g) for g in NE], N=N, se=sp.expand(s + e))

MS = [move_sym(j) for j in range(15)]

def class_subs(c):
    r, pa, pb = c; return {n: 4 * q + r, a: 2 * x + pa, b: 2 * y + pb}

def is_int_affine(ex):
    p = sp.Poly(ex, q, x, y)
    return p.total_degree() <= 1 and all(co.is_integer for co in p.coeffs())

def candidates(j, c, slacks=(0, 1, 2)):
    m = MS[j]; K = m['K']; sub = class_subs(c)
    G = [sp.expand(g.subs(sub)) for g in m['G']]
    out = {}
    if not K:
        return [()]
    for T in itertools.combinations(range(len(G)), len(K)):
        M = sp.Matrix([[G[i].coeff(k) for k in K] for i in T])
        if M.det() == 0: continue
        rest = [G[i] - sum(G[i].coeff(k) * k for k in K) for i in T]
        Minv = M.inv()
        for d in itertools.product(slacks, repeat=len(K)):
            rhs = sp.Matrix([dd - rr for dd, rr in zip(d, rest)])
            solk = Minv * rhs
            solk = [sp.expand(z) for z in solk]
            if all(is_int_affine(z) for z in solk):
                out[tuple(solk)] = 1
    return list(out.keys())

def evaluator(j, c):
    """returns f(kexprs) -> boolean numpy mask over sample arrays"""
    m = MS[j]; sub = class_subs(c)
    G = [sp.expand(g.subs(sub)) for g in m['G']]; NE = [sp.expand(g.subs(sub)) for g in m['NE']]
    N = sp.expand(m['N'].subs(sub)); se = sp.expand(m['se'].subs(sub))
    K = m['K']
    fG = sp.lambdify([q, x, y] + K, G, 'numpy'); fNE = sp.lambdify([q, x, y] + K, NE, 'numpy')
    fN = sp.lambdify([q, x, y] + K, N, 'numpy'); fse = sp.lambdify([q, x, y] + K, se, 'numpy')
    def f(Q, X, Y, kvals):
        ok = np.ones(len(Q), dtype=bool)
        for g in fG(Q, X, Y, *kvals): ok &= (np.asarray(g) + 0 * Q >= 0)
        for g in fNE(Q, X, Y, *kvals): ok &= (np.asarray(g) + 0 * Q != 0)
        Nv = np.asarray(fN(Q, X, Y, *kvals)) + 0 * Q; sev = np.asarray(fse(Q, X, Y, *kvals)) + 0 * Q
        par = np.where((Nv % 4 == 0) | (Nv % 4 == 3), 0, 1)
        ok &= (sev % 2 == par)
        return ok
    return f

def pyvalid(n_, a_, b_):
    return a_ != b_ and 0 <= a_ <= n_ and 0 <= b_ <= n_ and 2 * abs(a_ - b_) <= n_ + 1 and n_ <= 2 * (a_ + b_) <= 3 * n_ and abs(a_ - b_) % 2 == (n_ * (n_ + 1) // 2) % 2
def samples(c, n0=42, ns=70):
    r, pa, pb = c; pts = []
    for nn in range(n0, n0 + ns):
        if nn % 4 != r: continue
        for aa in range(pa, nn + 1, 2):
            for bb in range(aa + 1, nn + 1):
                if bb % 2 == pb and pyvalid(nn, aa, bb): pts.append((nn // 4, aa // 2, bb // 2))
    return pts

if __name__ == "__main__":
    ci = int(sys.argv[1]); c = CLASSES[ci]
    pts = samples(c); Q = np.array([p[0] for p in pts]); X = np.array([p[1] for p in pts]); Y = np.array([p[2] for p in pts])
    unc = np.ones(len(pts), dtype=bool); t0 = time.time(); allc = []
    for j in range(15):
        cs = candidates(j, c); f = evaluator(j, c); K = MS[j]['K']
        good = 0; cov = np.zeros(len(pts), dtype=bool)
        for kv in cs:
            fk = sp.lambdify([q, x, y], list(kv), 'numpy')
            kvals = [np.asarray(z) + 0 * Q for z in fk(Q, X, Y)] if kv else []
            mk = f(Q, X, Y, kvals)
            if mk.any(): good += 1; cov |= mk; allc.append((j, kv, mk))
        unc &= ~cov
        print(j + 1, "cands", len(cs), "useful", good, "covers", int(cov.sum()), "still uncovered", int(unc.sum()), round(time.time() - t0, 1), flush=True)
    print("samples", len(pts), "uncovered", int(unc.sum()))
    if unc.any(): print([pts[i] for i in np.nonzero(unc)[0][:10]])
