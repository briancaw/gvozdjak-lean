"""Generate Gvozdjak/Reduction<class>.lean: explicit witnesses for the reduction theorem.

For each residue class (n mod 4, a mod 2) write n = 4q+r, a = 2x+pa, b = 2y+pb.
Witnesses are integer-affine formulas in (q,x,y) for the parameters of a move (found by making
as many constraints tight as there are free layer sizes).  isl computes the exact region on which
each formula is valid; a small family of regions covering all admissible triples with n >= 42 is
selected, and a case tree is built whose leaves each lie inside one region.  isl only *finds* the
formulas and the tree; Lean re-checks every step.
"""
import sys, time, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_common import *
import islparse as ip
import wit_affine as wa
import sympy as sp, numpy as np
from gen_reduction import isl_e, atom_isl, atom_py, atom_lean, aset, nset, split_atoms, Tree, build, emit_tree

N0 = 42
q, x, y = wa.q, wa.x, wa.y

def lin_lean(ex):
    p = sp.Poly(sp.expand(ex), q, x, y)
    cq, cx, cy, c0 = [int(p.coeff_monomial(m)) for m in (q, x, y, 1)]
    def lit(v): return str(v) if v >= 0 else f"({v})"
    terms = [f"{lit(cv)} * {nm}" for cv, nm in ((cq, 'Q'), (cx, 'X'), (cy, 'Y')) if cv != 0]
    if c0 != 0 or not terms: terms.append(lit(c0))
    return "(" + " + ".join(terms) + ")"
def lin_isl(ex):
    p = sp.Poly(sp.expand(ex), q, x, y)
    cq, cx, cy, c0 = [int(p.coeff_monomial(m)) for m in (q, x, y, 1)]
    return f"({cq}*q + {cx}*x + {cy}*y + {c0})"

def full_witness(j, c, kv):
    m = wa.MS[j]; sub = wa.class_subs(c)
    ksub = {k: v for k, v in zip(m['K'], kv)}
    return {p: sp.expand(m['val'][p].subs(ksub).subs(sub)) for p in m['P']}

def exact_domain(j, c, W):
    I = INFO[j]; P = I['params']
    cons = [lean2isl(cc) for cc in I['cons']] + [validstr('N', 's', 'e')] + [f"{p} = {lin_isl(W[p])}" for p in P] + [f"{p} >= 0" for p in P]
    return isl.Set("{ [q,x,y] : exists (n,a,b," + ",".join(P) + ": " + class_sub(c) + " and " + " and ".join(cons) + ") }").coalesce()

def pieces_of(j, c, kv):
    W = full_witness(j, c, kv); D = exact_domain(j, c, W); out = []
    for bs in D.get_basic_sets():
        sbs = str(bs)
        try: ats = split_atoms(ip.set_conjuncts(sbs))
        except Exception as ex:
            try:
                for bs2 in isl.Set.from_basic_set(bs).compute_divs().get_basic_sets():
                    ats = split_atoms(ip.set_conjuncts(str(bs2))); out.append((bs2, ats))
            except Exception as ex2: raise Exception("cannot parse domain " + sbs)
            continue
        out.append((bs, ats))
    res = []
    for bs, ats in out:
        dom = isl.Set.from_basic_set(bs)
        re_dom = isl.Set("{ [q,x,y] : %s }" % (" and ".join(atom_isl(a_) for a_ in ats) if ats else "1 = 1"))
        assert re_dom.is_equal(dom), (str(bs))
        f = eval("lambda q,x,y: " + (" and ".join(atom_py(a_) for a_ in ats) if ats else "True"))
        res.append(dict(j=j, dom=dom, atoms=ats, W=W, f=f))
    return res

def gen_class(c, ns):
    t0 = time.time(); r, pa, pb = c; cname = f"{r}{pa}"
    V = Vc(c, N0).coalesce()
    pts = wa.samples(c, N0, ns)
    Q = np.array([p[0] for p in pts]); X = np.array([p[1] for p in pts]); Y = np.array([p[2] for p in pts])
    allc = []; evals = {}; candlist = {}
    for j in range(15):
        cs = wa.candidates(j, c); f = wa.evaluator(j, c); evals[j] = f; candlist[j] = cs
        for kv in cs:
            fk = sp.lambdify([q, x, y], list(kv), 'numpy')
            kvals = [np.asarray(z) + 0 * Q for z in fk(Q, X, Y)] if kv else []
            mk = f(Q, X, Y, kvals)
            if mk.any(): allc.append((j, kv, mk))
    print(f"class {c}: {len(allc)} useful candidate formulas, {len(pts)} samples, {time.time()-t0:.0f}s", flush=True)
    unc = np.ones(len(pts), dtype=bool); chosen = []
    while unc.any():
        best = max(range(len(allc)), key=lambda i: (int((allc[i][2] & unc).sum()), -allc[i][0]))
        if not (allc[best][2] & unc).any(): raise Exception("uncoverable sample")
        chosen.append((allc[best][0], allc[best][1])); unc &= ~allc[best][2]
    pcs = []
    for j, kv in chosen: pcs += pieces_of(j, c, kv)
    rem = V
    for pc in pcs: rem = rem.subtract(pc['dom'])
    rem = rem.coalesce(); extra = 0
    while not rem.is_empty():
        pt = rem.sample_point()
        p = tuple(int(str(pt.get_coordinate_val(isl.dim_type.set, k))) for k in range(3))
        Q1, X1, Y1 = (np.array([v]) for v in p); found = None
        for j in range(15):
            for kv in candlist[j]:
                fk = sp.lambdify([q, x, y], list(kv), 'numpy')
                kvals = [np.asarray(z) + 0 * Q1 for z in fk(Q1, X1, Y1)] if kv else []
                if evals[j](Q1, X1, Y1, kvals)[0]: found = (j, kv); break
            if found: break
        if not found: raise Exception("no affine witness at %s" % (p,))
        new = pieces_of(*((found[0], c, found[1])))
        pcs += new; extra += 1
        for pc in new: rem = rem.subtract(pc['dom'])
        rem = rem.coalesce()
    # tree
    st = Tree(); cands = pcs; used = list(range(len(pcs)))
    tree = build(V, list(range(len(pts))), pts, used, cands, st)
    usedleaf = set()
    def collect(t):
        if t[0] == 'leaf': usedleaf.add(t[1])
        else: collect(t[2]); collect(t[3])
    collect(tree)
    print(f"class {c}: formulas {len(chosen)}+{extra}, regions {len(pcs)}, used {len(usedleaf)}, leaves {st.leaves}, depth {st.maxdepth}, {time.time()-t0:.0f}s", flush=True)
    vbs = V.get_basic_sets(); assert len(vbs) == 1
    vats = split_atoms(ip.set_conjuncts(str(vbs[0])))
    _order = ["00", "01", "10", "11", "20", "21", "30", "31"]; _i = _order.index(cname)
    imp = "import Gvozdjak.Moves" if _i == 0 else f"import Gvozdjak.Reduction{_order[_i-1]}  -- chained so the classes compile one at a time"
    out = [f"/-\nReduction, residue class n ≡ {r} (mod 4), a ≡ {pa} (mod 2).  GENERATED by scripts/gen_reduction2.py.\n\nEach `p{cname}_i` gives explicit parameters of one move on a region of (q, x, y), where\nn = 4q + {r}, a = 2x + {pa}, b = 2y + {pb}; `cover{cname}` is a case tree whose leaves each lie in one region.\n-/\n{imp}\n\nnamespace Gvozdjak\n\nset_option maxHeartbeats 1000000\n"]
    for i in sorted(usedleaf):
        cd = cands[i]; j = cd['j']; P = INFO[j]['params']
        dom = " ∧ ".join(atom_lean(a_) for a_ in cd['atoms']) if cd['atoms'] else "True"
        L = [f"theorem p{cname}_{i} (n a b q x y : Nat) (Q X Y : Int) (hQ : Q = q) (hX : X = x) (hY : Y = y)",
             f"    (hn : n = 4 * q + {r}) (ha : a = 2 * x + {pa}) (hb : b = 2 * y + {pb})",
             f"    (hD : {dom}) : Red n a b := by"]
        for p in P:
            wl = lin_lean(cd['W'][p])
            L.append(f"  obtain ⟨{p}, h{p}⟩ : ∃ {p} : Nat, ({p} : Int) = {wl} := ⟨Int.toNat {wl}, by omega⟩")
        L.append(f"  exact Red.m{j+1} {' '.join(P)} (by unfold C{j+1}; omega) (by unfold AdmL; omega)")
        out.append("\n".join(L) + "\n")
    L = [f"theorem cover{cname} (n a b q x y : Nat) (hn : n = 4 * q + {r}) (ha : a = 2 * x + {pa})",
         f"    (hb : b = 2 * y + {pb}) (h42 : 42 ≤ n) (hab : a < b) (hadm : AdmL a b n) : Red n a b := by",
         "  obtain ⟨Q, hQ⟩ : ∃ Q : Int, Q = q := ⟨_, rfl⟩",
         "  obtain ⟨X, hX⟩ : ∃ X : Int, X = x := ⟨_, rfl⟩",
         "  obtain ⟨Y, hY⟩ : ∃ Y : Int, Y = y := ⟨_, rfl⟩",
         "  unfold AdmL at hadm"]
    for k, at in enumerate(vats): L.append(f"  have v{k} : {atom_lean(at)} := by omega")
    L.append("  clear hadm h42 hab")
    emit_tree(tree, cname, 1, L)
    out.append("\n".join(L) + "\n"); out.append("end Gvozdjak\n")
    return "\n".join(out)

if __name__ == "__main__":
    outdir = sys.argv[1]; which = [int(z) for z in sys.argv[2].split(",")]
    ns = int(os.environ.get("NS", "70"))
    for ci in which:
        c = CLASSES[ci]
        open(os.path.join(outdir, f"Reduction{c[0]}{c[1]}.lean"), "w").write(gen_class(c, ns))
