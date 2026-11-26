"""Generate Gvozdjak/Reduction*.lean: explicit witnesses for the reduction theorem.

For each residue class (n mod 4, a mod 2) write n = 4q+r, a = 2x+pa, b = 2y+pb.
isl supplies, for each move, regions of (q,x,y) on which explicit affine formulas give valid
parameters.  A small family of such regions covering all admissible triples with n >= 42 is
selected, and a case tree is built whose leaves each lie inside one region.  isl is only used
to *find* the formulas and the tree; Lean re-checks every step with `omega`.
"""
import sys, time, pickle, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_common import *
import islparse as ip

N0 = 42
import collections
STATS = collections.Counter()
NS = int(os.environ.get("NS", "70"))

def isl_e(e):
    k = e[0]
    if k == 'num': return str(e[1])
    if k == 'var': return e[1]
    if k == 'neg': return "(-%s)" % isl_e(e[1])
    if k == 'add': return "(%s + %s)" % (isl_e(e[1]), isl_e(e[2]))
    if k == 'sub': return "(%s - %s)" % (isl_e(e[1]), isl_e(e[2]))
    if k == 'mul': return "(%s * %s)" % (isl_e(e[1]), isl_e(e[2]))
    if k == 'fdiv': return "floor((%s)/%d)" % (isl_e(e[1]), e[2])
    if k == 'mod': return "((%s) mod %d)" % (isl_e(e[1]), e[2])
def atom_isl(at):
    a, o, b = at; return "%s %s %s" % (isl_e(a), o, isl_e(b))
def atom_py(at):
    a, o, b = at; return "(%s %s %s)" % (ip.py(a), ip.PYOP[o], ip.py(b))
def atom_lean(at):
    a, o, b = at; return "%s %s %s" % (ip.lean(a), ip.LEANOP[o], ip.lean(b))
def aset(at): return isl.Set("{ [q,x,y] : %s }" % atom_isl(at))
def nset(at): return isl.Set("{ [q,x,y] : not (%s) }" % atom_isl(at))
def has_floor(e): return e[0] in ('fdiv', 'mod') or any(isinstance(z, tuple) and has_floor(z) for z in e[1:])

def split_atoms(conjs):
    """atoms of a conjunction; a plain equality a = b becomes a <= b, a >= b"""
    out = []
    for s in conjs:
        for (a, o, b) in ip.atoms(s):
            if o == '=' and not (a[0] == 'mod' or b[0] == 'mod'):
                out.append((a, '<=', b)); out.append((a, '>=', b))
            else: out.append((a, o, b))
    return out

def candidates(c):
    cands = []
    for j in range(15):
        M = move_map_c(j, c)
        for bm in M.get_basic_maps():
            pma = isl.PwMultiAff.from_map(bm.lexmin())
            pcs = []
            pma.foreach_piece(lambda s, ma: pcs.append((s, ma)))
            for s, ma in pcs:
                try: w = [ip.parse_expr(z) for z in ip.ma_exprs(str(ma))]
                except Exception as ex: continue
                bsl = []
                for bs in s.get_basic_sets():
                    if "exists" in str(bs):
                        try: bsl += isl.Set.from_basic_set(bs).compute_divs().get_basic_sets()
                        except Exception as ex: STATS['cdfail'] += 1
                    else: bsl.append(bs)
                for bs in bsl:
                    try: ats = split_atoms(ip.set_conjuncts(str(bs)))
                    except Exception as ex:
                        STATS['setfail'] += 1; continue
                    dom = isl.Set(str(bs))
                    # sanity: our re-emitted atoms describe the same set
                    re_dom = isl.Set("{ [q,x,y] : %s }" % (" and ".join(atom_isl(a) for a in ats) if ats else "1 = 1"))
                    if not re_dom.is_equal(dom):
                        STATS['remis'] += 1; continue
                    f = eval("lambda q,x,y: " + (" and ".join(atom_py(a) for a in ats) if ats else "True"))
                    cands.append(dict(j=j, dom=dom, atoms=ats, w=w, f=f,
                                      cost=len(ats) + 3 * sum(has_floor(a[0]) or has_floor(a[2]) for a in ats) + sum(has_floor(z) for z in w)))
    return cands

def pyvalid(n, a, b):
    return a != b and 0 <= a <= n and 0 <= b <= n and 2 * abs(a - b) <= n + 1 and n <= 2 * (a + b) <= 3 * n and abs(a - b) % 2 == (n * (n + 1) // 2) % 2

def samples(c):
    r, pa, pb = c; pts = []
    for n in range(N0, N0 + NS):
        if n % 4 != r: continue
        for a in range(pa, n + 1, 2):
            for b in range(a + 1, n + 1):
                if b % 2 == pb and pyvalid(n, a, b): pts.append((n // 4, a // 2, b // 2))
    return pts

def select(c, cands, pts, V):
    cov = []
    for cd in cands:
        f = cd['f']; cov.append(set(i for i, p in enumerate(pts) if f(*p)))
    unc = set(range(len(pts))); chosen = []
    while unc:
        best = max(range(len(cands)), key=lambda i: (len(cov[i] & unc), -cands[i]['cost']))
        if not (cov[best] & unc): raise Exception("uncoverable sample %s" % (pts[next(iter(unc))],))
        chosen.append(best); unc -= cov[best]
    rem = V
    for i in chosen: rem = rem.subtract(cands[i]['dom'])
    rem = rem.coalesce(); extra = 0
    while not rem.is_empty():
        pt = rem.sample_point()
        p = tuple(int(str(pt.get_coordinate_val(isl.dim_type.set, k))) for k in range(3))
        opts = [i for i, cd in enumerate(cands) if cd['f'](*p)]
        if not opts: raise Exception("no candidate for %s" % (p,))
        best = min(opts, key=lambda i: cands[i]['cost'])
        chosen.append(best); rem = rem.subtract(cands[best]['dom']).coalesce(); extra += 1
    return chosen, extra

class Tree:
    def __init__(self): self.leaves = 0; self.nodes = 0; self.maxdepth = 0

def build(R, sidx, pts, chosen, cands, st, depth=0):
    st.maxdepth = max(st.maxdepth, depth)
    # rank chosen pieces by sample overlap
    if sidx:
        ranked = sorted(chosen, key=lambda i: -sum(1 for s in sidx if cands[i]['f'](*pts[s])))
    else:
        ranked = list(chosen)
    for i in ranked[:6]:
        if R.is_subset(cands[i]['dom']):
            st.leaves += 1; return ('leaf', i)
    P = None
    for i in ranked:
        if not R.intersect(cands[i]['dom']).is_empty(): P = i; break
    if P is None: raise Exception("region not covered: " + str(R)[:300])
    for at in cands[P]['atoms']:
        Rn = R.intersect(nset(at))
        if Rn.is_empty(): continue
        Rp = R.intersect(aset(at))
        f = eval("lambda q,x,y: " + atom_py(at))
        sp = [s for s in sidx if f(*pts[s])]; sn = [s for s in sidx if not f(*pts[s])]
        st.nodes += 1
        return ('node', at, build(Rp.coalesce(), sp, pts, chosen, cands, st, depth + 1),
                build(Rn.coalesce(), sn, pts, chosen, cands, st, depth + 1))
    # all atoms hold on R, so R is inside the piece
    st.leaves += 1; return ('leaf', P)

def emit_tree(t, cname, ind, out):
    pad = "  " * ind
    if t[0] == 'leaf':
        out.append(f"{pad}exact p{cname}_{t[1]} n a b q x y Q X Y hQ hX hY hn ha hb (by first | omega | lia | trivial)")
    else:
        out.append(f"{pad}by_cases h : {atom_lean(t[1])}")
        out.append(f"{pad}·"); emit_tree(t[2], cname, ind + 1, out)
        out.append(f"{pad}·"); emit_tree(t[3], cname, ind + 1, out)

def gen_class(ci, c):
    t0 = time.time()
    r, pa, pb = c; cname = f"{r}{pa}"
    V = Vc(c, N0).coalesce()
    cands = candidates(c); pts = samples(c)
    print("stats", dict(STATS), "cands", len(cands), flush=True)
    chosen, extra = select(c, cands, pts, V)
    used = sorted(set(chosen))
    st = Tree()
    tree = build(V, list(range(len(pts))), pts, used, cands, st)
    print(f"class {c}: cands {len(cands)} samples {len(pts)} chosen {len(used)} (extra {extra}) leaves {st.leaves} nodes {st.nodes} depth {st.maxdepth} time {time.time()-t0:.0f}s", flush=True)
    vbs = V.get_basic_sets(); assert len(vbs) == 1, len(vbs)
    vats = split_atoms(ip.set_conjuncts(str(vbs[0])))
    out = [f"/-\nReduction, residue class n ≡ {r} (mod 4), a ≡ {pa} (mod 2).  GENERATED by scripts/gen_reduction.py.\n-/\nimport Gvozdjak.Moves\n\nnamespace Gvozdjak\n\nset_option maxHeartbeats 400000\n"]
    usedleaf = set()
    def collect(t):
        if t[0] == 'leaf': usedleaf.add(t[1])
        else: collect(t[2]); collect(t[3])
    collect(tree)
    for i in sorted(usedleaf):
        cd = cands[i]; j = cd['j']; P = INFO[j]['params']
        dom = " ∧ ".join(atom_lean(a) for a in cd['atoms']) if cd['atoms'] else "True"
        L = [f"theorem p{cname}_{i} (n a b q x y : Nat) (Q X Y : Int) (hQ : Q = q) (hX : X = x) (hY : Y = y)",
             f"    (hn : n = 4 * q + {r}) (ha : a = 2 * x + {pa}) (hb : b = 2 * y + {pb})",
             f"    (hD : {dom}) : Red n a b := by"]
        for p, w in zip(P, cd['w']):
            wl = ip.lean(w)
            L.append(f"  obtain ⟨{p}, h{p}⟩ : ∃ {p} : Nat, ({p} : Int) = {wl} := ⟨Int.toNat {wl}, by omega⟩")
        L.append(f"  exact Red.m{j+1} {' '.join(P)} (by unfold C{j+1}; omega) (by unfold AdmL; omega)")
        out.append("\n".join(L) + "\n")
    L = [f"theorem cover{cname} (n a b q x y : Nat) (hn : n = 4 * q + {r}) (ha : a = 2 * x + {pa})",
         f"    (hb : b = 2 * y + {pb}) (h42 : 42 ≤ n) (hab : a < b) (hadm : AdmL a b n) : Red n a b := by",
         "  obtain ⟨Q, hQ⟩ : ∃ Q : Int, Q = q := ⟨_, rfl⟩",
         "  obtain ⟨X, hX⟩ : ∃ X : Int, X = x := ⟨_, rfl⟩",
         "  obtain ⟨Y, hY⟩ : ∃ Y : Int, Y = y := ⟨_, rfl⟩",
         "  unfold AdmL at hadm"]
    for k, at in enumerate(vats):
        L.append(f"  have v{k} : {atom_lean(at)} := by omega")
    L.append("  clear hadm h42 hab")
    emit_tree(tree, cname, 1, L)
    out.append("\n".join(L) + "\n")
    out.append("end Gvozdjak\n")
    return "\n".join(out), dict(cands=len(cands), chosen=len(used), leaves=st.leaves, pieces=len(usedleaf))

if __name__ == "__main__" and False:
    outdir = sys.argv[1]
    which = [int(z) for z in sys.argv[2].split(",")] if len(sys.argv) > 2 else list(range(8))
    for ci in which:
        c = CLASSES[ci]
        txt, info = gen_class(ci, c)
        open(os.path.join(outdir, f"Reduction{c[0]}{c[1]}.lean"), "w").write(txt)
        print(info, flush=True)
