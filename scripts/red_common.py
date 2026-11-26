import islpy as isl, ast, sys, importlib.util, re
sys_argv_backup=list(sys.argv)
sys.argv=[sys.argv[0],'/home/claude/gvcode/allowed.txt','/tmp/Moves_tmp.lean']
spec=importlib.util.spec_from_file_location("gm","/home/claude/scripts/gen_moves.py"); gm=importlib.util.module_from_spec(spec); spec.loader.exec_module(gm)
sys.argv=sys_argv_backup
def parstr(n,a,b):
    return f"((({n}) mod 4 = 0 and ({a}+{b}) mod 2 = 0) or (({n}) mod 4 = 3 and ({a}+{b}) mod 2 = 0) or (({n}) mod 4 = 1 and ({a}+{b}) mod 2 = 1) or (({n}) mod 4 = 2 and ({a}+{b}) mod 2 = 1))"
def validstr(n,a,b):
    return f"(0<={a}<={n} and 0<={b}<={n} and 2*{b}<=2*{a}+{n}+1 and 2*{a}<=2*{b}+{n}+1 and {n}<=2*({a}+{b})<=3*{n} and ({a}<{b} or {a}>{b}) and {parstr(n,a,b)})"
def lean2isl(c):
    c=c.replace("≤","<=")
    m=re.match(r"^(.*) ≠ (.*)$",c)
    if m: return f"({m.group(1)} < {m.group(2)} or {m.group(1)} > {m.group(2)})"
    return c
INFO=[gm.info(s) for s in gm.sigs]
def move_map(j):
    I=INFO[j]; P=I['params']
    cons=[lean2isl(c) for c in I['cons']]+[validstr('N','s','e')]+[f"{p}>=0" for p in P]
    return isl.Map("{ [n,a,b] -> ["+",".join(P)+"] : "+" and ".join(cons)+" }")
def VALID(n0):
    return isl.Set("{ [n,a,b] : a<b and n>=%d and %s }"%(n0,validstr('n','a','b')))

CLASSES=[(r,pa,(pa+(1 if r in (1,2) else 0))%2) for r in range(4) for pa in range(2)]
def class_sub(c): 
    r,pa,pb=c; return f"n=4q+{r} and a=2x+{pa} and b=2y+{pb}"
def Vc(c,n0):
    return isl.Set("{ [q,x,y] : exists (n,a,b: %s and n>=%d and a<b and %s) }"%(class_sub(c),n0,validstr('n','a','b')))
def move_map_c(j,c):
    I=INFO[j]; P=I['params']
    cons=[lean2isl(cc) for cc in I['cons']]+[validstr('N','s','e')]+[f"{p}>=0" for p in P]
    return isl.Map("{ [q,x,y] -> ["+",".join(P)+"] : exists (n,a,b: "+class_sub(c)+" and "+" and ".join(cons)+") }")

def kparams(j):
    return [p for p in INFO[j]['params'] if p.startswith('k')]
def move_kmap_c(j,c):
    """map [q,x,y] -> [k's], other params existential"""
    I=INFO[j]; P=I['params']; K=kparams(j); rest=[p for p in P if p not in K]
    cons=[lean2isl(cc) for cc in I['cons']]+[validstr('N','s','e')]+[f"{p}>=0" for p in P]
    return isl.Map("{ [q,x,y] -> ["+",".join(K)+"] : exists (n,a,b,"+",".join(rest)+": "+class_sub(c)+" and "+" and ".join(cons)+") }")
