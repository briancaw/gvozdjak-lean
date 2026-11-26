import ast, sys, itertools, re, importlib.util
sys.argv=[sys.argv[0],sys.argv[1],"/tmp/Moves_tmp.lean"]
spec=importlib.util.spec_from_file_location("gm","/home/claude/scripts/gen_moves.py"); gm=importlib.util.module_from_spec(spec); spec.loader.exec_module(gm)
spec2=importlib.util.spec_from_file_location("lc","/home/claude/scripts/layers_check.py"); lc=importlib.util.module_from_spec(spec2); spec2.loader.exec_module(lc)
def valid(n,a,b): return a!=b and 0<=a<=n and 0<=b<=n and 2*abs(a-b)<=n+1 and n<=2*(a+b)<=3*n and abs(a-b)%2==(n*(n+1)//2)%2
def graceful(p,n,a,b): return p[0]==a and p[-1]==b and sorted(p)==list(range(n+1)) and sorted(abs(p[i]-p[i+1]) for i in range(n))==list(range(1,n+1))
import functools
@functools.lru_cache(None)
def corepath(N,s,e):
    # backtracking search for a graceful labeling
    used=[False]*(N+1); du=[False]*(N+1); p=[s]; used[s]=True
    def rec():
        if len(p)==N+1: return p[-1]==e
        for x in range(N+1):
            d=abs(x-p[-1])
            if not used[x] and d>=1 and not du[d]:
                used[x]=True;du[d]=True;p.append(x)
                if rec(): return True
                p.pop();used[x]=False;du[d]=False
        return False
    return tuple(p) if rec() else None
def py(c): return c.replace("≤","<=").replace("≠","!=").replace(" = "," == ")
tot=0
for j,sig in enumerate(gm.sigs,1):
    I=gm.info(sig); types=I['types']; r=I['r']; cnt=0
    ranges=[]
    names=[]
    for i,t in enumerate(types[:-1]):
        if t in('O','EL','EH'): names+=[f"k{i}",f"A{i}"]; ranges+=[range(0,4),range(0,4)]
    names+=["N","s","e"]; ranges+=[range(1,6),range(0,6),range(0,6)]
    for vals in itertools.product(*ranges):
        env=dict(zip(names,vals))
        ok=True
        for i,t in enumerate(types[:-1]):
            if t in('O','EL','EH'):
                if env[f"A{i}"]>env[f"k{i}"]: ok=False
                env[f"B{i}"]=env[f"k{i}"]-env[f"A{i}"]
        if not ok or not valid(env['N'],env['s'],env['e']): continue
        env['n']=eval(py(I['cons'][[c.startswith('n + 1 = ') for c in I['cons']].index(True)]).split('==')[1],{},env)-1
        hs=[]
        for i,t in enumerate(types[:-1]):
            hh={'O':env.get(f"k{i}",0)+1,'EL':env.get(f"k{i}",0),'EH':env.get(f"k{i}",0)+1,'SH':1}[t]; hs.append(hh)
            env[f"H{i}"]=env['n']+1-sum(hs)
        ca=[c for c in I['cons'] if c.startswith('a = ')][0]; cb=[c for c in I['cons'] if c.startswith('b = ')][0]
        env['a']=eval(ca[4:],{},env); env['b']=eval(cb[4:],{},env)
        if not all(eval(py(c),{},env) for c in I['cons']): continue
        # build
        n=env['n']; pieces=[]
        for jj,i in enumerate(I['perm']):
            t=types[i]; lo=eval(I['Lo'][i],{},env)
            if t=='C':
                cp=corepath(env['N'],env['s'],env['e']); assert cp
                q=[lo+x for x in cp]
            else:
                hi=env[f"H{i}"]; k=env.get(f"k{i}"); A=env.get(f"A{i}")
                q={'O':lambda: lc.O(k,A,lo,hi),'EL':lambda: lc.EL(k,A,lo,hi),'EH':lambda: lc.EH(k,A,lo,hi),'SH':lambda:[hi]}[t]()
            if I['ors'][jj]: q=q[::-1]
            pieces+=q
        assert graceful(pieces,n,env['a'],env['b']),(j,env,pieces)
        cnt+=1
    print(j,types,cnt); tot+=cnt
print("total",tot)
