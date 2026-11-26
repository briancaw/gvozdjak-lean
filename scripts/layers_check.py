import sys, functools
sys.setrecursionlimit(100000)
def ind(s,k,x): return 1 if s<=x<s+k else 0
def spec(p,u,v,cv,cd,rng):
    assert p[0]==u and p[-1]==v,(p,u,v)
    for x in range(rng): assert p.count(x)==cv(x),(p,x)
    ds=[abs(p[i]-p[i+1]) for i in range(len(p)-1)]
    for d in range(rng): assert ds.count(d)==cd(d),(p,ds,d)
def O(k,A,lo,hi):
    assert A<=k and lo+k+1<=hi
    if 2*A<=k:
        if k==0: p=[lo,hi]
        elif 2*A<=k-1:
            k1=k//2;k2=(k-1)//2
            p=O(k1,A,lo,hi+k2+1)+O(k2,A,lo+k1+1,hi)
        else:
            p=EL(A,A,lo,hi+A+1)+EH(A,A,lo+A+1,hi)[::-1]
    else:
        c=lo+hi+k
        p=[c-x for x in O(k,k-A,lo,hi)][::-1]
    spec(p,lo+A,hi+A,lambda x:ind(lo,k+1,x)+ind(hi,k+1,x),lambda d:ind(hi-lo-k,2*k+1,d),hi+k+3)
    return p
def EL(k,A,lo,hi):
    assert k>=1 and A<=k and 2*A!=k and lo+k+1<=hi
    if 2*A<k:
        if k==1: p=[lo,hi,lo+1]
        else:
            if k==3*A+1: k1,k2=A+1,2*A-1
            else: k1,k2=A,k-1-A
            p=O(k1,A,lo,hi+k2)+EL(k2,A,lo+k1+1,hi)
    else:
        p=EL(k,k-A,lo,hi)[::-1]
    spec(p,lo+A,lo+k-A,lambda x:ind(lo,k+1,x)+ind(hi,k,x),lambda d:ind(hi-lo-k,2*k,d),hi+k+3)
    return p
def EH(k,A,lo,hi):
    assert k>=1 and A<=k and 2*A!=k and lo+k<=hi
    c=lo+hi+k
    p=[c-x for x in EL(k,k-A,lo,hi+1)]
    spec(p,hi+A,hi+k-A,lambda x:ind(lo,k,x)+ind(hi,k+1,x),lambda d:ind(hi-lo-k+1,2*k,d),hi+k+3)
    return p
n=0
for k in range(0,14):
    for A in range(k+1):
        for lo in (0,3):
            for g in (0,1,5):
                O(k,A,lo,lo+k+1+g); n+=1
                if k>=1 and 2*A!=k:
                    EL(k,A,lo,lo+k+1+g); EH(k,A,lo,lo+k+g); n+=2
print("ok",n)
