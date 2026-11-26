import re, sys
tex=open(sys.argv[1]).read()
rows=re.findall(r"\$\((\d+);\\,(\d+),(\d+)\)\$ & ([\d, ]+) \\\\",tex)
def graceful(p,n,a,b):
    return p[0]==a and p[-1]==b and sorted(p)==list(range(n+1)) and sorted(abs(p[i]-p[i+1]) for i in range(n))==list(range(1,n+1))
out=["/-\nThe 39 base cases: admissible triples with `n ≤ 41` and `a < b` that are not produced\nby one of the fifteen moves, each with an explicit graceful labeling checked by `decide`.\nGenerated from the appendix of the paper.\n-/\nimport Gvozdjak.Statement\n\nnamespace Gvozdjak\n"]
names=[]
for n,a,b,p in rows:
    n,a,b=int(n),int(a),int(b); p=[int(x) for x in p.split(",")]
    assert graceful(p,n,a,b)
    nm=f"base_{n}_{a}_{b}"; names.append((n,a,b,nm))
    out.append(f"theorem {nm} : IsGraceful {a} {b} {n} {p} := by\n  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide\n")
out.append("end Gvozdjak\n")
open(sys.argv[2],"w").write("\n".join(out))
print(len(rows))
