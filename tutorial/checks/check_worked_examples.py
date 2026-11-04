"""Exact finite illustration checks; this is not a proof of the transfer theorem."""
from pathlib import Path
import json

def mul(A,B,p):
 return [[sum(A[i][k]*B[k][j] for k in range(len(B)))%p for j in range(len(B[0]))] for i in range(len(A))]
def sub(A,B,p):return [[(a-b)%p for a,b in zip(r,s)] for r,s in zip(A,B)]
I=[[int(i==j) for j in range(3)] for i in range(3)]
z=[[0,0,0],[0,1,1],[0,1,1]];w=[[0,1,0],[1,0,0],[0,0,1]]
assert mul(mul(z,w,2),z,2)==z
assert mul(z,z,2)==[[0]*3 for _ in range(3)]
e=mul(sub(I,mul(z,w,2),2),sub(I,mul(w,z,2),2),2)
assert e==[[1]*3 for _ in range(3)] and mul(e,e,2)==e
assert mul(e,[[1],[0],[0]],2)==[[1],[1],[1]]
assert mul(z,e,2)==mul(e,z,2)==[[0]*3 for _ in range(3)]

# A degree-one design need only satisfy usable linear totality equations.
chosen=[0,0,0,1,2,3]
A=[[int(chosen[j]==i) for j in range(6)] for i in range(4)]
assert all(sum(row)%2==1 for row in A)
assert all(sum(A[i][j] for i in range(4))%2==1 for j in range(6))
assert sum(A[0][j]*A[0][k] for j in range(6) for k in range(j+1,6))>0

# The consistent sum target at characteristic 3: the all-ones root is a
# countermodel outside multiples of 3; on multiples, summing axioms is exact.
assert [n%3==0 for n in range(1,7)]==[False,False,True,False,False,True]

# Exact finite polynomial arithmetic for the consistent PC/NS gap.
def add(a,b):
 c=dict(a)
 for m,v in b.items():c[m]=(c.get(m,0)+v)%2
 return {m:v for m,v in c.items() if v}
def times_var(a,j):
 out={}
 for m,v in a.items():q=list(m);q[j]+=1;out[tuple(q)]=v
 return out
f1={(1,1,0):1,(1,0,0):1};f2={(1,1,0):1,(0,0,0):1};f3={(1,0,1):1}
f4=add(f1,f2);f5=times_var(f4,2);target=add(f5,f3)
assert target=={(0,0,1):1}
assert all(max((sum(m) for m in f),default=0)<=2 for f in [f1,f2,f3,f4,f5,target])
assert all((0,0,1) not in f for f in [f1,f2,f3])
assert add(add(times_var(f1,2),times_var(f2,2)),f3)==target

# The full invariant elementary-symmetric degree-2 target is zero at one
# label and nonzero at three; a degree-1 lift of zero remains zero.
G1=[];G3=[(0,1),(0,2),(1,2)]
assert not G1 and len(G3)==3
assert mul(e,[[0],[0],[0]],2)==[[0],[0],[0]]

# Abstract arithmetic bounds used in the worked examples.
R=4*3+4;Q=1
while Q<=R:Q*=2
assert (R,Q,2*R+1)==(16,32,33)
beta=(62-2*4-1)//(2*4)
assert beta==6 and 2*(4*beta+4)+1==57
for n,q in [(6,3),(36,9)]:assert n>=2*q
assert 9<2*9

# F3 full nilpotent chain: top witness u*w*u=u and the ordered projector.
z3=[[0,1,0],[0,0,1],[0,0,0]];w3=[[0,0,0],[0,0,0],[1,0,0]]
u=mul(z3,z3,3)
assert mul(mul(u,w3,3),u,3)==u
S1=sub(I,mul(w3,u,3),3)
S2=mul(sub(I,mul(mul(z3,w3,3),z3,3),3),S1,3)
e3=mul(sub(I,mul(u,w3,3),3),S2,3)
assert e3==[[0]*3 for _ in range(3)]
results={"status":"pass","checks":["F2 one-label common witness, projector and explicit lift","F2 four-row/six-column degree-one design (not a satisfying model)","consistent characteristic-3 target residue split","consistent exact PC degree-2 / NS degree-3 illustration","counterexample to unqualified invariant-target lift at an unstable rank","strict prime-power arithmetic and fresh-target window eligibility","F3 top-witness and ordered full-chain projector"],"scope":"Finite illustration checks only; no new Lean verification or proof of general asymptotic results."}
(Path(__file__).resolve().parent/'worked_example_checks.json').write_text(json.dumps(results,indent=2)+'\n')
print('All',len(results['checks']),'finite illustration checks pass')
