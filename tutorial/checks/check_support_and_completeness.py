"""Finite checks of new illustrative calculations; not general proof verification."""
from itertools import combinations
from pathlib import Path
import json

def rank_mod(rows,p):
 A=[[x%p for x in row] for row in rows];r=0
 for j in range(len(A[0])):
  pivot=next((i for i in range(r,len(A)) if A[i][j]),None)
  if pivot is None:continue
  A[r],A[pivot]=A[pivot],A[r]
  inv=pow(A[r][j],-1,p);A[r]=[(x*inv)%p for x in A[r]]
  for i in range(len(A)):
   if i!=r and A[i][j]:
    f=A[i][j];A[i]=[(x-f*y)%p for x,y in zip(A[i],A[r])]
  r+=1
  if r==len(A):break
 return r
cases=[]
for n,s,p in [(5,4,2),(8,4,2),(12,4,2),(6,3,3),(6,2,3)]:
 rows=[[int(i in S) for i in range(n)] for S in combinations(range(n),s)]
 got=rank_mod(rows,p);want=n-1 if s%p==0 else n
 assert got==want,(n,s,p,got,want)
 cases.append({'n':n,'s':s,'p':p,'orbit_span_dimension':got})
assert rank_mod([[1]*4],2)==1

# Symbolic polynomial identities over the integers descend to every field.
def add(A,B,scale=1):
 C=dict(A)
 for m,c in B.items():C[m]=C.get(m,0)+scale*c
 return {m:c for m,c in C.items() if c}
def mult(A,B):
 C={}
 for (a,b),x in A.items():
  for (c,d),y in B.items():C[(a+c,b+d)]=C.get((a+c,b+d),0)+x*y
 return {m:c for m,c in C.items() if c}
one={(0,0):1};x={(1,0):1};y={(0,1):1}
B_x=add(mult(x,x),x,-1);B_y=add(mult(y,y),y,-1)
g_xy=mult(x,y);g_cov=mult(add(one,x,-1),add(one,y,-1));g_diff=add(x,y,-1)
gens=[g_cov,g_xy,g_diff]
def evaluate(F,a,b):return sum(c*a**i*b**j for (i,j),c in F.items())
T={}
for a in [0,1]:
 for b in [0,1]:
  delta=mult(x if a else add(one,x,-1), y if b else add(one,y,-1))
  f=next(f for f in gens if evaluate(f,a,b)!=0)
  value=evaluate(f,a,b);assert value in [-1,1]
  T=add(T,mult(delta,f),value)
H=add(one,T,-1);R={};q_x={};q_y={}
for (i,j),c in H.items():
 if i>=2:
  q_x=add(q_x,{(l,j):c for l in range(i-1)})
  i=1
 if j>=2:
  q_y=add(q_y,{(i,l):c for l in range(j-1)})
  j=1
 R=add(R,{(i,j):c})
assert not R
assert add(add(T,mult(q_x,B_x)),mult(q_y,B_y))==one
# Orbit-sum polynomial bases use distinct monomials, so even in
# characteristic2 a two-element orbit is a nonzero polynomial.
assert {(1,0):1,(0,1):1} and (1,0)!=(0,1)
report={'status':'pass','compression_cases':cases,'n4_exception_dimension':1,'boolean_certificate':'Exact integer identity for two-variable inconsistent Boolean system with xy, (1-x)(1-y), x-y and Boolean axioms','scope':'Finite examples only; the new general lemmas rely on their written proofs; no Lean certification claimed.'}
(Path(__file__).resolve().parent/'support_completeness_checks.json').write_text(json.dumps(report,indent=2)+'\n')
print('Support/completeness finite illustration checks pass')
