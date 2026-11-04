"""Finite diagnostics for illustrations, not a proof of the four-way theorem."""
import json
from pathlib import Path

def valuation(n,p):
 e=0
 while n%p==0:e+=1;n//=p
 return e

def period(d,p):
 if not d:return 1
 q=1
 while q<=d:q*=p
 return q
checks=0
for p in (2,3,5):
 for d in range(65):
  q=period(d,p); onset=1 if d==0 else 2*d+1
  for n in range(onset,2049):
   funcs=(lambda n:1,lambda n:n,lambda n:1 if n%p else n,lambda n:p**valuation(n,p))
   for h in funcs:
    assert min(h(n),d+1)==min(h(n+q),d+1)
    checks+=1
for d in range(16):
 for n in range(1,2049):
  easy = False if d==0 else n%period(d,2)!=0
  assert (2**valuation(n,2)<=d)==easy
# Same topological limit need not have the linear quantitative contract.
g=lambda n:1+valuation(n,2)
assert 16%8==24%8 and g(16)>4 and g(24)<=4
r={'status':'PASS','truncated_periodicity_comparisons':checks,
 'primes':[2,3,5],'budgets':'0..64','toy_profiles':4,
 'binary_easy_region_tests':16*2048,
 'logarithmic_toy_breaks_linear_period_contract':{'d':4,'n':16,'m':24,'period':8},
 'scope':'Finite illustrations only. Compactness/classification proved in text; no new Lean endpoint.'}
Path(__file__).with_name('topological_example_checks.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r))
