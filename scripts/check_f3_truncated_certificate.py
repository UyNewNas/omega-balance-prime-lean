"""Exact finite-residue regression for truncated certificate events, not a Lean proof."""
import json,math
from fractions import Fraction

def depth(n):
 if n==0:return math.inf
 n=abs(n);v=0
 while n%3==0:v+=1;n//=3
 return v
rows=[];observations=0;root_hits=0
for L in range(1,6):
 for H in range(1,7):
  a=1;b=1+3**L;q=3**max(H,L+1)
  units=[d for d in range(q) if d%3]
  successes=0
  for d in units:
   observations+=1
   x=depth(d-a);y=depth(d-b)
   if math.isinf(x) or math.isinf(y):root_hits+=1
   u=min(x,H);v=min(y,H)
   good=u!=v or u==v==H
   if good:
    successes+=1
    assert min(u,v)==min(L,H)
   assert (x>=H)<=good
   if L<H:assert good==(x!=y)
   else:assert good==(x>=H)
  actual=Fraction(successes,len(units))
  expected=Fraction(1,3**L) if L<H else Fraction(1,2*3**(H-1))
  lower=Fraction(1,2*3**(H-1))
  assert actual==expected and actual>=lower
  rows.append({'L':L,'H':H,'modulus':q,'unit_samples':len(units),'successes':successes,'probability':str(actual),'expected':str(expected),'uniform_lower_bound':str(lower)})
assert all(min(depth(d-1),0)==min(depth(d-4),0)==0 for d in range(9) if d%3)
print(json.dumps({'status':'exact finite-residue regression only; not kernel verification','cases':len(rows),'observations':observations,'root_hit_observations':root_hits,'H_zero_excluded':{'actual_success':'1','formula_if_misapplied':'1/2','reason':'paper and Lean mass formula require H>=1'},'rows':rows},indent=2))
