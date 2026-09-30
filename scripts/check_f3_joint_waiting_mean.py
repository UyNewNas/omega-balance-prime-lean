"""Supplemental finite numerical sanity; never a replacement for Lean verification."""
import math,json
from fractions import Fraction
from pathlib import Path
rows=[]
for B in [1,3,6,10,15,100]:
 for K in range(7):
  p=3.0**(-K);c=math.log(B)/p;bound=1+(math.log(B)+1)/p
  for N in [0,1,2,3,10,100,1000]:
   partial=sum(min(1.0,B*math.exp(-p*n)) for n in range(N))
   assert partial<=bound+1e-8*max(1,bound)
   assert abs(B*math.exp(-p*c)/p-1/p)<=1e-8*max(1,1/p)
   rows.append({'B':B,'K':K,'prefix_length':N,'envelope_partial_sum':partial,'paper_upper_bound':bound})
actual=[]
data=json.loads((Path(__file__).resolve().parents[1]/'reports/f3_joint_waiting_semantic_sanity.json').read_text())
groups={}
for row in data['results']:
 groups.setdefault(tuple(row['roots']),[]).append(row)
for roots, values in groups.items():
 values.sort(key=lambda x:x['T'])
 total=Fraction(0)
 for row in values:
  total+=Fraction(row['joint_failure_probability'])
  bound=1+3**row['K']*(1+math.log(row['B']))
  assert float(total)<=bound+1e-10*max(1,bound)
  actual.append({'roots':roots,'tail_prefix_through_T':row['T'],'exact_prefix_tail_sum':str(total),'paper_upper_bound':bound})
print(json.dumps({'actual_finite_residue_prefix_checks':actual,'scope':'Supplemental floating-point analytic envelope sanity only, not a Lean proof or infinite Haar computation','cases':len(rows),'includes_B_one':True,'includes_K_zero':True,'prefix_zero_checked':True,'rows':rows},indent=2))
