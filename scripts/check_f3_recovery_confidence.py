"""Finite confidence-threshold sanity, not a kernel or infinite-Haar proof."""
import json, math
from fractions import Fraction
from pathlib import Path
rows=[]
for B in [1,3,10]:
 for K in [1,2,5]:
  for delta in ['0.9','0.5','0.01','0.000001']:
   d=float(delta);A=3**K;threshold=A*math.log(B/d);T=math.ceil(threshold)
   envelope=B*math.exp(-T/A)
   assert T>=1 and envelope<=d+1e-13
   rows.append({'B':B,'K':K,'delta':delta,'threshold':threshold,'T':T,'failure_envelope':envelope})
actual=[]
data=json.loads((Path(__file__).resolve().parents[1]/'reports/f3_joint_waiting_semantic_sanity.json').read_text())
for row in data['results']:
 for delta in ['0.9','0.5','0.1']:
  if row['T']>=3**row['K']*math.log(row['B']/float(delta)):
   fail=Fraction(row['joint_failure_probability']);d=Fraction(delta)
   assert fail<=d and 1-fail>=1-d
   actual.append({'roots':row['roots'],'T':row['T'],'delta':delta,'exact_failure':str(fail),'exact_success':str(1-fail)})
print(json.dumps({'status':'finite numerical/exact-rational sanity only; not Lean verification','threshold_cases':len(rows),'actual_finite_cases':len(actual),'threshold_checks':rows,'actual_checks':actual},indent=2))
