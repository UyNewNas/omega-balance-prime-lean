"""Finite complete-observation histograms; supplementary, not a Lean/Haar proof."""
import collections,itertools,json,math

def depth(n):
 if n==0:return math.inf
 n=abs(n);v=0
 while n%3==0:v+=1;n//=3
 return v
rows=[];batches=0
for H in range(1,5):
 q=3**H;units=[d for d in range(q) if d%3]
 models=[(1,1+3**H),(2,2+3**(H+1))]
 tables=[{d:(min(depth(d-a),H),min(depth(d-b),H)) for d in units} for a,b in models]
 assert all(x==y for table in tables for x,y in table.values())
 for T in range(4):
  hist=[]
  for table in tables:
   h=collections.Counter(tuple(table[d] for d in ds) for ds in itertools.product(units,repeat=T))
   hist.append(h);batches+=len(units)**T
  assert hist[0]==hist[1]
  rows.append({'H':H,'T':T,'models':models,'true_distances':[H,H+1],'unit_residues':len(units),'batch_inputs_per_model':len(units)**T,'full_observation_sequences':len(hist[0]),'histograms_equal':True})
controls=[]
for H in range(2,5):
 units=[d for d in range(3**H) if d%3]
 def law(L):return collections.Counter((min(depth(d-1),H),min(depth(d-(1+3**L)),H)) for d in units)
 assert law(H-1)!=law(H)
 controls.append({'H':H,'distances':[H-1,H],'histograms_equal':False,'reason':'both distances must be at least H for the nonidentifiability theorem'})
print(json.dumps({'status':'finite full-histogram regression only, not a kernel proof','cases':len(rows),'batch_inputs_checked':batches,'known_base_depth':1,'T0_included':True,'root_infinity_preserved_before_min':True,'rows':rows,'negative_controls':controls},indent=2))
