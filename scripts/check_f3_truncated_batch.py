"""Exact finite-residue checks of actual truncated matrix recovery; not Lean proof."""
import itertools,json,math
from fractions import Fraction

def depth(n):
 if n==0:return math.inf
 n=abs(n);v=0
 while n%3==0:v+=1;n//=3
 return v
configs=[[1,4],[1,10],[1,28],[1,4,7],[1,4,10],[1,10,19],[1,4,7,10]]
rows=[];batches_checked=0;root_hit_batches=0
for roots in configs:
 m=len(roots);pairs=list(itertools.combinations(range(m),2));B=len(pairs)
 for H in [1,2,3]:
  q=3**H;units=[d for d in range(q) if d%3]
  observations={d:[min(depth(d-a),H) for a in roots] for d in units}
  successes={d:{ij for ij in pairs if observations[d][ij[0]]!=observations[d][ij[1]] or observations[d][ij[0]]==observations[d][ij[1]]==H} for d in units}
  single={ij:Fraction(sum(ij in successes[d] for d in units),len(units)) for ij in pairs}
  for T in range(4):
   failed=0;pair_fail={ij:0 for ij in pairs};n=0
   for batch in itertools.product(units,repeat=T):
    n+=1;batches_checked+=1
    if any(d in roots for d in batch):root_hit_batches+=1
    known=set();matrix=[[H if i==j else None for j in range(m)] for i in range(m)]
    for d in batch:
     for i,j in successes[d]:
      known.add((i,j));l=min(observations[d][i],observations[d][j]);assert l==min(depth(roots[i]-roots[j]),H)
      if matrix[i][j] is None:matrix[i][j]=matrix[j][i]=l
    target=[[min(depth(roots[i]-roots[j]),H) for j in range(m)] for i in range(m)]
    failure=matrix!=target
    assert failure==(len(known)!=B)
    if failure:failed+=1
    for ij in pairs:
     if ij not in known:pair_fail[ij]+=1
   probability=Fraction(failed,n);bound=min(1.0,B*math.exp(-T/(2*3**(H-1))))
   assert float(probability)<=bound+1e-12
   for ij in pairs:assert Fraction(pair_fail[ij],n)==(1-single[ij])**T
   assert probability<=sum((Fraction(v,n) for v in pair_fail.values()),Fraction(0))
   if T==0:assert probability==1
   rows.append({'roots':roots,'H':H,'T':T,'batches':n,'actual_matrix_failure':str(probability),'paper_exponential_bound':bound,'pair_failures':{str(ij):str(Fraction(v,n)) for ij,v in pair_fail.items()}})
print(json.dumps({'status':'finite exact-rational/numerical regression only; no kernel or Haar proof claim','cases':len(rows),'batches_checked':batches_checked,'root_hit_batches':root_hit_batches,'checks':['actual scan target min(L,H) and diagonalH','joint-saturation certificates','T0','exact time-product pair law','canonical union bound without pair independence','paper precision-uniform exponential bound'],'rows':rows},indent=2))
