#!/usr/bin/env python3
"""Finite symmetry regression only; exact Haar independence is a Lean target."""
import json
from collections import Counter
from fractions import Fraction
from pathlib import Path

def depth(x):
    if x == 0:
        return None
    n = 0
    while x % 3 == 0:
        x //= 3
        n += 1
    return n

rows = []
for L in range(1,5):
    for extra in range(2,5):
        N=L+extra
        a,b=1,1+3**L
        joint,sign,size=Counter(),Counter(),Counter()
        root_hits=0
        for d in range(3**N):
            if d%3==0:
                continue
            r,s=depth(d-a),depth(d-b)
            if r==s:
                continue
            root_hits += r is None or s is None
            # Explicit representative only; None remains infinite in the raw observation.
            z=(0 if r is None else r)-(0 if s is None else s)
            v,n=z>0,abs(z)
            joint[v,n]+=1;sign[v]+=1;size[n]+=1
        total=sum(sign.values())
        assert root_hits==2 and sign[True]==sign[False]
        for v in [False,True]:
            for n in range(N+1):
                assert Fraction(joint[v,n],total)==Fraction(sign[v],total)*Fraction(size[n],total)
        rows.append({'L':L,'precision':N,'condition_count':total,'explicit_root_representatives':root_hits,
                     'sign_true':sign[True],'sign_false':sign[False],'size_counts':dict(sorted(size.items()))})
for z in range(-30,31):
    for n in range(1,31):
        for v in [False,True]:
            assert (((z>0),abs(z))==(v,n)) == (z==(n if v else -n))
out={'status':'finite regression only; root-representative atoms are not the exact Haar marginal',
     'cases':len(rows),'algebra_cases':61*30*2,'rows':rows}
Path('reports/f3_sign_size_independence_sanity.json').write_text(json.dumps(out,indent=2)+'\n')
print(f'PASS: {len(rows)} finite sign-size products and {out["algebra_cases"]} positive-size atom identities')
