#!/usr/bin/env python3
"""Exact finite checks for F3 round 9. Python >=3.10; standard library only.
No prime-distribution theorem or Lean proof is certified by these tests.
"""
from __future__ import annotations
import argparse
from collections import Counter
from fractions import Fraction as F
import hashlib
import json
import math
from pathlib import Path
import random

Box = tuple[F, F, F, F]
FULL: Box = (F(0), F(1), F(0), F(1))
SPECIAL: Box = (F(1,4), F(1,3), F(1,2), F(2,3))


def v3(n: int) -> int:
    if n == 0:
        raise ValueError('v3(0) is not used')
    n=abs(n); k=0
    while n%3==0:
        n//=3; k+=1
    return k


def f3(n: int) -> int:
    if n<=1: raise ValueError('n must exceed 1')
    return v3(n+1)-v3(n-1)


def primes(n: int) -> list[int]:
    if n<2:return []
    b=bytearray(b'\x01')*(n+1); b[0:2]=b'\x00\x00'
    for p in range(2, math.isqrt(n)+1):
        if b[p]: b[p*p:n+1:p]=b'\x00'*(((n-p*p)//p)+1)
    return [p for p in range(2,n+1) if b[p]]


def quadratic_roots(t: int,c: int,h: int,eps: int) -> list[int]:
    """Roots of 2u^2-2t h u-eps h modulo 3^c, by exact Hensel lifting."""
    if c<1 or eps not in (-1,1) or t%3: raise ValueError('invalid parameters')
    mod=3
    roots=[u for u in (1,2) if (2*u*u-2*t*h*u-eps*h)%3==0]
    for _ in range(1,c):
        newmod=3*mod
        roots=[u+k*mod for u in roots for k in range(3)
               if (2*(u+k*mod)**2-2*t*h*(u+k*mod)-eps*h)%newmod==0]
        mod=newmod
    return sorted(roots)


def floor(x:F)->int:return x.numerator//x.denominator


def branches(j:int,c:int,eps:int,box:Box=FULL):
    """Yield (h,u0,lmin,lmax) exact arithmetic branches; arbitrary c>=1."""
    t=3**j; s=3**c; m=t*t*s; U=(t*s-1)//2
    al,ah,bl,bh=box
    for h in range(1,s):
        if h%3!=(-eps)%3:continue
        lo=max(1,t*h-U, floor((al*m-eps)/(2*t))+1,
               t*h-floor((bh*m-eps)/(2*t)))
        hi=min(U,t*h-1, floor((ah*m-eps)/(2*t)),
               t*h-floor((bl*m-eps)/(2*t))-1)
        if lo>hi:continue
        for u0 in quadratic_roots(t,c,h,eps):
            lmin=(lo-u0+s-1)//s; lmax=(hi-u0)//s
            if lmin<=lmax:yield (h,u0,lmin,lmax)


def branch_points(j:int,c:int,eps:int,box:Box=FULL):
    t=3**j;s=3**c
    for h,u0,lmin,lmax in branches(j,c,eps,box):
        for ell in range(lmin,lmax+1):
            u=u0+s*ell;v=t*h-u
            yield (eps+2*t*u,eps+2*t*v)


def chord(box:Box,z:F)->F:
    al,ah,bl,bh=box
    return max(F(0),min(ah,z-bl)-max(al,z-bh))


def legendre(n:int,p:int)->int:
    x=pow(n%p,(p-1)//2,p)
    return -1 if x==p-1 else x


def rho(p:int,C:int)->int:
    return 3-int(C%p==0)+legendre(C*C-8,p)


def local_product(C:int,y:int)->F:
    out=F(1)
    for p in primes(y):
        if p>=5:out*=F(p-rho(p,C),p)
    return out


def screened_branches(j:int,c:int,eps:int,y:int,box:Box=SPECIAL):
    """Exact sieve of branch parameters; input integers can exceed machine width."""
    t=3**j;s=3**c;plist=[p for p in primes(y) if p>=5]
    raw=total=0; details=[]
    for h,u0,lo,hi in branches(j,c,eps,box):
        n=hi-lo+1;raw+=n;flags=bytearray(b'\x01')*n
        C=2*eps+2*t*t*h; start=eps+2*t*u0; step=2*t*s
        for p in plist:
            bad=[x for x in range(p) if (x*(C-x)*(x*(C-x)-2))%p==0]
            assert len(bad)==rho(p,C)
            inv=pow(step,-1,p)
            for x in bad:
                residue=((x-start)*inv-lo)%p
                if residue<n:
                    flags[residue:n:p]=b'\x00'*((n-1-residue)//p+1)
        count=sum(flags);total+=count
        details.append({'h':h,'u0':u0,'raw':n,'survivors':count})
    return raw,total,details


def run(out:Path,max_r:int,max_j:int):
    rng=random.Random(20260928)
    counters=Counter(); box_checks=[]
    # Independent inverses, not the new parametrization.
    for r in range(3,max_r+1):
        m=3**r;groups={}
        for a in range(3,m,2):
            if a%3==0:continue
            b=pow(a,-1,m)
            if b<=1 or b%2==0:continue
            fa=f3(a); assert f3(b)==fa and 2*abs(fa)<r
            groups.setdefault((abs(fa),-1 if fa>0 else 1),set()).add((a,b))
            counters['inverse_pairs']+=1
        for j in range(1,(r-1)//2+1):
            c=r-2*j;t=3**j;s=3**c
            for eps in (-1,1):
                expected=groups.get((j,eps),set())
                got=list(branch_points(j,c,eps))
                assert len(got)==len(set(got)) and set(got)==expected
                counters['layer_set_checks']+=1
                counters['normal_form_points']+=len(got)
                if c>j:counters['new_range_layer_checks']+=1
                for h in range(1,s):
                    roots=quadratic_roots(t,c,h,eps)
                    assert len(roots)==(2 if h%3==(-eps)%3 else 0)
                    counters['root_lifting_checks']+=1
                    for u in roots:
                        assert (2*u-t*h)**2%s==(t*t*h*h+2*eps*h)%s
                for _ in range(3):
                    al,ah=sorted(rng.sample(range(13),2));bl,bh=sorted(rng.sample(range(13),2))
                    box=(F(al,12),F(ah,12),F(bl,12),F(bh,12))
                    selected={(a,b) for a,b in expected if box[0]*m<a<=box[1]*m and box[2]*m<b<=box[3]*m}
                    actual=set(branch_points(j,c,eps,box))
                    assert actual==selected
                    main=t*sum((chord(box,F(2*h,s)) for h in range(1,s) if h%3==(-eps)%3),F(0))
                    assert abs(F(len(actual))-main)<=10*s
                    counters['box_checks']+=1
                    for d in (1,5,7,35,55):
                        exact=sum((a*b*(a*b-2))%d==0 for a,b in actual)
                        g=F(1)
                        for p in primes(d):
                            if d%p==0:g*=F(3*p-2,p*p)
                        area=(box[1]-box[0])*(box[3]-box[2])
                        pred=g*F(t*s,6)*area
                        omega=sum(d%p==0 for p in primes(d))
                        assert abs(F(exact)-pred)<=100*(t+s)*4**omega
                        counters['divisibility_error_checks']+=1
    # Explicit counterexample to extending the simplified round-8 equation unchanged.
    a,b,j,c,eps=5,65,1,2,-1;t=3**j;s=3**c;u=(a-eps)//(2*t);v=(b-eps)//(2*t);h=(u+v)//t
    assert a*b%81==1 and f3(a)==f3(b)==1
    assert (2*u*u-eps*h)%s!=0
    assert (2*u*u-2*t*h*u-eps*h)%s==0
    witness={'a':a,'b':b,'m':81,'j':j,'c':c,'h':h,'u':u,'old_residual_mod_s':(2*u*u-eps*h)%s,'corrected_residual':0}
    # Check local roots exactly, including ramified discriminants.
    for p in primes(101):
        if p<5:continue
        for C in range(p):
            exact=sum((a*(C-a)*(a*(C-a)-2))%p==0 for a in range(p))
            assert exact==rho(p,C) and 0<=exact<=4<p
            counters['local_root_checks']+=1
    # CRT verification of screened branch counts at small sizes.
    for j in range(2,7):
        for eps in (-1,1):
            for y in (11,29):
                pts=list(branch_points(j,2,eps,SPECIAL)); ps=[p for p in primes(y) if p>=5]
                expected=sum(all(a*b*(a*b-2)%p for p in ps) for a,b in pts)
                raw,got,_=screened_branches(j,2,eps,y,SPECIAL)
                assert raw==len(pts) and got==expected
                counters['direct_presieve_checks']+=1
    # New finite data. No primality testing is performed here.
    data=[]
    for j in [j for j in (4,6,7,8,10,12,14,16) if j<=max_j]:
        c=2;r=2*j+c;t=3**j;m=t*t*9
        y=math.floor(math.exp(math.sqrt(math.log(m))))
        raw,count,detail=screened_branches(j,c,-1,y,SPECIAL)
        _,neg,_=screened_branches(j,c,1,y,SPECIAL)
        expected_raw=(t+(3 if j%2==0 else 9))//12
        assert raw==expected_raw and neg==0
        C=-2+8*t*t;V=local_product(C,y)
        line_main=F(t,12)*V
        data.append({'j':j,'r':r,'m':m,'sieving_threshold':y,'raw_positive':raw,'raw_negative':0,
                     'rough_positive':count,'rough_negative':neg,'line_density_num':V.numerator,
                     'line_density_den':V.denominator,'line_main':float(line_main),
                     'count_over_line_main':count/float(line_main), 'branches':detail})
    result={'status':'PASS','max_r':max_r,'max_j':max_j,'exact_checks':dict(counters),
            'simplified_formula_counterexample':witness,'critical_presieve_data':data,
            'limitations':['Finite checks are not asymptotic proofs.','Presieved survivors are not asserted to be primes.','No Lean or CI verification is claimed.']}
    out.mkdir(parents=True,exist_ok=True)
    (out/'verification_results.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-r',type=int,default=11)
    parser.add_argument('--max-j',type=int,default=14)
    parser.add_argument('--out',type=Path,default=Path(__file__).parent)
    args=parser.parse_args()
    if not 3<=args.max_r<=13 or not 4<=args.max_j<=18:
        parser.error('resource guard: 3<=max-r<=13 and 4<=max-j<=18')
    run(args.out,args.max_r,args.max_j)
