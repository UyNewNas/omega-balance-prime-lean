"""Independent exact cross-check up to 10^6: different sieve + integer bitset sumset.
Requires numpy. It compares to output from check_omega_goldbach.cpp.
"""
from pathlib import Path
from math import isqrt
import json
import numpy as np
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--prefix',type=Path,default=Path(__file__).resolve().parent/'run_1e8')
args=parser.parse_args()
base=args.prefix.parent
prefix=args.prefix.name
L=1_000_000
# Eratosthenes, separate from the C++ linear/SPF sieve.
isprime=np.ones(L+2,dtype=np.bool_)
isprime[:2]=False
for p in range(2,isqrt(L+1)+1):
    if isprime[p]: isprime[p*p::p]=False
primes=np.flatnonzero(isprime)
# Omega(n) counts, independently, each prime power dividing n.
om=np.zeros(L+2,dtype=np.uint8)
for p0 in primes:
    p=int(p0); power=p
    while power<=L+1:
        om[power::power]+=1
        power*=p
B=[int(p) for p in primes if 2<p<=L and om[p-1]==om[p+1]]
from_cpp=np.loadtxt(base/(prefix+'_balanced_primes.txt'),dtype=np.int64)
assert B==from_cpp[from_cpp<=L].tolist()
# Bit i is 1 iff i is in B. The union of all shifts computes B+B exactly.
packed=bytearray((L+8)//8)
for p in B: packed[p//8]|=1<<(p%8)
base_bits=int.from_bytes(packed,'little')
covered=0
for p in B:
    if p+5>L: break
    covered|=base_bits<<p
covered &= (1<<(L+1))-1
raw=covered.to_bytes((L+8)//8,'little')
missing=[n for n in range(2,L+1,2) if not (raw[n//8]>>(n%8))&1]
expected=np.loadtxt(base/(prefix+'_missing.txt'),dtype=np.int64)
assert missing==expected[expected<=L].tolist()
# Positive witnesses agree and their factors have matching prime-factor counts.
witnesses=np.fromfile(base/(prefix+'_witnesses.bin'),dtype=np.uint32,count=L//2)
targets=np.arange(2,L+1,2,dtype=np.uint32)
mask=witnesses>0
ps=witnesses[mask]; qs=targets[mask]-ps
balanced=np.zeros(L+2,dtype=np.bool_);balanced[B]=True
assert np.all(ps<=qs) and np.all(balanced[ps]) and np.all(balanced[qs])
assert np.array_equal(targets[~mask],np.array(missing))
result={"independent_bound":L,"method":"Eratosthenes + prime-power Omega sieve + exact integer bitset B+B", "balanced_primes":len(B),"missing_count":len(missing),"largest_missing":max(missing),"status":"PASS"}
(base/'independent_check.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
