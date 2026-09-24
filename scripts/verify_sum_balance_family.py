#!/usr/bin/env python3
"""Exact audit of a polynomial family of prime-centred Ruth-Aaron pairs.

Python standard library only.  The scan is exhaustive in 1 <= t <= limit,
NOT in all primes <= some bound and NOT in all Ruth-Aaron pairs.

Miller-Rabin is used only as a one-sided rejection filter. Every retained
u, v, q, r is proved prime by trial division by ALL primes <= sqrt(n).
Every retained centre P has a Pocklington certificate using the prime q:
q | P-1, q*q > P, a^(P-1) = 1 (mod P),
gcd(a^((P-1)/q)-1, P) = 1.
No probable prime is reported as a proved prime.
"""
from __future__ import annotations
import argparse
import json
from math import gcd, isqrt
from pathlib import Path


def values(t: int) -> tuple[int, int, int, int, int]:
    u = 2*t + 1
    v = 15*t + 8
    q = 390*t*t + 238*t + 17
    r = 390*t*t + 225*t + 16
    P = 23400*t*t*t + 25980*t*t + 8160*t + 511
    return u, v, q, r, P


def primes_to(limit: int) -> list[int]:
    sieve = bytearray(b'\x01') * (limit + 1)
    if limit >= 0:
        sieve[0] = 0
    if limit >= 1:
        sieve[1] = 0
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            start = p*p
            sieve[start::p] = b'\x00' * ((limit-start)//p + 1)
    return [i for i in range(2, limit + 1) if sieve[i]]


def probable_prime_filter(n: int) -> bool:
    """False is a proof of compositeness; True is NOT a primality proof."""
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d, s = n-1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11):
        x = pow(a, d, n)
        if x in (1, n-1):
            continue
        for _ in range(s-1):
            x = x*x % n
            if x == n-1:
                break
        else:
            return False
    return True


def trial_prime(n: int, primes: list[int], sieve_limit: int) -> bool:
    if n < 2:
        return False
    if isqrt(n) > sieve_limit:
        raise ValueError('Trial-division sieve is too short')
    for p in primes:
        if p*p > n:
            return True
        if n % p == 0:
            return n == p
    return True


def pocklington_witness(P: int, q: int) -> int:
    """q must already be certified prime. Raise rather than silently skip."""
    if (P-1) % q or q*q <= P:
        raise ValueError('Pocklington size/divisibility hypothesis failed')
    for a in range(2, 1002):
        if pow(a, P-1, P) == 1 and gcd(pow(a, (P-1)//q, P)-1, P) == 1:
            return a
    raise RuntimeError(f'Unresolved probable-prime centre {P}; increase witness search')


def symbolic_audit() -> dict:
    # These finite identities checks are additional regression checks.
    # Proofs for all t are in docs/sum_balance/research_round2.md.
    for t in range(-100, 101):
        u, v, q, r, P = values(t)
        A, B, d = 15*u, 2*v, 13*t+1
        assert B-A == 1
        assert q == 1+B*d and r == 1+A*d
        assert B*r-A*q == 1
        assert P == 2*A*q+1 == 2*B*r-1
        assert 2+3+5+u+q == 2+2+v+r
    allowed = {str(ell): [t for t in range(ell)
                          if all(n % ell for n in values(t))]
               for ell in (2, 3, 5, 7)}
    assert allowed == {'2':[1], '3':[0,2], '5':[0,3,4], '7':[4,5]}
    disc_q = 238**2 - 4*390*17
    disc_r = 225**2 - 4*390*16
    assert isqrt(disc_q)**2 != disc_q
    assert isqrt(disc_r)**2 != disc_r
    cubic_residues = [values(t)[4] % 19 for t in range(19)]
    assert 23400 % 19 != 0 and all(cubic_residues)
    # Coefficient contents are 1; hence none is identically zero modulo any prime.
    coeffs = [(2,1), (15,8), (390,238,17), (390,225,16),
              (23400,25980,8160,511)]
    for cs in coeffs:
        g = 0
        for c in cs:
            g = gcd(g, c)
        assert g == 1
    # Product degree is 9; every prime ell >= 11 has more than 9 residues,
    # so the nonzero product polynomial cannot vanish at every residue.
    # This completes the no-fixed-prime-divisor proof together with the table.
    # Audit the obstruction in the classic Nelson-Penney-Pomerance family.
    for k in range(3):
        assert ((2*k+1)*(8*k+5)*(768*k**3+864*k*k+224*k-9)) % 3 == 0
    return {'allowed_residues':allowed,
            'quadratic_discriminants':[disc_q,disc_r],
            'cubic_modulus':19,'cubic_residues':cubic_residues}


def scan(limit: int) -> dict:
    if not __debug__:
        raise RuntimeError('Run without -O: exact audit assertions must remain enabled')
    if not 1 <= limit <= 100000:
        raise ValueError('limit must lie in [1, 100000]')
    audit = symbolic_audit()
    sieve_limit = isqrt(max(values(limit)[:4]))
    primes = primes_to(sieve_limit)
    rows = []
    four_prime_hits = 0
    for t in range(1, limit+1):
        u,v,q,r,P = values(t)
        if not all(probable_prime_filter(n) for n in (u,v,q,r)):
            continue
        if not all(trial_prime(n, primes, sieve_limit) for n in (u,v,q,r)):
            continue
        four_prime_hits += 1
        if not probable_prime_filter(P):
            continue
        a = pocklington_witness(P,q)
        left, right = [2,3,5,u,q], [2,2,v,r]
        from math import prod
        assert prod(left) == P-1 and prod(right) == P+1
        assert sum(left) == sum(right)
        rows.append({'t':t,'u':u,'v':v,'q':q,'r':r,'p':P,
                     'S_neighbor':sum(left),'Omega_left':5,'Omega_right':4,
                     'left_prime_factors':left,'right_prime_factors':right,
                     'center_certificate':{'method':'Pocklington',
                         'prime_divisor_q':q,'witness_a':a,
                         'cofactor':(P-1)//q,
                         'q_squared_greater_than_p':q*q>P,
                         'fermat_residue':pow(a,P-1,P),
                         'gcd':gcd(pow(a,(P-1)//q,P)-1,P)}})
    if limit == 50000:
        assert four_prime_hits == 48
        assert [row['t'] for row in rows] == [5,41529,48465]
    return {'parameter_range':{'min_t':1,'max_t':limit},
            'scope':'This polynomial family only; not all S-balanced primes',
            'four_prime_hits':four_prime_hits,'prime_center_hits':len(rows),
            'trial_division_sieve_limit':sieve_limit,'audit':audit,'rows':rows}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--limit',type=int,default=50000)
    parser.add_argument('--output',type=Path,default=Path('sum_balance_family_verified.json'))
    parser.add_argument('--check-against', type=Path,
                        help='Require exact equality with a stored JSON regression report')
    args = parser.parse_args()
    report = scan(args.limit)
    if args.check_against is not None:
        expected = json.loads(args.check_against.read_text(encoding='utf-8'))
        if report != expected:
            raise RuntimeError(f'Regression mismatch: {args.check_against}')
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    print(f"Exact scan: t=1..{args.limit}; four-prime hits={report['four_prime_hits']}; "
          f"certified prime-centre hits={report['prime_center_hits']}")
    for row in report['rows']:
        print(f"t={row['t']}, p={row['p']}, S={row['S_neighbor']}, "
              f"Pocklington witness={row['center_certificate']['witness_a']}")
    print(f'Written {args.output.resolve()}')

if __name__ == '__main__':
    main()
