"""Finite exact checks for the conservative all-index construction in paper/main.tex.

These are consistency tests, not a substitute for the proof. Default: 100 cases.
Use --large to additionally replay the historical p=2, K=48 primitive enclosure.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path

import flint
from flint import arb, ctx, fmpq, fmpq_mat, fmpz_poly
from qbeta import entries, chi

ROOT = Path(__file__).resolve().parents[1]


def content_exponent(K):
    return (10*K**3 + 3*K*K - 10*K - 3*(K % 2)) // 12


def cyclotomic_exponent(K, d):
    if d % 2:
        if d <= K:
            r, t = divmod(K, d)
            f = lambda m: (m+2)**2 // 4 if m else 0
            return t*f(r+1) + (d-t)*f(r)
        return 2*(K-(d-1)//2) if d <= 2*K else 0
    if d % 4 == 2:
        h = d//2
        return sum(max(0, K-a*h) for a in range(1, K//h+1, 2))
    u = d//4
    return min(K, max(0, K-4*u) + max(0, K-u-1))


def clearer(p, K):
    phi = [0]*(4*K+1)
    result = 1
    for d in range(1, 4*K+1):
        value = p**d-1
        for j in range(1, d):
            if d % j == 0:
                assert value % phi[j] == 0
                value //= phi[j]
        phi[d] = value
        result *= value**cyclotomic_exponent(K, d)
    return result


def determinant_polynomial(p, K):
    aa, bb = entries(p, K, 2)
    A = fmpq_mat(K, K, [aa[i+j] for i in range(K) for j in range(K)])
    B = fmpq_mat(K, K, [bb[i+j] for i in range(K) for j in range(K)])
    # det(A+XB)=det(B) det(XI+B^{-1}A).
    return (-(B.inv()*A)).charpoly()*B.det()


def primitive(poly):
    den = math.lcm(*(int(c.q) for c in poly))
    integers = [int(c.p)*(den//int(c.q)) for c in poly]
    con = math.gcd(*integers)
    return fmpz_poly([c//con for c in integers]), den, con


def divisor_enclosure(p, prec):
    """Exact divisor-sum partial sum and an Arb enclosure of its n^2 tail."""
    ctx.prec = prec
    N = math.ceil((prec+64)*math.log(2)/math.log(p))+128
    sigma = [0]*(N+1)
    for d in range(1, N+1):
        for n in range(d, N+1, d):
            sigma[n] += d*chi(n//d)
    total = 0
    for n in range(1, N+1):
        total = p*total + sigma[n]
    value = arb(total)/arb(p)**N
    rho = (arb(N+2)/arb(N+1))**2/p
    assert rho < 1
    tail = arb(N+1)**2*arb(p)**(-N-1)/(1-rho)
    return value+arb(0, tail), N, tail


def large_case():
    p, K = 2, 48
    poly = determinant_polynomial(p, K)
    assert poly[K] == fmpq(p)**(K*(K*K-1))
    P, den, con = primitive(poly)
    bits = max(abs(int(c)).bit_length() for c in P)
    prec = bits+16*K*K+256
    z, N, tail = divisor_enclosure(p, prec)
    value = arb(0)
    for c in reversed(list(P)):
        value = value*z+int(c)
    assert not value.contains(0)
    encoded = ','.join(str(c) for c in P).encode()
    return dict(p=p, K=K, degree=P.degree(), nonzero_certified=True,
                normalization='primitive integer polynomial, positive gcd removed',
                precision_bits=prec, terms=N, tail_bound=tail.str(24),
                value=value.str(40), logabs=float(abs(value).log()),
                coefficient_sha256=hashlib.sha256(encoded).hexdigest(),
                v2content=(con & -con).bit_length()-1,
                denominator_bits=den.bit_length())


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--large', action='store_true')
    args = parser.parse_args()
    rows, examples = [], []
    for p in (2, 3, 4, 5, 6):
        for K in range(1, 21):
            poly = determinant_polynomial(p, K)
            assert poly.degree() == K
            assert poly[K] == (-1)**K*fmpq(p)**(K*(K*K-1))
            c = content_exponent(K)
            scale = fmpq(clearer(p, K), p**c)
            P = poly*scale
            assert all(co.q == 1 for co in P), (p, K)
            rows.append(dict(p=p, K=K, c_K=c, degree=K,
                             leading_coefficient_matches=True, integer_coefficients=True))
            if p in (2, 3, 4) and K <= 4:
                examples.append(dict(p=p, K=K,
                    delta_coefficients_ascending=[str(co) for co in poly],
                    safe_integer_coefficients_ascending=[str(co) for co in P]))
        print('Passed exact conservative normalization:', p, flush=True)
    output = ROOT/'certificates'
    output.mkdir(exist_ok=True)
    result = dict(status='passed', scope='finite exact consistency evidence',
                  python_flint=flint.__version__, cases=len(rows), rows=rows)
    (output/'normalization-replay.json').write_text(json.dumps(result, indent=2)+'\n')
    (output/'small-examples.json').write_text(json.dumps(examples, indent=2)+'\n')
    if args.large:
        row = large_case()
        (output/'large-enclosure-replay.json').write_text(json.dumps(row, indent=2)+'\n')
        print(json.dumps(row), flush=True)


if __name__ == '__main__':
    main()
