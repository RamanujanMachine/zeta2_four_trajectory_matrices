"""Independent exact audit: evaluate finite sums, without polynomial expansion.

Uses standard-library Fraction and a closed product derivative, independently
of the fmpq_poly implementation in check_main_shell.py.
"""
from fractions import Fraction as Q
from math import comb, factorial, isqrt, prod
import json
from pathlib import Path


def primes(n):
    return [p for p in range(2, n+1)
            if all(p % t for t in range(2, isqrt(p)+1))]


def residue(q, p):
    q = Q(q)
    assert q.denominator % p, (q, p)
    return q.numerator * pow(q.denominator, -1, p) % p


def binom_and_derivative(t, b):
    # All test arguments have t>=0.  Include derivative at a zero of binom.
    assert t >= 0
    if t < b:
        return 0, Q((-1)**(b-1-t), b * comb(b-1, t))
    value = comb(t, b)
    return value, value * sum((Q(1, h) for h in range(t-b+1, t+1)), Q(0))


def finite_data(N):
    m, width = 11*N, 8*N
    fs = {}
    for s in range(-2*N, m+1):
        pairs = [binom_and_derivative(s+u*N, width) for u in (9, 10, 11)]
        val = prod(z[0] for z in pairs)
        derivative = sum((pairs[i][1] * prod(pairs[j][0] for j in range(3) if j != i)
                          for i in range(3)), Q(0))
        fs[s] = (val, derivative)
    hs, h = [], Q(0)
    for t in range(m+2*N+1):
        if t:
            h += Q(1, t*t)
        hs.append(h)
    weights = [(-1)**j * comb(m, j) for j in range(m+1)]
    return fs, hs, weights


def run():
    output = []
    for N in (3, 4, 5, 8, 12):
        fs, hs, weights = finite_data(N)
        m = 11*N
        for p in primes(8*N):
            if not (p*p > 50*N and 13*N < 2*p < 16*N):
                continue
            b, d = 8*N-p, 11*N-p
            for r in (0, 1, 2):
                if not 13*N+r < 2*p:
                    continue
                values = [j**r * fs[j][0] for j in range(m+1)]
                harmonic = sum((weights[j] * values[j] * hs[j+2*N]
                                for j in range(m+1)), Q(0))
                assert residue(p*p*harmonic, p) == 0, (N, p, r, "harmonic")
                residues = []
                for s in range(-2*N, p-2*N):
                    v, derivative = fs[s]
                    pv = s**r * v
                    pd = s**r * derivative + (r*s**(r-1)*v if r else 0)
                    summands = [weights[j] * (pd if s == j else Q(pv-values[j], s-j))
                                for j in range(m+1)]
                    actual = residue(p*sum(summands, Q(0)), p)
                    k = s % p
                    expected = 0
                    if k <= d:
                        f = prod(comb(k+u*N-p, b) for u in (9, 10, 11))
                        expected = -4*(-1)**k*comb(d, k)*k**r*f % p
                    assert actual == expected, (N, p, r, s, actual, expected)
                    residues.append(actual)
                assert sum(residues) % p == 0, (N, p, r, "Newton coefficient")
                output.append({"N": N, "prime": p, "column": r,
                               "exact_finite_sum_nodes": p})
    report = {"all_assertions_passed": True, "cases": output,
              "case_count": len(output),
              "exact_sum_node_count": sum(x["exact_finite_sum_nodes"] for x in output)}
    Path(__file__).with_name("independent_checks.json").write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps({k:v for k,v in report.items() if k != "cases"}, indent=2))


if __name__ == "__main__":
    run()
