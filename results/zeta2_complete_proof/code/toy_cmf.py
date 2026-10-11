#!/usr/bin/env python3
"""Exact, standard-library verification of a row/prime dependent CMF square.

No numerical approximations and no third-party dependencies.  The rational
field is M_i(w)=F(w)^(-1)F(w+e_i), with the polynomial potential below.  It is
defined wherever the relevant matrices are invertible.  A finite-grid check
illustrates its identity; the general identity follows by cancellation.
"""
from fractions import Fraction as Q
import json


def mat(rows):
    return tuple(tuple(Q(x) for x in row) for row in rows)


def mul(a, b):
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(len(b)))
                       for j in range(len(b[0]))) for i in range(len(a)))


def inv(a):
    d = a[0][0] * a[1][1] - a[0][1] * a[1][0]
    if not d:
        raise ZeroDivisionError("singular potential")
    return mat(((a[1][1] / d, -a[0][1] / d),
                (-a[1][0] / d, a[0][0] / d)))


def potential(x, y):
    return mat(((1 + x + 2*y + 2*x*y, 3*y*(1-x)),
                (3*x*(1-y), 1 + 2*x + y + 2*x*y)))


def edge(x, y, dx, dy):
    return mul(inv(potential(x, y)), potential(x + dx, y + dy))


def vp(q, p):
    q = Q(q)
    if not q:
        return float("inf")
    n, d, out = abs(q.numerator), q.denominator, 0
    while n % p == 0:
        n //= p
        out += 1
    while d % p == 0:
        d //= p
        out -= 1
    return out


def content_p(a, p):
    return min(vp(x, p) for row in a for x in row)


def bound(row, first, second, p):
    return content_p(mul(row, first), p) + content_p(second, p)


def main():
    a = edge(0, 0, 1, 0)
    b = edge(0, 0, 0, 1)
    c = edge(1, 0, 0, 1)
    d = edge(0, 1, 1, 0)
    assert a == mat(((2, 0), (3, 3)))
    assert b == mat(((3, 3), (0, 2)))
    assert c == mat(((3, 0), (-3, 2)))
    assert d == mat(((2, -3), (0, 3)))
    endpoint = mat(((6, 0), (0, 6)))
    assert mul(a, c) == mul(b, d) == endpoint
    assert mul(a, b) != mul(b, a)
    rows = (mat(((1, 0),)), mat(((0, 1),)))
    assert mul(rows[0], a) == mat(((2, 0),))
    assert mul(rows[1], b) == mat(((0, 2),))
    table = []
    for p in (2, 3):
        assert all(content_p(m, p) == 0 for m in (a, b, c, d))
        for row_id, row in enumerate(rows, 1):
            xy, yx = bound(row, a, c, p), bound(row, b, d, p)
            actual = content_p(mul(row, endpoint), p)
            assert sorted((xy, yx)) == [0, 1]
            assert max(xy, yx) == actual == 1
            table.append({"row": row_id, "prime": p, "XY_bound": xy,
                          "YX_bound": yx, "actual_content": actual,
                          "best_order": "XY" if xy > yx else "YX"})
    # Exact spot checks are distinct from the telescoping identity valid
    # for all nonsingular rational x,y.
    checks, skipped = 0, 0
    for x in range(8):
        for y in range(8):
            try:
                xy = mul(edge(x, y, 1, 0), edge(x+1, y, 0, 1))
                yx = mul(edge(x, y, 0, 1), edge(x, y+1, 1, 0))
            except ZeroDivisionError:
                skipped += 1
                continue
            assert xy == yx
            checks += 1
    print(json.dumps({"square_endpoint": [[6, 0], [0, 6]],
                      "prime_row_bounds": table,
                      "finite_grid_checks": checks,
                      "singular_squares_skipped": skipped}, indent=2))


if __name__ == "__main__":
    main()
