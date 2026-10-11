#!/usr/bin/env python3
"""Independent exact diagnostics for the audited finite formula.

The uniform derivation is in the accompanying manuscript. These finite checks do
not replace it and do not establish any extra arithmetic divisibility.
"""
import json
import sys
from math import comb, factorial
from pathlib import Path
from flint import fmpq, fmpq_mat, fmpq_poly

from core import I, R, START, theta, segment

s = fmpq_poly([0, 1])

def F_at(w):
    out = fmpq_poly([1])
    for x, y in zip(w[:3], w[4:]):
        for k in range(y, x):
            out *= s + k
        out /= factorial(x-y)
    return out

def divided_sum(m, F, f):
    P = F*f
    out = fmpq_poly([])
    for j in range(m+1):
        q, r = divmod(P-P(j), s-j)
        assert not r
        out += (-1)**j*comb(m,j)*q
    return out

def J(P, eta):
    total = fmpq(0)
    for h in range(P.degree()+1):
        delta = sum(((-1)**(h-t)*comb(h,t)*P(t-eta) for t in range(h+1)), fmpq(0))
        total += fmpq((-1)**h,h+1)*delta
    return total

def ell(w, f, eta):
    F=F_at(w);m=-w[3]
    H=[fmpq(0)]
    for k in range(1,m+eta+1):H.append(H[-1]+fmpq(1,k*k))
    coeff=[(-1)**j*comb(m,j)*F(j)*f(j) for j in range(m+1)]
    return (sum((coeff[j]*H[j+eta] for j in range(m+1)), fmpq(0))+J(divided_sum(m,F,f),eta),sum(coeff,fmpq(0)))

def Y(w,eta):
    out=fmpq_mat(2,3);C=F_at(w)(0)
    for r in range(3):
        v=ell(w,s**r,eta)
        for i in range(2):out[i,r]=2*v[i]/C
    return out

def audit(w):
    x=w[:3];y=w[4:];m=-w[3];F=F_at(w)
    lo=sorted(a-1 for a in y)[1];hi=min(a-1 for a in x)
    A=s;D=s-m
    for yi in y:A*=s+yi-1
    for xi in x:D*=s+xi
    SA=divided_sum(m,F,A);SD=divided_sum(m,F,D)
    assert SD==SA(s+1)
    denom=fmpq_poly([1])
    for j in range(m+1):denom*=s-j
    partial=fmpq_poly([])
    for j in range(m+1):partial+=(-1)**j*comb(m,j)*divmod(denom,s-j)[0]
    assert partial==fmpq_poly([(-1)**m*factorial(m)])
    for eta in range(lo,hi+1):
        assert ell(w,A-D,eta)==(0,0)
        assert Y(w,eta)==Y(w,lo)
        for P in (F,SA,s**5+3*s**2-7):
            assert J(P(s+1)-P,eta)==P.derivative()(-eta)
            assert J(P,eta+1)-J(P,eta)==-P.derivative()(-eta-1)
    native=R*segment(START,w)
    assert native==Y(w,lo)
    for i in range(3):
        nxt=list(w);nxt[i]+=1;nxt=tuple(nxt)
        assert Y(nxt,lo)==native*(I+theta(w)*fmpq(1,w[i]))
    for i in range(3):
        if y[i]>=2:
            nxt=list(w);nxt[i+4]-=1;nxt=tuple(nxt)
            assert Y(nxt,lo)==native*(I+theta(w)*fmpq(1,y[i]-1))
    nxt=list(w);nxt[3]-=1;nxt=tuple(nxt)
    assert Y(nxt,lo)==native*(I-theta(nxt)*fmpq(1,m+1)).inv()
    return {'vertex':list(w),'eta_range':[lo,hi],'kernel_sign':(-1)**m,
            'shift_companion_eta_generator_and_native_checks':True}

if __name__=='__main__':
    assert Y(START,0)==R
    rows=[]
    for xyz,ys in [((3,4,5),(1,2,3)),((2,4,6),(1,2,2)),((5,3,4),(2,1,3)),((1,2,4),(1,1,1))]:
        for m in range(4):rows.append(audit((*xyz,-m,*ys)))
    out=Path(__file__).with_name('finite_formula_checks.json')
    out.write_text(json.dumps({'initial_rows_match':True,'states':rows,'state_count':len(rows)},indent=2)+'\n')
    print(f'{len(rows)} general vertices: all exact checks passed; {out}')
