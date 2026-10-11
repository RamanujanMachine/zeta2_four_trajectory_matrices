"""Exact native 4F3 matrices. Product order is left to right on row states."""
from itertools import combinations
from math import prod, gcd, lcm, comb
from flint import fmpq, fmpq_mat

START=(1,1,1,0,1,1,1)
DIRECTION=(10,9,11,-11,2,1,3)
I=fmpq_mat([[1,0,0],[0,1,0],[0,0,1]])
R=fmpq_mat([[0,2,-1],[2,0,0]])

def elementary(x,k): return sum(prod(t) for t in combinations(x,k))

def theta(w):
    x=w[:4]; y=[v-1 for v in w[4:]]
    a=[-prod(x),prod(y)-elementary(x,3),elementary(y,2)-elementary(x,2),sum(y)-sum(x)]
    if a[3]==0: raise ZeroDivisionError(('singular vertex',w))
    return fmpq_mat([[0,0,fmpq(-a[0],a[3])],[1,0,fmpq(-a[1],a[3])],[0,1,fmpq(-a[2],a[3])]])

def move(w,axis,sign):
    target=list(w); target[axis]+=sign; target=tuple(target)
    if axis<4 and sign==1: E=I+theta(w)*fmpq(1,w[axis])
    elif axis<4: E=(I+theta(target)*fmpq(1,target[axis])).inv()
    else: E=(I+theta(target)*fmpq(1,w[axis])).inv()
    return target,E

def balanced(matrices):
    if not matrices: return I
    while len(matrices)>1:
        matrices=[matrices[i]*matrices[i+1] if i+1<len(matrices) else matrices[i]
                  for i in range(0,len(matrices),2)]
    return matrices[0]

def segment(start,stop):
    """Whole coordinate blocks; positive uppers, lower raises, negative upper."""
    w=tuple(start); matrices=[]
    for ax in (0,1,2,4,5,6,3):
        d=stop[ax]-w[ax]
        if ax!=3 and d<0: raise ValueError('nonmonotone path')
        if ax==3 and d>0: raise ValueError('nonmonotone x3')
        for _ in range(abs(d)):
            w,E=move(w,ax,1 if d>0 else -1); matrices.append(E)
    return balanced(matrices)

def endpoint(N): return tuple(s+N*d for s,d in zip(START,DIRECTION))

def C(w,perm=(0,1,2)):
    return prod(comb(w[i]-1,w[4+perm[i]]-1) for i in range(3))

def content(A):
    g=0; d=1
    for i in range(A.nrows()):
        for j in range(A.ncols()):
            v=A[i,j]; g=gcd(g,int(v.numerator)); d=lcm(d,int(v.denominator))
    return fmpq(g,d)

def encode(A): return [[str(A[i,j]) for j in range(A.ncols())] for i in range(A.nrows())]
def decode(a): return fmpq_mat([[fmpq(v) for v in row] for row in a])
