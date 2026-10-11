"""Exact arrangement certificate for the six-shell digit patterns.
The only moving y-boundaries are {c*x}, c in SLOPES. Their ordering
can change only at an integer c*x or (c-c')*x. Thus checking the
listed rational x cuts and one point per intervening chamber checks
all real x,y in each displayed shell, not just sampled N,p.
"""
from fractions import Fraction as Q
from itertools import combinations
import json
from pathlib import Path
SLOPES=(11,-9,-10,-11,-1,-2,-3)
def floor(x):return x.numerator//x.denominator
def frac(x):return x-floor(x)
REGIONS=[
 ('k2',Q(1,8),Q(2,13),(1,1,0,0,(1,1,1),(0,0,0))),
 ('k3',Q(2,9),Q(3,13),(1,2,2,0,(2,2,2),(1,1,0))),
 ('k4',Q(3,10),Q(4,13),(2,3,1,0,(2,3,3),(0,1,0))),
 ('k5',Q(3,8),Q(5,13),(3,4,0,0,(3,3,4),(0,0,0))),
 ('k6a',Q(4,9),Q(5,11),(3,4,1,0,(4,5,5),(0,1,0))),
 ('k6b',Q(5,11),Q(6,13),(3,5,2,1,(4,5,5),(0,1,0))),
 ('k12a',Q(8,9),Q(10,11),(7,9,0,0,(8,9,10),(0,0,0))),
 ('k12b',Q(10,11),Q(12,13),(7,10,1,1,(8,9,10),(0,0,0))),
]
def signature(x,y):
 a=floor(8*x);M=floor(11*x);b=frac(8*x);d=frac(11*x)
 e=int(y>d);lam=tuple(floor(y+u*x) for u in (9,10,11))
 delta=tuple(int(frac(y+u*x)<b) for u in (9,10,11))
 return a,M,e+sum(delta),e,lam,delta

def run():
 ds=set(map(abs,SLOPES))|{abs(c-d) for c,d in combinations(SLOPES,2)}|{8}
 cuts=sorted({Q(k,d) for d in ds if d for k in range(d+1)})
 rows=[]
 for name,lo,hi,expected in REGIONS:
  xs=sorted({lo,hi}|{x for x in cuts if lo<x<hi})
  xprobes=xs[1:-1]+[(a+b)/2 for a,b in zip(xs,xs[1:])]
  count=0
  for x in xprobes:
   ys=sorted({Q(0),Q(1)}|{frac(c*x) for c in SLOPES})
   probes=ys[:-1]+[(a+b)/2 for a,b in zip(ys,ys[1:])]
   sigs=[signature(x,y) for y in probes]
   h=min(s[2] for s in sigs)
   assert h==expected[2],(name,x,h,expected)
   for y,s in zip(probes,sigs):
    assert s[0:2]==expected[0:2],(name,x,y,s,expected)
    if s[2]==h:assert s==expected,(name,x,y,s,expected)
   count+=len(probes)
  rows.append({'name':name,'x_interval':[str(lo),str(hi)],'signature':expected,'x_probe_count':len(xprobes),'y_cell_checks':count})
 # Split endpoints x=5/11,10/11 cannot occur for eligible primes: p|11N
 # and p^2>50N while N/p in these ranges force p>50*x>22,
 # so p!=11; hence p|N would force N/p to be a positive integer.
 out={'status':'exact_chamber_certificate_passed','regions':rows,'total_y_cell_checks':sum(row['y_cell_checks'] for row in rows)}
 print(json.dumps(out,indent=2))
 Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
if __name__=='__main__':run()
