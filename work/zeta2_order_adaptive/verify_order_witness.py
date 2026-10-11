"""Short exact replay of literal prime- and row-dependent order preferences."""
import json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'work/zeta2_orders_10911'))
from core import START, R, segment, endpoint

def vp(q,p):
    if not q:return 10**9
    v=0
    for sign,n in ((1,abs(int(q.numerator))),(-1,int(q.denominator))):
        while n%p==0:
            v+=sign;n//=p
    return v

N=80
W=segment(START,endpoint(N))
cuts={'A':(3,3,3,0,0,0,0),'B':(4,4,4,0,0,0,0),
      'C':(6,6,6,-9,2,1,3)}
records={}
for name,ds in cuts.items():
    w=tuple(s+N*d for s,d in zip(START,ds))
    A=segment(START,w);B=segment(w,endpoint(N))
    assert A*B==W
    U=R*A
    records[name]={p:[min(vp(U[r,i]*B[i,0],p) for i in range(3))
                     for r in range(2)] for p in (2,59,883)}
assert min(records['A'][2])==-19 and min(records['B'][2])==-25
assert min(records['A'][59])==-3 and min(records['B'][59])==-2
assert records['C'][883]==[-2,-2] and records['A'][883]==[-3,0]
out=dict(N=N,all_nine_endpoint_entries_equal=True,cut_directions=cuts,
         row_valuation_certificates=records,all_assertions_passed=True,
         scope='Exact finite preference witnesses. No asymptotic claim from these tests.')
N=40
W=segment(START,endpoint(N))
strict=[]
for ds in [(3,3,3,-3,0,0,0),(3,3,3,0,0,0,0)]:
    w=tuple(s+N*d for s,d in zip(START,ds))
    A=segment(START,w);B=segment(w,endpoint(N))
    assert A*B==W
    U=R*A
    strict.append([min(vp(U[r,i]*B[i,0],491) for i in range(3)) for r in range(2)])
assert strict==[[-1,-2],[-2,0]]
out['strict_row_witness']=dict(N=40,p=491,row_bounds=strict,
    best_shared_of_two=-2,independent_rows=-1,
    previous_arithmetic_bound=-1)
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
