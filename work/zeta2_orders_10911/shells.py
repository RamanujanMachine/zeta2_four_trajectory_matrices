"""Held-out finite verification of six candidate extra prime shells."""
import argparse,json,math,sys,time
from fractions import Fraction as F
from core import *
from arithmetic import sieve
from profile import phi
from cuts import logabs
from pathlib import Path
sys.set_int_max_str_digits(0)
OUT=Path(__file__).resolve().parents[2]/'results/zeta2_orders_10911'
SHELLS=[(F(13,2),F(8)),(F(13,3),F(9,2)),(F(13,4),F(10,3)),
        (F(13,5),F(8,3)),(F(13,6),F(9,4)),(F(13,12),F(9,8))]
COLUMN_AWARE=False

def run(N):
    began=time.perf_counter();W=segment(START,endpoint(N));CY=R*W*C(endpoint(N))
    D=lcm(*range(1,12*N+1))*lcm(*range(1,13*N+3));G=1;H=1;used=[]
    H_columns=[1,1,1]
    for p in sieve(13*N):
        if p*p<=50*N:continue
        G*=p**phi(F(N,p))
        if any(a*N<p<b*N for a,b in SHELLS):H*=p;used.append(p)
        for r in range(3):
            if any((a*N+F(r,a.denominator))<p<b*N for a,b in SHELLS):H_columns[r]*=p
    if COLUMN_AWARE:
        residual=[];bounds=[]
        for r in range(3):
            Dr=lcm(*range(1,12*N+1))*lcm(*range(1,13*N+r+1))
            residual.append([str((CY[i,r]*fmpq(Dr,G*H_columns[r])).denominator) for i in range(2)])
            bounds.append(logabs(CY[1,r])+math.log(Dr)-math.log(G)-math.log(H_columns[r]))
        ok=all(d=='1' for row in residual for d in row)
        result=dict(N=N,status='NUMERICAL_CANDIDATE' if ok else 'REJECTED',
                    every_column_pair_integral=ok,residual_denominators_by_column=residual,
                    log_q_bounds_by_column=bounds,unshifted_all_six_counterexample_retained=True,
                    lower_shell_endpoints='(13*N+r)/k for k=2,3,4,5,6,12; column r=0,1,2',
                    runtime_seconds=time.perf_counter()-began)
        (OUT/f'shells_columnwise_{N}.json').write_text(json.dumps(result,indent=2))
        print(json.dumps(result),flush=True);return
    A=CY*fmpq(D,G*H)
    residual=[[str(A[i,j].denominator) for j in range(3)] for i in range(2)]
    ok=all(A[i,j].denominator==1 for i in range(2) for j in range(3))
    result=dict(N=N,status='NUMERICAL_CANDIDATE' if ok else 'REJECTED',all_six_entries_integral=ok,
                shells=[[str(a),str(b)] for a,b in SHELLS],shell_prime_count=len(used),
                residual_denominators=residual,log_q_bound=logabs(CY[1,0])+math.log(D)-math.log(G)-math.log(H),
                actual_reduced_log_q=math.log(int((CY[0,0]/CY[1,0]).denominator)),
                arithmetic_rate=(math.log(D)-math.log(G)-math.log(H))/N,
                shell_gain_rate=math.log(H)/N,G=str(G),H=str(H),D=str(D),runtime_seconds=time.perf_counter()-began)
    (OUT/f'shells_{N}.json').write_text(json.dumps(result,indent=2))
    print(json.dumps({k:v for k,v in result.items() if k not in ('G','H','D','shells')}),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--depths',nargs='+',type=int,default=[640,1280,2000,3000,4000,6000]);p.add_argument('--column-aware',action='store_true')
    args=p.parse_args();COLUMN_AWARE=args.column_aware;tag='_columnwise' if COLUMN_AWARE else ''
    for N in args.depths:
        if not (OUT/f'shells{tag}_{N}.json').exists():run(N)
