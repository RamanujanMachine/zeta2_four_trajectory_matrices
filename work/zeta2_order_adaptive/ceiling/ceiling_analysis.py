"""Exact finite arithmetic headroom after the columnwise six-shell normalizer.

Reads immutable prior checkpoints. This is numerical diagnosis, not a uniform
arithmetic assertion. Outputs are resumable and live beside this script.
"""
import argparse,json,math,sys,time
from pathlib import Path
from fractions import Fraction
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'work/zeta2_orders_10911'))
from core import decode,R,C,endpoint
from arithmetic import sieve
from flint import fmpq,fmpz
OUT=Path(__file__).resolve().parent
SOURCE=ROOT/'results/zeta2_orders_10911'
SHELLS=((2,8,1),(3,9,2),(4,10,3),(5,8,3),(6,9,4),(12,9,8))

def vp(z,p):
 if z==0:return None
 z=abs(z); v=0
 while z%p==0:z//=p;v+=1
 return v

def lcm_upto(n,primes):
 ans=fmpz(1)
 for p in primes:
  if p>n:break
  pp=p
  while pp*p<=n:pp*=p
  ans*=pp
 return ans

def shell(N,r,p):
 return any(k*p>13*N+r and b*p<a*N for k,a,b in SHELLS)

def run(N):
 began=time.perf_counter()
 primes=sieve(50*N)
 W=decode(json.loads((SOURCE/f'matrix_{N}.json').read_text()))
 CY=R*W*C(endpoint(N))
 cache=SOURCE/f'arithmetic_{N}.json'
 if not cache.exists():cache=SOURCE/f'shells_{N}.json'
 prior=json.loads(cache.read_text())
 G=fmpz(prior['G'])
 depths=json.loads((SOURCE/f'depth_{N}.json').read_text())['rows']
 L=lcm_upto(12*N,primes)
 rows=[]
 for r in range(3):
  D=L*lcm_upto(13*N+r,primes)
  H=fmpz(1)
  for p in primes:
   if p*p>50*N and p<=13*N and shell(N,r,p):H*=p
  z=[CY[i,r]*fmpq(D,G*H) for i in range(2)]
  assert all(t.denominator==1 for t in z),(N,r,'nonintegral')
  pnorm,qnorm=(t.numerator for t in z)
  g=pnorm.gcd(qnorm);remaining=g
  factors=[]
  for p in primes:
   v=vp(remaining,p)
   if not v:continue
   remaining//=fmpz(p)**v
   pv,qv=vp(pnorm,p),vp(qnorm,p)
   factors.append(dict(p=p,v=v,p_over_N=p/N,numerator_v=pv,denominator_v=qv,
                       class_= 'excluded_small_prime' if p*p<=50*N else 'beyond_cutoff' if p>13*N else 'eligible_prime',
                       in_shell=shell(N,r,p),x=str(Fraction(N,p))))
   if remaining==1:break
  logg=math.log(int(g))
  grouped={label:sum(t['v']*math.log(t['p'])/N for t in factors if t['class_']==label) for label in ('excluded_small_prime','eligible_prime','beyond_cutoff')}
  actual=depths[r]
  assert int((z[0]/z[1]).denominator)==int(actual['q'])
  rows.append(dict(column=r,reduced_log_q=actual['log_q'],delta=actual['delta'],numerical_implied_mu=1+1/actual['delta'],
   normalized_gcd=str(g),normalized_gcd_log=logg,extra_gain_per_N=logg/N,
   classified_gain_per_N=grouped,trial_factor_limit=50*N,unfactored_remainder=str(remaining),factors=factors))
 record=dict(status='NUMERICAL_CANDIDATE',N=N,rows=rows,runtime_seconds=time.perf_counter()-began,
  scope='Exact finite gcd beyond C_N D_(N,r)/(G_N H_(N,r)); no all-N divisibility or asymptotic exponent claimed.')
 (OUT/f'ceiling_{N}.json').write_text(json.dumps(record,indent=2))
 print(json.dumps(dict(N=N,seconds=record['runtime_seconds'],rows=[{k:x[k] for k in ('column','extra_gain_per_N','classified_gain_per_N','unfactored_remainder')} for x in rows])),flush=True)
 return record

def main():
 p=argparse.ArgumentParser();p.add_argument('--depths',nargs='+',type=int,default=[160,320,640,1280,2000,3000,4000,6000]);a=p.parse_args()
 for n in a.depths:
  path=OUT/f'ceiling_{n}.json'
  if not path.exists():run(n)
if __name__=='__main__':main()
