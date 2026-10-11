"""Held-out exact finite test of column-shifted periodic shell lifts.

Training interpretation is the six base intervals; these tests do not establish
an all-depth assertion. The coefficient integrated below is a candidate.
"""
import json,math,sys
from fractions import Fraction as F
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'work/zeta2_orders_10911'))
from arithmetic import sieve
import mpmath as mp
OUT=Path(__file__).resolve().parent
BASE=((2,8,1),(3,9,2),(4,10,3),(5,8,3),(6,9,4),(12,9,8))
def membership(N,r,p):
 t=N//p
 if not t:return None
 for k,a,b in BASE:
  if (13*t+k)*p>13*N+r and (b+a*t)*p<a*N:return (t,k,a,b)
 return None

def run():
 records=[]
 for N in [160,320,640,1280,2000,3000,4000,6000]:
  data=json.loads((OUT/f'ceiling_{N}.json').read_text())
  rowresults=[]
  for row in data['rows']:
   r=row['column'];remaining={f['p']:f['v'] for f in row['factors'] if f['class_']=='eligible_prime'}
   pred=[];fail=[];gain=0
   for p in sieve(13*N):
    if p*p<=50*N:continue
    member=membership(N,r,p)
    if member is None:continue
    pred.append(dict(p=p,t=member[0],k=member[1],extra_actual=remaining.get(p,0)))
    if not remaining.get(p,0):fail.append(p)
    else:remaining[p]-=1
    gain+=math.log(p)/N
   uncovered=[dict(p=p,v=v) for p,v in remaining.items() if v]
   rowresults.append(dict(column=r,predicted_prime_count=len(pred),failures=fail,predicted_log_gain_per_N=gain,
                          uncovered=uncovered,predictions=pred))
  record=dict(N=N,rows=rowresults);records.append(record)
  print(json.dumps(dict(N=N,rows=[{k:v for k,v in row.items() if k!='predictions'} for row in rowresults])),flush=True)
 mp.mp.dps=60
 lifts=sum(mp.digamma(1+mp.mpf(k)/13)-mp.digamma(1+mp.mpf(b)/a) for k,a,b in BASE)
 a=mp.mpf('38.168732909606170552329029927825357155');E=mp.mpf('62.636575041536217199981441047831');c=mp.mpf('10.9299051423483')
 result=dict(status='NUMERICAL_CANDIDATE' if not any(x['failures'] for r in records for x in r['rows']) else 'REJECTED',
  periodic_extra_gain_candidate=str(lifts),projected_mu_if_uniform=str(E/(E-a-c+lifts)),
  formula='t=floor(N/p)>=1; (13N+r)/(13t+k)<p<aN/(b+at), base (k,a,b)=(2,8,1),(3,9,2),(4,10,3),(5,8,3),(6,9,4),(12,9,8)',
  caveat='Finite exact evidence only. Coefficient from formal PNT sum of proposed bands; no uniform divisibility or tail argument supplied.',records=records)
 (OUT/'periodic_shell_probe.json').write_text(json.dumps(result,indent=2))
 print(json.dumps({k:v for k,v in result.items() if k!='records'},indent=2))
if __name__=='__main__':run()
