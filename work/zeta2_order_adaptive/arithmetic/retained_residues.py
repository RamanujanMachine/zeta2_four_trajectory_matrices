"""Prime/row-adapted long-block bounds retaining at most two residue digits.

Consumes exact genuine START->cut->endpoint products from the orders lane.
For terms t_i=prefix_row_i*suffix_column_i, divide by their rational gcd g.
The integral vector t/g has gcd one. Keep g as the componentwise certificate;
add p or p^2 only when its three residues sum to zero modulo p or p^2.
The bound never uses the exact endpoint sum. That sum is checked separately.
Results are finite NUMERICAL_CANDIDATE diagnostics, not uniform estimates.
"""
import argparse,json,math,sys,time
from fractions import Fraction
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'work/zeta2_orders_10911'))
from core import R,START,endpoint,segment,C,fmpq,content,fmpq_mat
from arithmetic import sieve
from profile import phi
from cuts import qgcd,qlcm,logabs
sys.set_int_max_str_digits(0)
OUT=ROOT/'results/zeta2_order_adaptive/arithmetic'
SHELLS=[(Fraction(13,2),Fraction(8)),(Fraction(13,3),Fraction(9,2)),
        (Fraction(13,4),Fraction(10,3)),(Fraction(13,5),Fraction(8,3)),
        (Fraction(13,6),Fraction(9,4)),(Fraction(13,12),Fraction(9,8))]
INF=10**9

def vp(q,p):
 if not q:return INF
 val=0
 for s,x in [(1,abs(int(q.numerator))),(-1,int(q.denominator))]:
  while x%p==0:x//=p;val+=s
 return val

def baseline(N):
 D=math.lcm(*range(1,12*N+1))*math.lcm(*range(1,13*N+1));G=H=1
 for p in sieve(13*N):
  if p*p<=50*N:continue
  G*=p**phi(Fraction(N,p))
  if any(lo*N<p<hi*N for lo,hi in SHELLS):H*=p
 return fmpq(G*H,C(endpoint(N))*D)

def unpack(rec):
 # The producer emits the compact checkpoint schema; aliases allow older caches.
 prefix=rec.get('prefix_rows',rec.get('prefix'))
 suffix=rec.get('suffix_column',rec.get('suffix'))
 if prefix is None or suffix is None:raise KeyError(f'missing row/vector fields: {list(rec)}')
 if suffix and isinstance(suffix[0],list):suffix=[row[0] for row in suffix]
 return [[fmpq(v) for v in row] for row in prefix],[fmpq(v) for v in suffix]

def run(N,path):
 begun=time.perf_counter();OUT.mkdir(parents=True,exist_ok=True)
 raw=R*segment(START,endpoint(N));truecontent=qgcd(raw[0,0],raw[1,0]);old=baseline(N)
 assert (truecontent/old).denominator==1
 primes=sieve(13*N+2)
 fixed_best=[(fmpq(0),None) for _ in range(3)]
 joint=[old,old,old];pure_joint=[fmpq(0),fmpq(0),fmpq(0)]
 best=[[old,old] for _ in range(3)];pure=[[fmpq(0),fmpq(0)] for _ in range(3)]
 selected=[[{} for r in range(2)] for cap in range(3)]
 for cap in range(3):
  for r in range(2):
   for p in primes:selected[cap][r][p]={'valuation':vp(old,p),'name':'six_shell_baseline','retained_digits':0}
 source=[]
 for line in path.read_text().splitlines():
  try:rec=json.loads(line)
  except json.JSONDecodeError:continue
  if rec.get('status')=='COMPUTATION_FAILED':continue
  if rec.get('prefix_rows',rec.get('prefix')) is None:continue
  source.append(rec)
 for rec in source:
  prefix,suffix=unpack(rec);name=rec['name'];cut_caps=[[],[],[]]
  for r in range(2):
   terms=[prefix[r][i]*suffix[i] for i in range(3)]
   assert sum(terms,fmpq(0))==raw[r,0],(N,name,r)
   g=content(fmpq_mat([terms]));integers=[]
   for t in terms:
    u=t/g;assert u.denominator==1;integers.append(int(u.numerator))
   factors=[1,1,1]
   for p in primes:
    residue1=sum(u%p for u in integers)%p
    delta=0 if residue1 else (1 if sum(u%(p*p) for u in integers)%(p*p) else 2)
    v=vp(g,p)
    for cap in range(3):
     retained=min(cap,delta);factors[cap]*=p**retained
     value=v+retained;current=selected[cap][r][p]
     if value>current['valuation']:
      modulus=p**retained if retained else p
      selected[cap][r][p]={
       'valuation':value,'name':name,'base_valuation':v,'retained_digits':retained,
       'normalized_term_residues':[u%modulus for u in integers],
       'modulus':modulus,'direction_to_cut':rec.get('direction_to_cut',rec.get('cut_direction')),
       'cut_vertex':rec.get('cut_vertex',rec.get('vertex'))}
   for cap in range(3):
    gcap=g*factors[cap]
    assert (raw[r,0]/gcap).denominator==1,(N,name,r,cap)
    best[cap][r]=qlcm(best[cap][r],gcap);pure[cap][r]=qlcm(pure[cap][r],gcap)
    cut_caps[cap].append(gcap)
  for cap in range(3):
   pair_content=qgcd(*cut_caps[cap]);joint[cap]=qlcm(joint[cap],pair_content);pure_joint[cap]=qlcm(pure_joint[cap],pair_content)
   fixed_bound=qlcm(old,pair_content)
   if not fixed_best[cap][0] or logabs(fixed_bound)>logabs(fixed_best[cap][0]):fixed_best[cap]=(fixed_bound,name)
 reports=[]
 for cap in range(3):
  bound=qgcd(*best[cap]);pbound=qgcd(*pure[cap]);assert (truecontent/bound).denominator==1
  gains=[]
  for p in primes:
   bv=vp(old,p);nv=vp(bound,p)
   if nv>bv:
    gains.append({'prime':p,'old_common_valuation':bv,'new_common_valuation':nv,
      'actual_common_valuation':vp(truecontent,p),'gain_exponent':nv-bv,
      'best_same_order_common_valuation':vp(joint[cap],p),
      'strict_row_adaptation_gain':nv-vp(joint[cap],p),
      'large_prime':p*p>50*N,
      'rows':[dict(selected[cap][r][p],row=r,actual_valuation=vp(raw[r,0],p)) for r in range(2)]})
  reports.append({'retained_digit_cap':cap,'combined_content':str(bound),
    'log_q_bound':logabs(raw[1,0])-logabs(bound),
    'pure_order_log_q_bound':logabs(raw[1,0])-logabs(pbound),
    'log_gain_over_six_shell':logabs(bound/old),
    'gap_above_actual_log_q':logabs(truecontent/bound),
    'strict_row_adaptation_log_gain':logabs(bound/joint[cap]),
    'pure_order_strict_row_adaptation_log_gain':logabs(pbound/pure_joint[cap]),
    'same_order_for_both_rows_log_q_bound':logabs(raw[1,0])-logabs(joint[cap]),
    'best_fixed_order':fixed_best[cap][1],
    'best_fixed_order_log_q_bound':logabs(raw[1,0])-logabs(fixed_best[cap][0]),
    'strict_prime_adaptation_log_gain':logabs(bound/fixed_best[cap][0]),
    'large_prime_log_gain_over_six_shell':sum(w['gain_exponent']*math.log(w['prime']) for w in gains if w['large_prime']),
    'strict_gain_prime_count':len(gains),'witnesses':gains})
 report={'N':N,'status':'NUMERICAL_CANDIDATE','source_checkpoint':str(path.relative_to(ROOT)),
  'orders_consumed':len(source),'prime_range':[2,13*N+2],
  'six_shell_log_q_bound':logabs(raw[1,0])-logabs(old),
  'actual_reduced_log_q':logabs(raw[1,0])-logabs(truecontent),
  'levels':reports,'runtime_seconds':time.perf_counter()-begun,
  'caveat':'Finite checkpoint certificates with bounded residue retention; no new asymptotic exponent or all-N result is inferred.'}
 dest=OUT/f'retained_{N}.json';dest.write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({k:v for k,v in report.items() if k!='levels'},indent=2))
 for r in reports:print(json.dumps({k:v for k,v in r.items() if k not in ['combined_content','witnesses']},indent=2))
 return report

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('N',type=int);ap.add_argument('checkpoint',type=Path)
 args=ap.parse_args();run(args.N,args.checkpoint.resolve())
