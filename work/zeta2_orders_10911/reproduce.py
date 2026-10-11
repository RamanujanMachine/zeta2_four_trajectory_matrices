"""Reproduce the user's exact 4F3 zeta(2) approximants. Requires python-flint."""
import argparse,csv,json,math,sys,time
from pathlib import Path
from flint import arb,ctx
from core import *
sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent
OUT=HERE if (HERE/'candidate.json').exists() else HERE.parents[1]/'results/zeta2_orders_10911'

def write_json(p,data):
    temp=p.with_suffix('.tmp'); temp.write_text(json.dumps(data,indent=2)); temp.replace(p)

def score(W,N,seconds):
    Y=R*W; records=[]
    height=max(max(len(str(abs(int(W[i,j].numerator)))),len(str(W[i,j].denominator)))
               for i in range(3) for j in range(3))
    for j in range(3):
        if Y[1,j]==0: continue
        r=Y[0,j]/Y[1,j]; p=int(r.numerator); q=int(r.denominator)
        scores=[]; base=max(100,2*len(str(q))+100)
        for prec in (base,base+100):
            ctx.dps=prec
            err=abs(arb.pi()**2/6-arb(p)/arb(q))
            if not err>0: raise ArithmeticError('unresolved error')
            E=-err.log(); H=arb(q).log(); delta=E/H-1
            scores.append(dict(precision_dps=prec,delta=float(delta),delta_ball=delta.str(22),
                               error=err.str(22),digits_correct=float(E/arb(10).log())))
        assert abs(scores[0]['delta']-scores[1]['delta'])<1e-12
        records.append(dict(N=N,column=j,p=str(p),q=str(q),log_q=float(H),
                            delta=scores[-1]['delta'],error=scores[-1]['error'],
                            digits_correct=scores[-1]['digits_correct'],precision_checks=scores,
                            runtime_seconds=seconds,matrix_entry_height_digits=height))
    return records

def main():
    parser=argparse.ArgumentParser(); parser.add_argument('--depths',nargs='+',type=int,default=[20,40,80,160,320])
    args=parser.parse_args(); OUT.mkdir(parents=True,exist_ok=True)
    for N in args.depths:
        result=OUT/f'depth_{N}.json'
        if result.exists(): print('cached',N,flush=True); continue
        start=time.perf_counter(); W=segment(START,endpoint(N)); elapsed=time.perf_counter()-start
        rows=score(W,N,elapsed)
        write_json(OUT/f'matrix_{N}.json',encode(W))
        write_json(result,dict(rows=rows,rows_content=str(content(R*W)),matrix_content=str(content(W))))
        print(json.dumps({k:v for k,v in rows[0].items() if k not in ('p','q','precision_checks')}),flush=True)
    records=[]
    for p in sorted(OUT.glob('depth_*.json')): records+=json.loads(p.read_text())['rows']
    records.sort(key=lambda r:(r['N'],r['column']))
    fields=['N','column','p','q','log_q','delta','error','digits_correct','runtime_seconds','matrix_entry_height_digits']
    with (OUT/'approximants.csv').open('w') as f:
        writer=csv.DictWriter(f,fieldnames=fields,extrasaction='ignore'); writer.writeheader(); writer.writerows(records)
    slopes={}
    for col in range(3):
        rows=[r for r in records if r['column']==col]
        for size in (len(rows),3):
            a=rows[-size:]
            if len(a)<2: continue
            def slope(key):
                xm=sum(r['N'] for r in a)/len(a); ym=sum(r[key] for r in a)/len(a)
                return sum((r['N']-xm)*(r[key]-ym) for r in a)/sum((r['N']-xm)**2 for r in a)
            slopes[f'column_{col}_last_{size}']=slope('digits_correct')*math.log(10)/slope('log_q')-1
    write_json(OUT/'delta_summary.json',dict(slopes=slopes,depths=sorted(set(r['N'] for r in records))))

if __name__=='__main__': main()
