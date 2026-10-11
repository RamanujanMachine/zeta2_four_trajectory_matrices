"""Checkpointed exact search of genuine long-block native path orders.

The certificate is gcd_i((R A)[r,i] B[i,0]); no cancellation at the cut
is used. A and B are entire native products and A B is checked against W.
This searches estimates of the SAME approximant, never new approximants.
"""
import argparse, json, math, random, sys, time
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'work/zeta2_orders_10911'))
from core import START, R, segment, endpoint, C, content, fmpq_mat, fmpq
from cuts import qgcd, qlcm, logabs
from arithmetic import sieve
from profile import phi
from shells import SHELLS

sys.set_int_max_str_digits(0)
OUT = ROOT / 'results/zeta2_order_adaptive'


def baseline(N):
    D = math.lcm(*range(1, 12*N+1))*math.lcm(*range(1, 13*N+1))
    G = H = 1
    for p in sieve(13*N):
        if p*p <= 50*N:
            continue
        G *= p**phi(Fraction(N, p))
        if any(a*N < p < b*N for a,b in SHELLS):
            H *= p
    return fmpq(G*H, C(endpoint(N))*D)


def vertices(N, count, seed):
    rng = random.Random(seed)
    seen = set()
    while len(seen) < count:
        # Quarter-N coordinates and deliberately unequal positive uppers.
        upper = [rng.randint(12, 4*u)*N//4 for u in (10,9,11)]
        lower = [rng.randint(0, 4*v)*N//4 for v in (2,1,3)]
        maxm = min(9*N, sum(upper)-sum(lower)-1)
        m = rng.randint(1, maxm)
        ds = tuple(upper + [-m] + lower)
        if ds in seen:
            continue
        seen.add(ds)
        yield tuple(s+d for s,d in zip(START,ds))


def run(N, count, seed):
    OUT.mkdir(parents=True, exist_ok=True)
    started = time.perf_counter()
    W = segment(START, endpoint(N))
    Y = R*W
    actual = qgcd(Y[0,0], Y[1,0])
    base = baseline(N)
    assert (actual/base).denominator == 1
    path = OUT / f'random_checkpoint_N{N}_seed{seed}.jsonl'
    cached = {tuple(x['vertex']):x for x in map(json.loads,path.read_text().splitlines())} if path.exists() else {}
    records = []
    for i,w in enumerate(vertices(N,count,seed)):
        if w in cached:
            record = cached[w]
        else:
            A = segment(START,w)
            B = segment(w,endpoint(N))
            assert A*B == W
            U = R*A
            row = [content(fmpq_mat([[U[r,k]*B[k,0] for k in range(3)]])) for r in range(2)]
            common = qgcd(*row)
            assert (actual/common).denominator == 1
            record = dict(vertex=w, row_contents=list(map(str,row)),
                          common_content=str(common),
                          log_q_bound=logabs(Y[1,0])-logabs(common),
                          negative_moves_in_prefix=-w[3], negative_moves_in_suffix=11*N+w[3],
                          all_nine_endpoint_entries_match=True)
            with path.open('a') as f:
                f.write(json.dumps(record)+'\n')
        records.append(record)
        if (i+1)%50 == 0:
            print(json.dumps(dict(N=N,completed=i+1,seconds=time.perf_counter()-started)),flush=True)
    best = min(records,key=lambda z:z['log_q_bound'])
    rowbest = [fmpq(0),fmpq(0)]
    commonbest = fmpq(0)
    for record in records:
        for r in range(2):
            rowbest[r] = qlcm(rowbest[r],fmpq(record['row_contents'][r]))
        commonbest = qlcm(commonbest,fmpq(record['common_content']))
    adaptive = qgcd(*rowbest)
    combined = qlcm(base,adaptive)
    assert (actual/combined).denominator == 1
    gain = combined/base
    assert gain.denominator == 1
    result = dict(N=N,status='NUMERICAL_CANDIDATE',seed=seed,cuts=count,
        minimum_negative_suffix=2*N,base_content=str(base),
        best_fixed_cut=best,
        prime_adaptive_same_row_path_log_q_bound=logabs(Y[1,0])-logabs(commonbest),
        prime_and_row_adaptive_log_q_bound=logabs(Y[1,0])-logabs(adaptive),
        baseline_six_shell_log_q_bound=logabs(Y[1,0])-logabs(base),
        combined_log_q_bound=logabs(Y[1,0])-logabs(combined),
        actual_reduced_log_q=math.log(int((Y[0,0]/Y[1,0]).denominator)),
        extra_factor_over_six_shell=str(gain),
        gain_log_over_N=logabs(gain)/N,
        adaptation_only_row_gain=logabs(adaptive/commonbest),
        seconds=time.perf_counter()-started)
    (OUT/f'random_N{N}_seed{seed}.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('best_fixed_cut','base_content','extra_factor_over_six_shell')}),flush=True)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--depths',nargs='+',type=int,default=[20,40,80,160])
    ap.add_argument('--count',type=int,default=240)
    ap.add_argument('--seed',type=int,default=731109)
    args = ap.parse_args()
    for N in args.depths:
        run(N,args.count,args.seed)
