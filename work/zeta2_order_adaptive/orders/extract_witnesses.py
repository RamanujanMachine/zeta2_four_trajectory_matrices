"""Require incompatible maximizer sets, rather than arbitrary tie choices."""
import json,sys
from itertools import combinations
from pathlib import Path
from adaptive_paths import OUT,baseline,fmpq,qlcm,qgcd,vp,logabs,sieve


def run(N):
    rows=[z for z in map(json.loads,(OUT/f'paths_{N}.jsonl').read_text().splitlines())
          if z['status']=='NUMERICAL_CANDIDATE']
    base=baseline(N);contents=[list(map(fmpq,z['row_contents']))for z in rows]
    effective=[qlcm(base,qgcd(*c))for c in contents]
    best=max(range(len(rows)),key=lambda i:logabs(effective[i]))
    primes=[];rowconflicts=[]
    for p in sieve(50*N+50):
        vv=[[vp(c[r],p)for r in range(2)]for c in contents]
        maxima=[max(v[r]for v in vv)for r in range(2)]
        sets=[{i for i,v in enumerate(vv)if v[r]==maxima[r]}for r in range(2)]
        common=max(min(v)for v in vv);bv=vp(base,p)
        if sets[0].isdisjoint(sets[1]):
            i=min(sets[0]);j=min(sets[1])
            rowconflicts.append(dict(prime=p,maximal_row_bounds=maxima,
                                     numerator_best_path=rows[i]['name'],numerator_path_bounds=vv[i],
                                     denominator_best_path=rows[j]['name'],denominator_path_bounds=vv[j],
                                     common_same_path_bound=common,
                                     common_independent_rows_bound=min(maxima)))
        if common>bv:
            winners={i for i,v in enumerate(vv)if min(v)==common}
            primes.append(dict(prime=p,baseline=bv,best_bound=common,winners=winners,vectors=vv))
    incompatible=[]
    for a,b in combinations(primes,2):
        if not a['winners'].isdisjoint(b['winners']):continue
        i=min(a['winners']);j=min(b['winners'])
        incompatible.append(dict(primes=[a['prime'],b['prime']],baseline_bounds=[a['baseline'],b['baseline']],
                                 optimal_common_bounds=[a['best_bound'],b['best_bound']],
                                 first_path=rows[i]['name'],first_direction=rows[i]['direction_to_cut'],
                                 first_path_row_bounds=[a['vectors'][i],b['vectors'][i]],
                                 second_path=rows[j]['name'],second_direction=rows[j]['direction_to_cut'],
                                 second_path_row_bounds=[a['vectors'][j],b['vectors'][j]],
                                 maximizing_path_sets_disjoint=True))
        if len(incompatible)==10:break
    summary=json.loads((OUT/f'summary_{N}.json').read_text())
    report=dict(N=N,best_single_path=rows[best]['name'],best_single_direction=rows[best]['direction_to_cut'],
                best_single_gain_factor=str(effective[best]/base),
                prime_adaptation_gain_over_best_single=str(fmpq(summary['same_path_prime_envelope_content'])/effective[best]),
                prime_adaptation_log_gain=logabs(fmpq(summary['same_path_prime_envelope_content']))-logabs(effective[best]),
                row_adaptation_common_gain_factor=summary['gain_factor_from_row_choice'],
                incompatible_prime_witnesses=incompatible,row_maximum_conflicts=rowconflicts)
    (OUT/f'witnesses_{N}.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items()if k not in('row_maximum_conflicts','incompatible_prime_witnesses')},indent=2))
    print('prime witness:',incompatible[:1]);print('row conflict:',rowconflicts[:1])


if __name__=='__main__':
    for N in map(int,sys.argv[1:]or[20,40,80,160]):run(N)
