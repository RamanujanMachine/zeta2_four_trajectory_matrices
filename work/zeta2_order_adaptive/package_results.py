from pathlib import Path
import hashlib,json,zipfile

ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
OUT=ROOT/'results/zeta2_order_adaptive'

report='''ADAPTIVE ORDERS AND THE ZETA(2) ARITHMETIC IMPROVEMENT

Result: the new periodic-divisor lemma, together with the preceding full
manuscript, gives mu(zeta(2)) <= 62636575/13646619 < 4.589897.
Read zeta2_adaptive_orders_addendum.pdf/tex. The earlier complete proof
is included unchanged in the bundle to supply the exact readout, baseline
arithmetic, analytic estimates, and nonvanishing argument.

What the actual ordering experiments establish
--------------------------------------------
All 89 structured paths at six depths and 240 seeded random paths at seven
depths were checked using exact native 3x3 matrix identities. They reach
the same endpoint, and the suffix retains at least 2N negative-upper moves.
Prime-dependent path selection strictly improves finite certificates.
Different rows can have disjoint maximizing path sets. At N40,p491,
independent row selection improves the path-only bound by491; the prior
arithmetic normalization already certifies that factor. Independent row
selection gave no additional gain BEYOND that prior normalization.
At N=320 and 640, the new lifted large-prime factors already have one
shared full-preparation order. Thus the improved asymptotic bound is not
evidence that different orders by row or prime are necessary.

Reproduction (from the extracted bundle root)
-------------------------------------------
Install python-flint==0.9.0 and mpmath==1.3.0 in a Python environment.
  python work/zeta2_order_adaptive/verify_order_witness.py
  python work/zeta2_order_adaptive/ceiling/lift_density_certificate.py
  python work/zeta2_order_adaptive/ceiling/periodic_shell_probe.py
  python work/zeta2_order_adaptive/check_lifted_kernel.py
  python work/zeta2_order_adaptive/orders/adaptive_paths.py 20 40 80 160 320 640
  python work/zeta2_order_adaptive/random_cuts.py --depths 20 40 80 160 320 640 1280 --count 240
Path searches resume from JSONL checkpoints. To replay uncached paths,
move their checkpoints aside in your extracted copy. The native input
matrices and scalar arithmetic records needed by the ceiling analyzer
are included at their original relative paths.

The scripts test finite certificates; they are not proof-assistant code.
The all-N extension is the translated finite-field argument in the text.
The short rate certificate uses integer divisions and rational bounds,
not floating-point assumptions.

Required project handoff
------------------------
1. Files inspected: the newly supplied (4).tex is zero bytes; the previous
   nonempty (3).tex was read as background. Reused the native core and
   order/cut scripts, exact matrices and six-shell records under
   work/results zeta2_orders_10911, the full previous proof and its exact
   certificates, and the new structured/random/residue/ceiling records.
   The prior recursive archive inventory was reused; archive was not edited.
2. Files created: new source, exact checkpoints, audit notes, logs and
   certificates under work/zeta2_order_adaptive; addendum source/PDF,
   random/residue records, this report, verification and manifest under
   results/zeta2_order_adaptive; a reproducibility ZIP under results.
3. Experiments recovered: the same native pFq(4,3,1) start
   (1,1,1,0;1,1,1), direction (10,9,11,-11;2,1,3), forward orientation,
   R rows (0,2,-1),(2,0,0), primarily column 0; all three columns in
   the periodic-divisor checks. No new approximation sequence is claimed.
4. Top delta values: no new delta search. Previous delta3000=.278673337629,
   delta4000=.279047437501, delta6000=.278946586656; last-three slope
   .279152068816. Changing the multiplication path leaves these unchanged.
5. Rejected/limited interpretations: independent row choice has no extra
   common-factor gain beyond the previous normalization. Most finite improvements
   involve excluded small primes and cannot be treated as a constant
   exponential saving. The earlier unshifted periodic guess remains
   rejected; the column-corrected inequality repairs its boundary error.
6. Numerical uncertainties: finite path optimality and any further residual
   factors remain numerical questions. The displayed bound uses the written
   universal lemma and exact rational rate certificate; no formal proof
   assistant is used. Neither global path optimality nor necessity of
   adaptive orders is claimed.
7. Exact next region: same trajectory, N=640,1280,2560, unequal upper and
   lower cut progress in quarter-N increments, negative suffix >=2N,
   one/two retained p-adic digits. Target eligible primes outside the
   periodic divisor, including residual 1583 (all columns) and 11743
   (column 0) at N=6000. Require a new uniform rule before improving mu.
'''
(OUT/'REPORT.txt').write_text(report)
(OUT/'requirements.txt').write_text('python-flint==0.9.0\nmpmath==1.3.0\n')

structured=[]
for N in (20,40,80,160,320,640):
 d=json.loads((HERE/f'orders/summary_{N}.json').read_text())
 structured.append({k:d[k] for k in ('N','path_count','baseline_log_q_bound','improved_log_q_bound','actual_reduced_log_q','gain_factor_from_row_choice')})
random=[]
for N in (20,40,80,160,320,640,1280):
 d=json.loads((OUT/f'random_N{N}_seed731109.json').read_text())
 random.append({k:d[k] for k in ('N','cuts','combined_log_q_bound','actual_reduced_log_q','adaptation_only_row_gain')})
kernel=json.loads((HERE/'check_lifted_kernel.json').read_text())
witness=json.loads((HERE/'verify_order_witness.json').read_text())
rate=json.loads((HERE/'ceiling/lift_density_certificate.json').read_text())
pattern=json.loads((HERE/'ceiling/periodic_shell_probe.json').read_text())
assert kernel['all_assertions_passed'] and witness['all_assertions_passed'] and rate['inequalities_verified']
assert all(not x['failures'] for r in pattern['records'] for x in r['rows'])
checks=dict(structured=structured,random=random,total_native_path_checks=6*89+7*240,
            lifted_kernel_cases=len(kernel['cases']),lifted_kernel_S_checks=kernel['S_checks'],
            short_witness_passed=True,exact_density_certificate_passed=True,
            periodic_pattern_depths=[r['N'] for r in pattern['records']],periodic_pattern_columns=[0,1,2],
            pdf_pages=7,visually_reviewed_pages=list(range(1,8)),compile_success=True,
            layout_or_reference_warnings=[],proof_assistant_used=False)
(OUT/'verification.json').write_text(json.dumps(checks,indent=2)+'\n')

files=[]
for base in (HERE,OUT,ROOT/'results/zeta2_complete_proof'):
 for p in base.rglob('*'):
  if p.is_file() and p.name!='package_run.log' and not any(x in p.parts for x in ('build','__pycache__')) and p.suffix not in ('.pyc','.zip'):
   files.append(p)
for name in ('core','cuts','arithmetic','profile','shells','reproduce'):
 files.append(ROOT/f'work/zeta2_orders_10911/{name}.py')
for N in (160,320,640,1280,2000,3000,4000,6000):
 for name in ('matrix','depth'):
  files.append(ROOT/f'results/zeta2_orders_10911/{name}_{N}.json')
 p=ROOT/f'results/zeta2_orders_10911/arithmetic_{N}.json'
 if not p.exists():p=ROOT/f'results/zeta2_orders_10911/shells_{N}.json'
 files.append(p)
files += [ROOT/'results/zeta2_proof_strategy/rate_certificate.json',
          ROOT/'work/zeta2_completion/analytic/analytic_certificates.json']
files=sorted(set(files))
manifest={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files if p.name!='artifact_manifest.json'}
(OUT/'artifact_manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
files=sorted(set(files+[OUT/'artifact_manifest.json']))
dest=ROOT/'results/zeta2_adaptive_orders_bundle.zip'
with zipfile.ZipFile(dest,'w',zipfile.ZIP_DEFLATED,compresslevel=6) as z:
 for p in files:z.write(p,p.relative_to(ROOT))
with zipfile.ZipFile(dest) as z:assert z.testzip() is None
print(json.dumps(dict(bundle=str(dest),files=len(files),bytes=dest.stat().st_size,verification=checks),indent=2))
