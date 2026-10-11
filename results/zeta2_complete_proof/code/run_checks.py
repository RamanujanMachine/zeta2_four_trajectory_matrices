#!/usr/bin/env python3
"""Replay the self-contained certificates and diagnostics accompanying the proof.

Dependencies must already be installed. All subprocesses use this interpreter;
outputs remain in this directory. No dependency installation or network access.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--skip-rt', action='store_true',
                        help='Omit only the optional independent RamanujanTools replay.')
    parser.add_argument('--rt-depths', type=int, nargs='+', default=[1, 2, 3])
    args = parser.parse_args()
    logs = HERE / 'run_logs'
    logs.mkdir(exist_ok=True)
    jobs = [
        ['toy_cmf.py'],
        ['check_finite_formula.py'],
        ['check_main_shell.py'],
        ['check_fifth_shell.py'],
        ['check_shell_independent.py'],
        ['rate_certificate.py'],
        ['chamber_certificate.py'],
        ['check_local_kernel.py'],
        ['analytic/certify_analytic_rates.py'],
    ]
    if not args.skip_rt:
        jobs.append(['rt_blocks.py', '--depths', *map(str, args.rt_depths)])

    def run(job):
        began = time.perf_counter()
        proc = subprocess.run([sys.executable, *job], cwd=HERE,
                              text=True, capture_output=True)
        name = Path(job[0]).stem
        (logs / (name + '.log')).write_text(proc.stdout + proc.stderr)
        if name == 'toy_cmf' and proc.returncode == 0:
            (HERE / 'toy_cmf_checks.json').write_text(proc.stdout)
        return {'script': job[0], 'arguments': job[1:],
                'exit_code': proc.returncode,
                'elapsed_seconds': time.perf_counter() - began,
                'log': str(Path('run_logs') / (name + '.log'))}

    records = []
    with ThreadPoolExecutor(max_workers=4) as pool:
        pending = [pool.submit(run, job) for job in jobs]
        for future in as_completed(pending):
            record = future.result()
            records.append(record)
            print(json.dumps(record), flush=True)
    records.sort(key=lambda record: record['script'])
    report = {
        'all_executed_checks_passed': all(r['exit_code'] == 0 for r in records),
        'python_version': sys.version,
        'checks': records,
        'scope': ('Exact finite certificates for the floor arrangements, logarithmic '
                  'enclosures, and final scalar comparison, together with finite '
                  'matrix and congruence diagnostics. Uniform mathematical '
                  'arguments are in ../zeta2_complete_proof.tex.'),
    }
    (HERE / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    paths = sorted(set(HERE.glob('*.py')) | set(HERE.glob('*.json')) |
                   set(HERE.glob('*.md')) | set(HERE.glob('requirements.txt')) |
                   set((HERE/'analytic').glob('*.py')) |
                   set((HERE/'analytic').glob('*.json')) |
                   set(logs.glob('*.log')))
    manifest = [{'path': str(p.relative_to(HERE)),
                 'sha256': hashlib.sha256(p.read_bytes()).hexdigest()}
                for p in paths if p.name != 'package_manifest.json']
    (HERE/'package_manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
    return 0 if report['all_executed_checks_passed'] else 1


if __name__ == '__main__':
    sys.exit(main())
