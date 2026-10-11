# Code accompanying the complete ζ(2) CMF argument

This folder is self-contained and accompanies [the manuscript](../zeta2_complete_proof.tex) and its [PDF](../zeta2_complete_proof.pdf). It imports no code from the parent project.

The trajectory is `(10,9,11,-11;2,1,3)` from `(1,1,1,0;1,1,1)`, with initial rows `[[0,2,-1],[2,0,0]]`. The manuscript establishes the uniform matrix readout, block normalization, all six extra prime shells, analytic estimates, and the integer-separation argument. The exact scalar certificates below verify the constants used to obtain `mu(zeta(2)) < 4.62675`.

The finite matrix and congruence checks are diagnostics accompanying those arguments. Testing selected depths is not the justification for any all-depth statement.

## Setup and replay

Use Python 3.12. From this directory:

```sh
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -r requirements.txt
python run_checks.py
```

Dependencies are pinned, including RamanujanTools revision `e87622c8637b9a292364deea85cb201a00ca3ffc`. The native 3×3 CMF is also supplied as `core.py`; `rt_blocks.py` checks it independently through RamanujanTools. Installing the dependencies requires access to their package sources; running the checks does not access the network.

For a replay without the independent RamanujanTools comparison, run `python run_checks.py --skip-rt`. Each checker can also be run separately. The runner saves `verification.json`, individual JSON records, logs in `run_logs/`, and a SHA-256 `package_manifest.json`. Rerunning replaces these records, with timings as the only intended variation.

## Exact certificates and finite diagnostics

| Script | What it verifies |
|---|---|
| `chamber_certificate.py` | Exhaustive rational arrangement certificate: 390 constant floor cells covering the six shells and their two internal splits |
| `rate_certificate.py` | Directed rational enclosure of the carry-profile integral and the final arithmetic rate comparison |
| `analytic/certify_analytic_rates.py` | Exact limiting matrix and characteristic polynomial, root interval, observability determinant, and rational logarithmic enclosures |
| `toy_cmf.py` | Exact 2×2 conservation square and row/prime dependent arithmetic choices |
| `check_finite_formula.py` | Finite readout, polynomial functional, companion relation, shifts, and generator identities at 16 general vertices |
| `rt_blocks.py` | Both `t=3` and `t=4` multiplication routes at the requested depths; all nine endpoint entries agree |
| `check_local_kernel.py` | 2,229 exact normalized local polynomial values across all eight shell subregions, plus the local coefficient residues |
| `check_main_shell.py` | 1,693 eligible prime cases and 74 exact polynomial checks for the largest shell |
| `check_fifth_shell.py` | 473 eligible prime cases and 31 exact polynomial checks for the denominator-five shell |
| `check_shell_independent.py` | Separate standard-library implementation: 28 cases and 1,500 exact divided-sum nodes |

The three certificates in the first rows implement finite computations whose exhaustive scope is justified in the manuscript. For example, the arrangement certificate checks every interval and boundary on which the relevant floor expressions can change; it does not merely sample values of `N` and `p`. The contour estimates, asymptotic recurrence argument, and quantified divisibility proof are written arguments, not claims inferred from the diagnostic tests.

The recorded replay completed all ten checkers successfully with Python 3.12.14. The RamanujanTools replay tested both four-block orders at N=1,2,3. See `verification.json` for exit codes and per-check timings.

## Digit-pattern certificate table

Write `x=N/p`, `a=floor(8x)`, `M=floor(11x)`, `h=phi(x)`. At every residue with minimum carry `h`, the remaining data are constant on each region. Here `e=1` means the residue exceeds `d=11N-Mp`, and the triples are ordered by `u=9,10,11`.

| Region for x | a | M | h | e | Upper digits λ | Low-digit carries δ | K=3a−M+h |
|---|---:|---:|---:|---:|---|---|---:|
| (1/8, 2/13) | 1 | 1 | 0 | 0 | (1,1,1) | (0,0,0) | 2 |
| (2/9, 3/13) | 1 | 2 | 2 | 0 | (2,2,2) | (1,1,0) | 3 |
| (3/10, 4/13) | 2 | 3 | 1 | 0 | (2,3,3) | (0,1,0) | 4 |
| (3/8, 5/13) | 3 | 4 | 0 | 0 | (3,3,4) | (0,0,0) | 5 |
| (4/9, 5/11) | 3 | 4 | 1 | 0 | (4,5,5) | (0,1,0) | 6 |
| (5/11, 6/13) | 3 | 5 | 2 | 1 | (4,5,5) | (0,1,0) | 6 |
| (8/9, 10/11) | 7 | 9 | 0 | 0 | (8,9,10) | (0,0,0) | 12 |
| (10/11, 12/13) | 7 | 10 | 1 | 1 | (8,9,10) | (0,0,0) | 12 |

The internal split values `5/11` and `10/11` cannot arise from eligible primes with `p²>50N`. The column correction is the strict inequality `13N+r<Kp`. It makes the finite-field polynomial degree less than `p−1`, so its complete residue sum vanishes.

## Provenance

`source_manifest.json` records source files, original hashes, and portability edits. Arithmetic formulas are unchanged. The package does not modify the archive or compute a new delta estimate.
