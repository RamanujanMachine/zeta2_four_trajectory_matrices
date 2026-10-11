# Actual block orders with retained prime residues

Status: NUMERICAL_CANDIDATE. These finite experiments concern one approximation sequence, not separate discoveries. No prior proof artifact was changed.

The input is the exact pair of rows `[[0,2,-1],[2,0,0]]`, the start `(1,1,1,0;1,1,1)`, direction `(10,9,11,-11;2,1,3)`, forward orientation, native 3×3 gauge, and column 0. For each depth, 89 genuine paths from the start to a cut vertex and then to the endpoint were supplied by the orders lane. Each suffix retains at least `2N` negative-upper steps. Every full 3×3 endpoint equality was checked there.

At a cut `W=A B`, this experiment forms the three terms `(R A)[r,i] B[i,0]` separately for each initial row. Their rational gcd gives the componentwise certificate. After dividing by that gcd, the three terms are integers. Keeping one or two prime residue digits permits an additional factor `p` or `p²` only when their residues sum to zero at that precision. The exact endpoint sum is used to validate the result, not to construct this bounded-retention certificate. Rational lcms then choose the certificate separately for each prime and row.

The table combines those certificates with the earlier six-shell normalization. All numbers are natural logarithms of denominator bounds; actual denominators are reduced.

| N | Earlier six shells | Componentwise orders | One retained digit | Two retained digits | Actual reduced log q |
|---:|---:|---:|---:|---:|---:|
| 20 | 1006.830013 | 969.294302 | 966.461089 | 966.461089 | 966.461089 |
| 40 | 2024.521715 | 1952.684660 | 1952.684660 | 1952.684660 | 1952.684660 |
| 80 | 3995.558516 | 3897.972570 | 3897.279423 | 3897.279423 | 3897.279423 |
| 160 | 7952.463445 | 7845.385158 | 7844.692011 | 7843.998864 | 7843.998864 |
| 320 | 15860.979328 | 15681.089752 | 15673.163149 | 15670.860564 | 15668.557979 |
| 640 | 31662.180409 | 31318.172451 | 31312.432658 | 31311.739511 | 31310.353216 |

At N=320, the remaining gap with two retained digits is a factor 10; at N=640 it is a factor 4. At N=20,40,80,160, two digits recover the exact denominator. These successes do not establish an asymptotic bound.

## What adaptation actually contributed

Prime-dependent selection gives a strict finite improvement. At N=640, the best fixed order with componentwise certificates has log-q bound 31402.610855814; prime-dependent selection gives 31318.172450748, improving the logarithmic bound by 84.438405065. At N=320 the corresponding improvement is 52.493230890. Most of this gain comes from small primes omitted from the asymptotic carry product.

An explicit crossing at N=640 uses these genuine multiplication routes:

- Route A reaches all positive upper and lower endpoint parameters while `x3=0`, then performs the complete negative-upper block.
- Route B first raises each of the three positive uppers by `3N`, then completes the positive uppers, lowers, and negative-upper block.

For p=23, the common valuation certificate improves from −9 with A to −6 with B. For p=73 it improves from −7 with B to −4 with A. Thus neither route dominates at both primes. Full recorded witnesses and their cut directions are in `prime_adaptation_witnesses.json`.

Independent row choice gives a strict path-only gain at N=40, p=491 with zero retained digits: cuts (3,3,3,-3;0,0,0)N and (3,3,3,0;0,0,0)N have row bounds (-1,-2) and (-2,0). The best shared minimum is -2, while independent rows achieve -1. This is the log(491)=6.19644412779452 entry in the raw comparison. The old arithmetic normalization already supplies this factor. **No further gain beyond that normalization** was found at any of the six depths, with zero, one, or two retained digits. Distinct row witnesses at other primes may be ties. The scope of each comparison matters.

## Large primes and the periodic extension

The componentwise certificates recover every eligible column-0 prime in the newly identified periodic lifts at N=80,160,320,640. At N=320 the lift primes are 139,149,167,281,283. At N=640 they are 269,337,439,443,463,491,521,523,557,563.

All those lift primes are already covered by Route A alone at N=320 and N=640. They therefore do not demonstrate a need to switch orders prime by prime. Separate from these finite route tests, `work/zeta2_order_adaptive/arithmetic/periodic_lift_proof.tex` gives a uniform extension of the existing finite-field readout argument. That extension uses the corrected column-dependent endpoints; it is not presented as a theorem about optimal multiplication orders.

One retained residue digit also captures p=277 at N=320 and p=311 at N=640, which lie outside the periodic lifts. These isolated additional factors remain numerical observations. They could be accidental or contribute only a negligible rate.

## Replay, scope, and next region

Run from the project root, using the environment containing python-flint:

```sh
work/.venv_4f3/bin/python work/zeta2_order_adaptive/arithmetic/retained_residues.py 640 work/zeta2_order_adaptive/orders/paths_640.jsonl
```

The source path checkpoints make the experiment resumable. The arithmetic postprocessor is deterministic and consumes only complete successful checkpoint records. Per-depth JSON records contain every improving prime, selected row/order, base valuation, retained residue digits, exact residue witnesses, actual valuation, and the strict adaptation comparisons.

Inspected: native `core.py`, existing `cuts.py`, final-negative-block cut checker, and all six new path checkpoints. Created: `retained_residues.py`, per-depth arithmetic JSON/logs, crossing-order witnesses, and the separate periodic-lift audit/proof fragments. Recovered: 89 equivalent endpoint decompositions at each of six depths. No new delta estimate was computed; reordering leaves the approximants and their measured deltas unchanged. No new uniform rate is inferred from the finite tables.

The next route-search region is the full-positive/full-lower cut with `x3=0`, plus upper plateaus `3N,4N,8N`, retaining the actual incoming rows. Test lifted primes at fresh depths 1280 and 2560, and test the isolated extra-factor locations near `N/p=320/277` and `640/311`. To seek row-adaptation gains beyond the existing normalization, enlarge the path family or change the retained lattice.
