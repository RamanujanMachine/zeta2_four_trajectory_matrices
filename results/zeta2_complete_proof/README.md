# CMF arithmetic proof for the specified ζ(2) trajectory

The standalone article `zeta2_complete_proof.tex` and its 22-page PDF give the full derivation of

`mu(zeta(2)) <= 62636575/13537936 < 4.62675`.

This supersedes the earlier conditional manuscript. The four missing arithmetic intervals, uniform analytic estimates, and bounded-gap independence now have arguments in the text. No proof assistant is used or included.

## Read the proof

- Sections 1–2 explain conservation, independent row/prime choices, the 2×2 toy example, and the relation to the literature.
- Section 3 specifies the actual four-block route and native readout. Appendix A derives that readout uniformly from the generators; Appendix C records every boundary normalization.
- Section 4 and Appendix D establish the full six-interval extra divisor. The key finite-field quotient is a polynomial by root multiplicities. Its degree is below p−1, forcing the leading prime residue to vanish. Appendix B supplies the baseline arithmetic.
- Section 5 and Appendix E establish the arithmetic exponent using a rational carry-profile enclosure.
- Section 6 identifies the exact error by a Barnes integral, proves decay by Gamma-integral rotation, improves its rate by an elementary invariant-cone argument, and proves independence over three consecutive depths by a nonzero determinant. It then deduces the irrationality measure.
- Appendix F gives short RamanujanTools code. The complete portable Python package is in `code/`.

The precise CMF contribution is a useful whole-block representation derived from conservation. In this proof the four-block order is fixed, and the exact readout shift is chosen separately at each prime. The toy example also demonstrates literal row-dependent and prime-dependent path orders. These two freedoms are distinguished explicitly.

## Exact certificates and diagnostics

All ten packaged checks passed; see `code/verification.json`. The 390-cell floor certificate exhausts a finite rational arrangement after a proof that the relevant signatures are constant on its cells. The spectral and logarithmic certificates use exact rational arithmetic and explicit series remainder bounds. These are finite certificates for reductions stated in the proof.

The package also contains finite-depth diagnostics: native RT products, finite formulas, and local kernel congruences. Such diagnostics are not substituted for universal arguments. Additional independent review notes and a Barnes-integral numerical diagnostic are saved under `evidence/`.

Both the arithmetic and analytic derivations received independent mathematical review during this work. The document compiled successfully, has no overfull/underfull box or unresolved-reference warnings, and all 22 rendered pages were inspected.

## Required project handoff

1. **Files inspected.** Reused the supplied manuscript and matrix bundle, the prior exact native results under `results/zeta2_orders_10911/`, and the earlier finite-readout and baseline derivations under `work/zeta2_proof_strategy/`. Inspected the new floor-cell, local-kernel, contour, spectral, and observability arguments and their code. The previous recursive archive audit is preserved at `results/zeta2_orders_10911/archive_audit.json`; it was reused rather than rerun.
2. **Files created.** The article, PDF, this README, portable Python package, verification records, and evidence under `results/zeta2_complete_proof/`; new mathematical derivations, experiments, and document build files under `work/zeta2_completion/`; and the ZIP bundle under `results/`. No archive files were edited.
3. **Experiments recovered.** The original direction `(10,9,11,-11;2,1,3)` and start `(1,1,1,0;1,1,1)`, both four-block routes t=3,4, and the exact native readout. New work establishes the whole-kernel reduction behind all six prime intervals and the analytic connection to ζ(2).
4. **Top delta values.** No new delta search was run. Previously measured reduced-denominator scores are δ3000=0.278673337629, δ4000=0.279047437501, δ6000=0.278946586656, with last-three-depth slope 0.279152068816. The larger early δ20=0.2958276167 is not a stable asymptotic score. The numerical candidate record remains unchanged.
5. **Rejected or unstable certificates.** A componentwise estimate at the single cut m=0 fails to certify the required extra factor at N=160, p=347,349. It is not used in the proof. Earlier failed normalizations and unshifted prime-interval endpoints remain rejected as documented in the previous report. The completed argument retains the entire rational kernel, including contributions missed by a termwise estimate in the e=1 chambers.
6. **Numerical uncertainties.** The displayed upper bound uses rational enclosures, not floating-point assumptions. Finite-depth delta stabilization and the optimality of the arithmetic normalization remain numerical questions; the proof makes no claim of an optimal irrationality measure. The code supports the explicit mathematical reductions rather than constituting formal verification of the entire article.
7. **Exact next numerical search region.** To seek a stronger bound on this same trajectory, keep both initial rows and columns r=0,1,2, with t=3,4. At N=160,320,640,1280, inspect residual prime valuations for p²>50N and 1<p/N<13 outside the six established open intervals. Compare complete negative-upper blocks and long cuts at integer m between 0 and 11N. Any further divisor must receive a new uniform argument before being used in an irrationality-measure claim.

The user's explicit proof request governs this continuation; the ordinary numerical-discovery mission remains unchanged for unrelated searches.
