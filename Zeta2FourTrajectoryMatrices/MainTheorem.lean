import Zeta2FourTrajectoryMatrices.Blueprint.blueprint

/-!
# The main result: `μ(ζ(2)) ≤ 62636575/13537936 < 4.62675`

This file is the entry point of the repository. It restates the main theorem of the article
`results/zeta2_complete_proof/zeta2_complete_proof.tex` with all notions spelled out, checks it
against `Zeta2Blueprint.main_theorem`, and prints the axioms the proof depends on.

Run it with `lake env lean Zeta2FourTrajectoryMatrices/MainTheorem.lean` (or `lake build`).
-/

open Zeta2Blueprint

/-! ### The notions used in the statement -/

/-- `ζ(2)` as a real number: the real part of Mathlib's `riemannZeta 2`. -/
example : zeta2 = (riemannZeta 2).re := rfl

/-- `μ(α) ≤ μ`: for every `ε > 0` only finitely many rationals `q` (in lowest terms, with
denominator `q.den`) satisfy `|α - q| < q.den ^ (-(μ + ε))`. -/
example (α μ : ℝ) :
    IrrMeasureLE α μ ↔ ∀ ε > 0, {q : ℚ | |α - q| < (q.den : ℝ) ^ (-(μ + ε))}.Finite :=
  Iff.rfl

/-- The irrationality measure `μ(α) = inf {μ | μ(α) ≤ μ}` (valued in `EReal`). -/
example (α : ℝ) :
    irrationalityMeasure α = ⨅ (μ : ℝ) (_ : IrrMeasureLE α μ), (μ : EReal) :=
  rfl

/-! ### The main theorem -/

/-- **Main theorem.** The irrationality measure of `ζ(2)` is at most
`62636575/13537936 = 1 + σ/τ`, with `σ = 49.098639` and `τ = 13.537936`, and this number is
smaller than `4.62675`. -/
theorem zeta2_irrationality_measure :
    irrationalityMeasure zeta2 ≤ ((62636575 / 13537936 : ℝ) : EReal) ∧
      (62636575 / 13537936 : ℝ) < 4.62675 :=
  main_theorem

/-- The same statement in the "finitely many good approximations" form. -/
theorem zeta2_irrMeasure_bound : IrrMeasureLE zeta2 (62636575 / 13537936) :=
  zeta2_irrMeasureLE

#check @zeta2_irrationality_measure
#check @Zeta2Blueprint.main_theorem

/-! ### Axioms

The proof uses Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and one
additional axiom, `Zeta2ArithRate.prime_number_theorem` (`θ(x)/x → 1`), which is not yet in
Mathlib. No `sorry` is used. -/

#print axioms zeta2_irrationality_measure
#print Zeta2ArithRate.prime_number_theorem
