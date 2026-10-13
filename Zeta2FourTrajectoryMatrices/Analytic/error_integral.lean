/-
# Blueprint: `error_integral` (equation (A1), §6.1 of the article)

Statement (`Zeta2Blueprint.error_integral`, restated verbatim below): for `2N ≤ η ≤ 9N`,
`C_N 𝖤_{N,r} = -2 𝓘_η(s^r F_N L_m)`, `m = 11N`.

Proof outline (article §6.1).
* Partial fractions (`partial_fraction`):
  `s^r F_N(s) L_m(s) = S_r(s) + ∑_{j=0}^m j^r c_j / (s - j)` away from `0, …, m`.
  The line `Re s = -η - 1/2` avoids these poles (`barnesLine_re`).
* Linearity of `𝓘_η` on a polynomial plus finitely many resolvents
  (`barnesI_poly_add_resolvents`).
* `barnes_identities` (proved in `barnes_identities.lean` from its own lemmas):
  `𝓘_η(S_r) = J_η(S_r)`, `𝓘_η(1/(s-j)) = H^{(2)}_{j+η} - ζ(2)`.
* The exact readout `readout_formula` (proved in `blueprint_first_three.lean`):
  `C_N 𝖯_{N,r} = 2(∑ j^r c_j H^{(2)}_{j+η} + J_η(S_r))`, `C_N 𝖰_{N,r} = 2 ∑ j^r c_j`.
  Hence `C_N(ζ(2)𝖰 - 𝖯) = -2 (J_η(S_r) + ∑ j^r c_j (H^{(2)}_{j+η} - ζ(2))) = -2 𝓘_η(s^r F L)`.
-/
import Zeta2FourTrajectoryMatrices.Analytic.barnes_identities

open Polynomial Filter Topology Real Finset MeasureTheory Zeta2Blueprint

noncomputable section

namespace Zeta2ErrorIntegral

/-- **Lemma 1 (the Barnes line avoids the poles).** `Re(-η - 1/2 + iy) = -η - 1/2 < 0`.

* Estimated length: 3 lines.
* Formalizable directly from the pdf: yes. -/
theorem barnesLine_re (η : ℕ) (y : ℝ) : (barnesLine η y).re < 0 := by
  have h0 : (0 : ℝ) ≤ η := Nat.cast_nonneg η
  simp [barnesLine]
  linarith

theorem L_closedC (m : ℕ) : ∀ s : ℂ, (∀ j : ℕ, j ≤ m → s ≠ j) →
    ∑ j ∈ range (m + 1), (-1 : ℂ) ^ j * (m.choose j : ℂ) / (s - j) =
      (-1) ^ m * (m.factorial : ℂ) / ∏ j ∈ range (m + 1), (s - j) := by
  induction m with
  | zero =>
    intro s _
    rw [zero_add, sum_range_one, prod_range_one, pow_zero, Nat.choose_self,
      Nat.factorial_zero]
  | succ m ih =>
    intro s hs
    have hsm : ∀ j : ℕ, j ≤ m → s ≠ j := fun j hj => hs j (by omega)
    have hs1 : ∀ j : ℕ, j ≤ m → s - 1 ≠ j := fun j hj h => hs (j + 1) (by omega)
      (by rw [Nat.cast_add, Nat.cast_one, ← h, sub_add_cancel])
    have hrec : ∑ j ∈ range (m + 1 + 1), (-1 : ℂ) ^ j * ((m + 1).choose j : ℂ) / (s - j) =
        ∑ j ∈ range (m + 1), (-1 : ℂ) ^ j * (m.choose j : ℂ) / (s - j) -
          ∑ j ∈ range (m + 1), (-1 : ℂ) ^ j * (m.choose j : ℂ) / (s - 1 - j) := by
      have e1 : ∀ j ∈ range (m + 1), (-1 : ℂ) ^ (j + 1) * ((m + 1).choose (j + 1) : ℂ) /
          (s - ((j + 1 : ℕ) : ℂ)) = (-1 : ℂ) ^ (j + 1) * (m.choose (j + 1) : ℂ) /
            (s - ((j + 1 : ℕ) : ℂ)) - (-1 : ℂ) ^ j * (m.choose j : ℂ) / (s - 1 - j) :=
        fun j _ => by
          rw [Nat.choose_succ_succ', Nat.cast_add, Nat.cast_add, Nat.cast_one]
          ring
      have e2 := sum_range_succ' (fun j => (-1 : ℂ) ^ j * (m.choose j : ℂ) / (s - j)) (m + 1)
      rw [sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, mul_zero, zero_div,
        add_zero] at e2
      rw [sum_range_succ', sum_congr rfl e1, sum_sub_distrib, e2, Nat.choose_zero_right,
        Nat.choose_zero_right]
      ring
    rw [hrec, ih s hsm, ih (s - 1) hs1]
    have hA : ∏ j ∈ range (m + 1), (s - j) ≠ 0 :=
      prod_ne_zero_iff.2 fun j hj => sub_ne_zero.2 (hsm j (by have := mem_range.1 hj; omega))
    have hB : ∏ j ∈ range (m + 1), (s - 1 - j) ≠ 0 :=
      prod_ne_zero_iff.2 fun j hj => sub_ne_zero.2 (hs1 j (by have := mem_range.1 hj; omega))
    have e1 : (∏ j ∈ range (m + 1), (s - j)) * (s - ((m + 1 : ℕ) : ℂ)) =
        ∏ j ∈ range (m + 1 + 1), (s - j) := (prod_range_succ _ _).symm
    have e2 : s * ∏ j ∈ range (m + 1), (s - 1 - j) = ∏ j ∈ range (m + 1 + 1), (s - j) := by
      rw [prod_range_succ' (fun j : ℕ => s - (j : ℂ)) (m + 1), Nat.cast_zero, sub_zero, mul_comm]
      exact congrArg (· * s) (prod_congr rfl fun j _ => by
        rw [Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub, sub_right_comm])
    have hP : ∏ j ∈ range (m + 1 + 1), (s - j) ≠ 0 := by
      rw [← e1]; exact mul_ne_zero hA (sub_ne_zero.2 (hs (m + 1) le_rfl))
    rw [div_sub_div _ _ hA hB, div_eq_div_iff (mul_ne_zero hA hB) hP, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_succ, pow_succ]
    rw [Nat.cast_add, Nat.cast_one] at e1
    linear_combination (-((-1 : ℂ) ^ m * (m.factorial : ℂ) *
      ∏ j ∈ range (m + 1), (s - 1 - j))) * e1 +
        ((-1 : ℂ) ^ m * (m.factorial : ℂ) * ∏ j ∈ range (m + 1), (s - j)) * e2

/-- **Lemma 2 (exact partial-fraction identity).** For `Re s < 0` (so `s ∉ {0, …, m}`),
`s^r F_N(s) L_m(s) = S_r(s) + ∑_{j=0}^{m} j^r c_j / (s - j)`, `m = 11N`.
It combines `L_m(s) = ∑_j (-1)^j binom(m,j) / (s - j)` (with the sign `(-1)^m` retained) and the
definition of the divided differences in `S_r`.

* Estimated length: 50 lines (the `ℚ`-version is `Zeta2NextTwo.Sm_eval'` together with
  `Zeta2NextTwo.L_closed`; over `ℂ` repeat that argument, or prove the polynomial identity obtained
  by multiplying with `∏_j (X - j)` in `ℚ[X]` and evaluate it at `s`).
* Formalizable directly from the pdf: yes (Appendix A §2 and identity (P) of Appendix B). -/
theorem partial_fraction (N r : ℕ) (s : ℂ) (hs : s.re < 0) :
    s ^ r * aeval s (Fpoly N) * Lker (11 * N) s =
      aeval s (Spoly N r) +
        ∑ j ∈ range (11 * N + 1), ((j : ℂ) ^ r * (cj N j : ℂ)) / (s - j) := by
  have hsj : ∀ j : ℕ, s - j ≠ 0 := fun j h => by
    have h1 := congrArg Complex.re h
    rw [Complex.sub_re, Complex.natCast_re, Complex.zero_re] at h1
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have hp : aeval s (X ^ r * Fpoly N) = s ^ r * aeval s (Fpoly N) := by
    rw [map_mul, map_pow, aeval_X]
  have hD : ∀ j : ℕ, aeval s (Zeta2FirstThree.DD (X ^ r * Fpoly N) (j : ℚ)) =
      (s ^ r * aeval s (Fpoly N) - (j : ℂ) ^ r * (((Fpoly N).eval (j : ℚ) : ℚ) : ℂ)) /
        (s - j) := by
    intro j
    have h1 := congrArg (aeval s) (Zeta2FirstThree.DD_spec (X ^ r * Fpoly N) (j : ℚ))
    rw [map_mul, map_sub, map_sub, aeval_X, aeval_C, aeval_C, hp, eval_mul, eval_pow, eval_X,
      eq_ratCast, eq_ratCast, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast] at h1
    rw [eq_div_iff (hsj j), mul_comm, h1]
  have hS : aeval s (Spoly N r) = ∑ j ∈ range (11 * N + 1),
      (((-1) ^ j * ((11 * N).choose j : ℚ) : ℚ) : ℂ) *
        aeval s (Zeta2FirstThree.DD (X ^ r * Fpoly N) (j : ℚ)) := by
    rw [Spoly, map_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [map_smul, Rat.smul_def]
    rfl
  rw [Lker, ← L_closedC (11 * N) s (fun j _ h => hsj j (sub_eq_zero.2 h)), mul_sum, hS,
    ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  rw [hD, cj]
  push_cast
  ring

open Zeta2BarnesIdentities in
theorem poly_integrable_neg (η : ℕ) (P : ℚ[X]) :
    Integrable (fun y : ℝ =>
      ((π : ℂ) / Complex.sin ((π : ℂ) * lineAt (-(η : ℝ) - 1 / 2) y)) ^ 2 *
        aeval (lineAt (-(η : ℝ) - 1 / 2) y) P) := by
  have hk : (((-(η : ℤ) - 1 : ℤ)) : ℝ) + 1 / 2 = -(η : ℝ) - 1 / 2 := by
    rw [Int.cast_sub, Int.cast_neg, Int.cast_natCast, Int.cast_one]
    linarith
  have h := integrable_half_poly (-(η : ℤ) - 1) P
  rwa [hk] at h

open Zeta2BarnesIdentities in
theorem resolvent_integrable (η j : ℕ) :
    Integrable (fun y : ℝ =>
      ((π : ℂ) / Complex.sin ((π : ℂ) * lineAt (-(η : ℝ) - 1 / 2) y)) ^ 2 *
        (1 / (lineAt (-(η : ℝ) - 1 / 2) y - j))) := by
  have h0 : (0 : ℝ) ≤ η := Nat.cast_nonneg η
  have h1 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hre : ∀ y : ℝ, (lineAt (-(η : ℝ) - 1 / 2) y - j).re = -(η : ℝ) - 1 / 2 - j := fun y => by
    rw [Complex.sub_re, lineAt_re, Complex.natCast_re]
  have hne : ∀ y : ℝ, lineAt (-(η : ℝ) - 1 / 2) y - j ≠ 0 := fun y h => by
    have h2 := congrArg Complex.re h
    rw [hre, Complex.zero_re] at h2
    linarith
  have hK : Integrable (fun y : ℝ =>
      ((π : ℂ) / Complex.sin ((π : ℂ) * lineAt (-(η : ℝ) - 1 / 2) y)) ^ 2) :=
    (poly_integrable_neg η 1).congr (Filter.Eventually.of_forall fun y => by
      beta_reduce
      rw [map_one, mul_one])
  refine hK.mul_bdd (c := 2)
    ((continuous_const.div ((continuous_lineAt _).sub continuous_const) hne).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun y => ?_)
  have h2 := Complex.abs_re_le_norm (lineAt (-(η : ℝ) - 1 / 2) y - j)
  rw [hre, abs_of_neg (by linarith)] at h2
  rw [norm_div, norm_one, div_le_iff₀ (norm_pos_iff.2 (hne y))]
  linarith

/-- **Lemma 3 (linearity of `𝓘_η`).** On the line `Re s = -η - 1/2` the kernel decays like
`e^{-2π|y|}`, a polynomial grows polynomially and each resolvent `1/(s-j)` is bounded by `2`, so
all integrands are integrable and `𝓘_η` is additive on them.

* Estimated length: 60 lines (bound `|π / sin(π(x+iy))|² ≤ C e^{-2π|y|}` for `x ∈ ½ + ℤ`,
  `Integrable.mul_of_…`, `integral_add`, `integral_finset_sum`, `integral_mul_left`).
* Formalizable directly from the pdf: partially (the pdf only states that the integral converges
  "because of the exponential decay of the kernel"). -/
theorem barnesI_poly_add_resolvents (η : ℕ) (P : ℚ[X]) (m : ℕ) (a : ℕ → ℂ) :
    barnesI η (fun s => aeval s P + ∑ j ∈ range (m + 1), a j / (s - j)) =
      barnesI η (fun s => aeval s P) +
        ∑ j ∈ range (m + 1), a j * barnesI η (fun s => 1 / (s - j)) := by
  simp only [Zeta2BarnesIdentities.barnesI_eq, Zeta2BarnesIdentities.barnesAt]
  have hR : ∀ j ∈ range (m + 1), Integrable (fun y : ℝ => a j *
      (((π : ℂ) / Complex.sin ((π : ℂ) * Zeta2BarnesIdentities.lineAt (-(η : ℝ) - 1 / 2) y)) ^ 2 *
        (1 / (Zeta2BarnesIdentities.lineAt (-(η : ℝ) - 1 / 2) y - j)))) :=
    fun j _ => (resolvent_integrable η j).const_mul (a j)
  have e : ∀ y : ℝ,
      ((π : ℂ) / Complex.sin ((π : ℂ) * Zeta2BarnesIdentities.lineAt (-(η : ℝ) - 1 / 2) y)) ^ 2 *
        (aeval (Zeta2BarnesIdentities.lineAt (-(η : ℝ) - 1 / 2) y) P +
          ∑ j ∈ range (m + 1), a j / (Zeta2BarnesIdentities.lineAt (-(η : ℝ) - 1 / 2) y - j)) =
      ((π : ℂ) / Complex.sin ((π : ℂ) * Zeta2BarnesIdentities.lineAt (-(η : ℝ) - 1 / 2) y)) ^ 2 *
          aeval (Zeta2BarnesIdentities.lineAt (-(η : ℝ) - 1 / 2) y) P +
        ∑ j ∈ range (m + 1), a j *
          (((π : ℂ) / Complex.sin ((π : ℂ) *
            Zeta2BarnesIdentities.lineAt (-(η : ℝ) - 1 / 2) y)) ^ 2 *
            (1 / (Zeta2BarnesIdentities.lineAt (-(η : ℝ) - 1 / 2) y - j))) := fun y => by
    rw [mul_add, mul_sum]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [div_eq_mul_one_div (a j), mul_left_comm]
  rw [integral_congr_ae (Filter.Eventually.of_forall e),
    integral_add (poly_integrable_neg η P) (integrable_finsetSum _ hR),
    integral_finsetSum _ hR, mul_add, mul_sum]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, mul_left_comm]

/-- **(A1)** — restatement of `Zeta2Blueprint.error_integral`, proved from Lemmas 1–3,
`Zeta2BarnesIdentities.barnes_identities` and `Zeta2FirstThree.readout_formula`. -/
theorem error_integral (N : ℕ) (r : Fin 3) (η : ℕ) (hη₁ : 2 * N ≤ η) (hη₂ : η ≤ 9 * N) :
    (((CN N : ℝ) * Err N r : ℝ) : ℂ) =
      -2 * barnesI η (fun s => s ^ (r : ℕ) * aeval s (Fpoly N) * Lker (11 * N) s) := by
  set a : ℕ → ℂ := fun j => (j : ℂ) ^ (r : ℕ) * (cj N j : ℂ) with ha
  -- rewrite the integrand on the line by partial fractions
  have hline : barnesI η (fun s => s ^ (r : ℕ) * aeval s (Fpoly N) * Lker (11 * N) s) =
      barnesI η (fun s => aeval s (Spoly N r) + ∑ j ∈ range (11 * N + 1), a j / (s - j)) := by
    unfold barnesI
    congr 2
    funext y
    beta_reduce
    rw [partial_fraction N r _ (barnesLine_re η y)]
  have hI : barnesI η (fun s => s ^ (r : ℕ) * aeval s (Fpoly N) * Lker (11 * N) s) =
      (Jfun η (Spoly N r) : ℂ) +
        ∑ j ∈ range (11 * N + 1), a j * ((harm2 (j + η) : ℂ) - (zeta2 : ℂ)) := by
    rw [hline, barnesI_poly_add_resolvents, (Zeta2BarnesIdentities.barnes_identities η).1]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [(Zeta2BarnesIdentities.barnes_identities η).2 j]
  have hR := Zeta2FirstThree.readout_formula N r η hη₁ hη₂
  have h0 : (CN N : ℚ) * readout N 0 r = 2 * (∑ j ∈ range (11 * N + 1), (j : ℚ) ^ (r : ℕ) * cj N j *
      harm2 (j + η) + Jfun η (Spoly N r)) := congrFun hR 0
  have h1 : (CN N : ℚ) * readout N 1 r = 2 * ∑ j ∈ range (11 * N + 1), (j : ℚ) ^ (r : ℕ) * cj N j :=
    congrFun hR 1
  have h0' := congrArg (fun q : ℚ => (q : ℂ)) h0
  have h1' := congrArg (fun q : ℚ => (q : ℂ)) h1
  push_cast at h0' h1'
  have hsplit : ∑ j ∈ range (11 * N + 1), a j * ((harm2 (j + η) : ℂ) - (zeta2 : ℂ)) =
      ∑ j ∈ range (11 * N + 1), (j : ℂ) ^ (r : ℕ) * (cj N j : ℂ) * (harm2 (j + η) : ℂ) -
        (zeta2 : ℂ) * ∑ j ∈ range (11 * N + 1), (j : ℂ) ^ (r : ℕ) * (cj N j : ℂ) := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [ha]
    ring
  rw [hI, hsplit, Err]
  push_cast
  linear_combination (zeta2 : ℂ) * h1' - h0'

end Zeta2ErrorIntegral
