/-
# Blueprint: `error_coarse_bound` (equations (A2)–(A4), §6.2 of the article)

Statement (`Zeta2Blueprint.error_coarse_bound`, restated verbatim below):
`|C_N 𝖤_{N,r}| ≤ e^{-18N}` for all large `N`.

Proof outline (article §6.2).
* Take `η = 6N` in (A1) (`Zeta2ErrorIntegral.error_integral`, proved in `error_integral.lean`) and
  move the line from `Re s = -6N - 1/2` to `Re s = -6N`; the pole of the kernel at `s = -6N` is
  cancelled by the triple zero of `F_N` there (`barnes_shift_6N`).
* Put `s = -t`. The reflection formula and `L_m(-t) = -B(t, m+1)` turn the integrand into the
  Gamma form (A2) (`reflection_form`).
* Bound the six Gamma factors by rotating the Euler integral by `±π/4`
  (`gamma_rotation_bound`), the Beta factor by its value at `Re t` (`beta_bound`), and the sine by
  `e^{π|y|}`. Integrating in `y` gives (A3) (`A3_bound`).
* Stirling's formula gives the exponential rate `h` of the majorant (A4) (`coarse_rate`), and
  `h < -18` (`hconst_lt`).

Python certificate: `results/zeta2_complete_proof/code/analytic/certify_analytic_rates.py`
(the assertion `hb[1] < -18`) encloses `h` with exact rational logarithm bounds.
-/
import Zeta2FourTrajectoryMatrices.Analytic.error_integral
import Zeta2FourTrajectoryMatrices.Analytic.error_coarse_bound_gamma
import Zeta2FourTrajectoryMatrices.Analytic.error_coarse_bound_shift

open Polynomial Filter Topology Real Finset MeasureTheory Zeta2Blueprint

noncomputable section

namespace Zeta2ErrorCoarseBound

/-- The integrand `s^r F_N(s) L_{11N}(s)` of (A1). -/
def Gint (N r : ℕ) (s : ℂ) : ℂ := s ^ r * aeval s (Fpoly N) * Lker (11 * N) s

/-- The majorant of (A3) without the factor `K_r N^r`:
`2^{12N} B(6N, 11N+1) ∏_{k=3}^{5} Γ(kN) Γ(kN+1) / Γ(8N+1)³`. -/
def coarseMaj (N : ℕ) : ℝ :=
  2 ^ (12 * N) * (Gamma (6 * N) * Gamma (11 * N + 1) / Gamma (17 * N + 1)) *
    (∏ k ∈ ({3, 4, 5} : Finset ℕ), Gamma (k * N) * Gamma (k * N + 1)) / Gamma (8 * N + 1) ^ 3

/-- The exponent `h` of (A4). -/
def hconst : ℝ :=
  12 * log 2 + 6 * log 6 + 11 * log 11 - 17 * log 17 +
    2 * (3 * log 3 + 4 * log 4 + 5 * log 5) - 24 * log 8

/-- **Lemma 1 (moving the line to `Re s = -6N`).** For `η = 6N` the line `Re s = -6N - 1/2` may be
moved to `Re s = -6N`: the only integer met is `s = -6N`, a zero of `F_N` of multiplicity three
(from the factors `binom(s+uN, 8N)`, `u = 9, 10, 11`), which cancels the double pole of
`(π / sin πs)²`; the horizontal edges vanish by exponential decay.

* Estimated length: 150 lines (rectangle Cauchy theorem on `[-6N-1/2, -6N] × [-T, T]` for the
  holomorphic extension of `K · Gint` across `s = -6N`; decay of the horizontal edges as
  `T → ∞`; the integrand on the new line is changed only at `y = 0`).
* Formalizable directly from the pdf: partially (the pdf states the cancellation; the
  removable-singularity and contour estimates must be written out). -/
theorem barnes_shift_6N (N r : ℕ) (hN : 1 ≤ N) :
    barnesI (6 * N) (Gint N r) =
      Zeta2BarnesIdentities.barnesAt (-((6 * N : ℕ) : ℝ)) (Gint N r) :=
  Zeta2ECBShift.barnes_shift_core N r hN

theorem ne_neg_nat_of_im (z : ℂ) (hz : z.im ≠ 0) : ∀ k : ℕ, z ≠ -k := by
  intro k hk
  apply hz
  rw [hk, Complex.neg_im, Complex.natCast_im, neg_zero]

theorem gamma_add_nat_eq (z : ℂ) (hz : z.im ≠ 0) (n : ℕ) :
    Complex.Gamma (z + n) = Complex.Gamma z * (ascPochhammer ℂ n).eval z := by
  rw [← Complex.Gamma_add_nat_div_Gamma_eq z (ne_neg_nat_of_im z hz),
    mul_div_cancel₀ _ (Complex.Gamma_ne_zero (ne_neg_nat_of_im z hz))]

theorem sin_pi_mul_ne_zero (t : ℂ) (ht : t.im ≠ 0) : Complex.sin (π * t) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.1 h
  have him := congrArg Complex.im hk
  rw [Complex.im_ofReal_mul, Complex.mul_im, Complex.intCast_im, Complex.ofReal_im, zero_mul,
    mul_zero, add_zero] at him
  exact ht ((mul_eq_zero.1 him).resolve_left pi_ne_zero)

theorem aeval_binomPoly (s : ℂ) (a b : ℕ) :
    aeval s (binomPoly ℚ (a : ℚ) b) =
      ((b.factorial : ℂ))⁻¹ * (ascPochhammer ℂ b).eval (s + a - b + 1) := by
  rw [binomPoly, map_mul, aeval_C, aeval_comp, map_add, aeval_X, aeval_C, aeval_def,
    eval₂_eq_eval_map, descPochhammer_map, descPochhammer_eval_eq_ascPochhammer, map_inv₀,
    map_natCast, map_natCast]

theorem Lker_neg (m : ℕ) (t : ℂ) (ht : t.im ≠ 0) :
    Lker m (-t) = -(Complex.Gamma t * Complex.Gamma (m + 1) / Complex.Gamma (t + m + 1)) := by
  have hne := Complex.Gamma_ne_zero (ne_neg_nat_of_im t ht)
  have h1 : (descPochhammer ℂ (m + 1)).eval (-t) =
      (-1) ^ (m + 1) * (ascPochhammer ℂ (m + 1)).eval t := by
    have h := ascPochhammer_eval_neg_eq_descPochhammer ℂ (-t) (m + 1)
    rw [neg_neg] at h
    rw [h, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  have h2 : Complex.Gamma (t + m + 1) = Complex.Gamma t * (ascPochhammer ℂ (m + 1)).eval t := by
    rw [add_assoc, ← Nat.cast_add_one, gamma_add_nat_eq t ht]
  have hpow : ((-1 : ℂ)) ^ m ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  rw [Lker, ← descPochhammer_eval_eq_prod_range, h1, h2, Complex.Gamma_nat_eq_factorial,
    mul_div_mul_left _ _ hne, pow_succ, mul_neg_one, neg_mul, div_neg,
    mul_div_mul_left _ _ hpow]

theorem aeval_binom_neg (t : ℂ) (ht : t.im ≠ 0) (c b : ℕ) :
    aeval (-t) (binomPoly ℚ ((c + b : ℕ) : ℚ) b) =
      Complex.Gamma (t - c) * Complex.Gamma (-t + (c + b : ℕ) + 1) *
        Complex.sin (π * (t - c)) / π / b.factorial := by
  have hw : -t + ((c + b : ℕ) : ℂ) - b + 1 = 1 - (t - c) := by push_cast; ring
  have harg : 1 - (t - c) + b = -t + ((c + b : ℕ) : ℂ) + 1 := by push_cast; ring
  have hz : (t - c).im ≠ 0 := by rwa [Complex.sub_im, Complex.natCast_im, sub_zero]
  have hwim : (1 - (t - c)).im ≠ 0 := by rwa [Complex.sub_im, Complex.one_im, zero_sub, neg_ne_zero]
  have hS := sin_pi_mul_ne_zero (t - c) hz
  have key : Complex.Gamma (1 - (t - c)) * Complex.Gamma (t - c) * Complex.sin (π * (t - c)) =
      π := by
    rw [mul_comm (Complex.Gamma _), Complex.Gamma_mul_Gamma_one_sub, div_mul_cancel₀ _ hS]
  rw [aeval_binomPoly, hw, ← harg, gamma_add_nat_eq _ hwim b]
  calc ((b.factorial : ℂ))⁻¹ * (ascPochhammer ℂ b).eval (1 - (t - c))
      = (ascPochhammer ℂ b).eval (1 - (t - c)) *
          (Complex.Gamma (1 - (t - c)) * Complex.Gamma (t - c) * Complex.sin (π * (t - c))) /
            π / b.factorial := by
        rw [key, mul_div_cancel_right₀ _ (Complex.ofReal_ne_zero.2 pi_ne_zero), div_eq_inv_mul]
    _ = _ := by ring

theorem aeval_binom_factor (t : ℂ) (ht : t.im ≠ 0) (v N : ℕ) :
    aeval (-t) (binomPoly ℚ (((v + 8) * N : ℕ) : ℚ) (8 * N)) =
      Complex.Gamma (t - v * N) * Complex.Gamma ((v + 8) * N + 1 - t) *
        Complex.sin (π * (t - v * N)) / π / Complex.Gamma (8 * N + 1) := by
  have e1 : -t + ((v * N + 8 * N : ℕ) : ℂ) + 1 = (v + 8) * N + 1 - t := by push_cast; ring
  have e2 : ((v * N : ℕ) : ℂ) = v * N := Nat.cast_mul v N
  have e3 : ((8 * N : ℕ) : ℂ) + 1 = 8 * N + 1 := by rw [Nat.cast_mul, Nat.cast_ofNat]
  rw [show (v + 8) * N = v * N + 8 * N from add_mul v 8 N, aeval_binom_neg t ht, e1, e2,
    ← Complex.Gamma_nat_eq_factorial, e3]

theorem sin_sub_nat_mul (t : ℂ) (v N : ℕ) :
    Complex.sin (π * (t - v * N)) = (-1) ^ (v * N) * Complex.sin (π * t) := by
  rw [mul_sub, mul_comm (π : ℂ) ((v : ℂ) * N), ← Nat.cast_mul]
  exact Complex.sin_antiperiodic.sub_nat_mul_eq (v * N)

theorem sin_cube (t : ℂ) (N : ℕ) :
    Complex.sin (π * (t - (2 : ℕ) * N)) * Complex.sin (π * (t - (1 : ℕ) * N)) *
      Complex.sin (π * (t - (3 : ℕ) * N)) = Complex.sin (π * t) ^ 3 := by
  have hsign : ((-1 : ℂ)) ^ (2 * N) * (-1) ^ (1 * N) * (-1) ^ (3 * N) = 1 := by
    rw [← pow_add, ← pow_add, show 2 * N + 1 * N + 3 * N = 2 * (3 * N) by ring, pow_mul,
      neg_one_sq, one_pow]
  rw [sin_sub_nat_mul, sin_sub_nat_mul, sin_sub_nat_mul]
  calc ((-1 : ℂ)) ^ (2 * N) * Complex.sin (π * t) * ((-1) ^ (1 * N) * Complex.sin (π * t)) *
        ((-1) ^ (3 * N) * Complex.sin (π * t))
      = ((-1 : ℂ) ^ (2 * N) * (-1) ^ (1 * N) * (-1) ^ (3 * N)) * Complex.sin (π * t) ^ 3 := by
        ring
    _ = Complex.sin (π * t) ^ 3 := by rw [hsign, one_mul]

/-- **Lemma 2 (the Gamma form (A2), pointwise).** For `Im t ≠ 0`, with `m = 11N`,
`K(-t) (-t)^r F_N(-t) L_m(-t) = (-t)^r · (-B(t, m+1)) · (sin πt / π) ·
  ∏_{v=1}^{3} Γ(t - vN) Γ((v+8)N + 1 - t) / Γ(8N+1)³`.
Ingredients: `binom(uN - t, 8N) = Γ(uN-t+1) / (Γ(8N+1) Γ((u-8)N - t + 1))`, the reflection formula
`1/Γ(vN+1-t) = Γ(t-vN) sin(π(t-vN)) / π`, the parity `(-1)^{(1+2+3)N} = 1`, and
`L_m(-t) = -Γ(t) m! / Γ(t+m+1)`.

* Estimated length: 120 lines (`Complex.Gamma_mul_Gamma_one_sub`, `Complex.Gamma_add_nat` /
  `descPochhammer` evaluation, `Complex.sin_sub_int_mul_pi`).
* Formalizable directly from the pdf: yes (all identities are stated in §6.2). -/
theorem reflection_form (N r : ℕ) (t : ℂ) (ht : t.im ≠ 0) :
    ((π : ℂ) / Complex.sin ((π : ℂ) * (-t))) ^ 2 * Gint N r (-t) =
      (-t) ^ r *
        (-(Complex.Gamma t * Complex.Gamma (11 * N + 1) / Complex.Gamma (t + 11 * N + 1))) *
        (Complex.sin ((π : ℂ) * t) / π) *
        (∏ v ∈ ({1, 2, 3} : Finset ℕ),
          Complex.Gamma (t - v * N) * Complex.Gamma ((v + 8) * N + 1 - t)) /
        Complex.Gamma (8 * N + 1) ^ 3 := by
  have hS := sin_pi_mul_ne_zero t ht
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 pi_ne_zero
  rw [Gint, Lker_neg (11 * N) t ht, Nat.cast_mul, Nat.cast_ofNat, Fpoly, map_mul, map_mul,
    show 10 * N = (2 + 8) * N from rfl, show 9 * N = (1 + 8) * N from rfl,
    show 11 * N = (3 + 8) * N from rfl, aeval_binom_factor t ht, aeval_binom_factor t ht,
    aeval_binom_factor t ht, Finset.prod_insert (show (1 : ℕ) ∉ ({2, 3} : Finset ℕ) by decide),
    Finset.prod_insert (show (2 : ℕ) ∉ ({3} : Finset ℕ) by decide), Finset.prod_singleton,
    mul_neg (π : ℂ) t, Complex.sin_neg]
  have hkey : ((π : ℂ) / Complex.sin (π * t)) ^ 2 * Complex.sin (π * t) ^ 3 / (π : ℂ) ^ 3 =
      Complex.sin (π * t) / π := by
    rw [div_pow, div_mul_eq_mul_div, div_div,
      div_eq_div_iff (mul_ne_zero (pow_ne_zero 2 hS) (pow_ne_zero 3 hpi)) hpi]
    ring
  calc _ = ((π : ℂ) / -Complex.sin (π * t)) ^ 2 *
        (Complex.sin (π * (t - (2 : ℕ) * N)) * Complex.sin (π * (t - (1 : ℕ) * N)) *
          Complex.sin (π * (t - (3 : ℕ) * N))) / (π : ℂ) ^ 3 *
        ((-t) ^ r *
          (Complex.Gamma (t - (2 : ℕ) * N) * Complex.Gamma (((2 : ℕ) + 8) * N + 1 - t) *
            (Complex.Gamma (t - (1 : ℕ) * N) * Complex.Gamma (((1 : ℕ) + 8) * N + 1 - t)) *
            (Complex.Gamma (t - (3 : ℕ) * N) * Complex.Gamma (((3 : ℕ) + 8) * N + 1 - t))) /
          Complex.Gamma (8 * N + 1) ^ 3 *
          -(Complex.Gamma t * Complex.Gamma (11 * N + 1) / Complex.Gamma (t + 11 * N + 1))) := by
        ring
    _ = _ := by
        rw [sin_cube, div_neg, neg_sq, hkey]
        ring

/-- **Lemma 3 (rotated Euler integral).** For `a > 0`, real `y` and `0 < θ < π/2`,
`|Γ(a + iy)| ≤ Γ(a) (cos θ)^{-a} e^{-θ|y|}`.

* Estimated length: 150 lines (rotate `∫₀^∞ x^{z-1} e^{-x} dx` to the ray `arg x = sgn(y) θ` by
  Cauchy's theorem on a sector; outer arc decays exponentially, the inner arc vanishes since
  `a > 0`; then `|e^{-r e^{iφ}}| = e^{-r cos θ}` and
  `∫₀^∞ r^{a-1} e^{-r cos θ} dr = Γ(a) cos^{-a} θ`).
* Formalizable directly from the pdf: partially (the pdf gives the rotation argument in two
  sentences; Mathlib has `Complex.GammaIntegral` but no sector contour lemma). -/
theorem gamma_rotation_bound (a y θ : ℝ) (ha : 0 < a) (hθ₀ : 0 < θ) (hθ : θ < π / 2) :
    ‖Complex.Gamma (a + y * Complex.I)‖ ≤ Gamma a * (cos θ) ^ (-a) * exp (-θ * |y|) :=
  Zeta2ECBGamma.gamma_rotation_bound_core a y θ ha hθ₀ hθ

theorem re_ofReal_add_mul_I (a y : ℝ) : ((a : ℂ) + y * Complex.I).re = a := by
  rw [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero, add_zero]

theorem im_ofReal_add_mul_I (a y : ℝ) : ((a : ℂ) + y * Complex.I).im = y := by
  rw [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, Complex.I_im, mul_one, zero_add]

theorem beta_real_eq (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫ x in (0 : ℝ)..1, x ^ (a - 1) * (1 - x) ^ (b - 1) = Gamma a * Gamma b / Gamma (a + b) := by
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (a : ℂ)) (t := (b : ℂ))
    (by rw [Complex.ofReal_re]; exact ha) (by rw [Complex.ofReal_re]; exact hb)
  have hB : Complex.betaIntegral a b =
      ((∫ x in (0 : ℝ)..1, x ^ (a - 1) * (1 - x) ^ (b - 1) : ℝ) : ℂ) := by
    rw [Complex.betaIntegral, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le zero_le_one] at hx
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1, Complex.ofReal_cpow (sub_nonneg.2 hx.2),
      Complex.ofReal_sub, Complex.ofReal_sub, Complex.ofReal_sub, Complex.ofReal_one]
  rw [hB, ← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_inj] at h
  rw [eq_div_iff (Gamma_pos_of_pos (add_pos ha hb)).ne', mul_comm]
  exact h.symm

/-- **Lemma 4 (Beta bound).** For `a, b > 0`: `|B(a + iy, b)| ≤ B(a, b)`, directly from
`B(z, b) = ∫₀¹ x^{z-1} (1-x)^{b-1} dx` and `|x^{iy}| = 1`.

* Estimated length: 30 lines (`Complex.betaIntegral`, `Complex.Gamma_mul_Gamma_eq_betaIntegral`,
  `norm_integral_le_integral_norm`).
* Formalizable directly from the pdf: yes. -/
theorem beta_bound (a b y : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ‖Complex.Gamma (a + y * Complex.I) * Complex.Gamma b / Complex.Gamma (a + b + y * Complex.I)‖ ≤
      Gamma a * Gamma b / Gamma (a + b) := by
  have hs : 0 < ((a : ℂ) + y * Complex.I).re := by rw [re_ofReal_add_mul_I]; exact ha
  have hb' : 0 < (b : ℂ).re := by rw [Complex.ofReal_re]; exact hb
  have hsb : (a : ℂ) + y * Complex.I + b = a + b + y * Complex.I := add_right_comm _ _ _
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral hs hb'
  rw [hsb] at h
  have hne : Complex.Gamma ((a : ℂ) + b + y * Complex.I) ≠ 0 := by
    refine Complex.Gamma_ne_zero_of_re_pos ?_
    rw [← hsb, Complex.add_re, re_ofReal_add_mul_I, Complex.ofReal_re]
    exact add_pos ha hb
  rw [h, mul_div_cancel_left₀ _ hne, Complex.betaIntegral, ← beta_real_eq a b ha hb]
  refine (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans (le_of_eq ?_)
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun x hx => ?_))
  rw [Set.uIoc_of_le zero_le_one] at hx
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx.1, Complex.sub_re, re_ofReal_add_mul_I,
    Complex.one_re, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_sub,
    ← Complex.ofReal_cpow (sub_nonneg.2 hx.2),
    Complex.norm_of_nonneg (rpow_nonneg (sub_nonneg.2 hx.2) _)]

theorem norm_sin_le_exp (z : ℂ) : ‖Complex.sin z‖ ≤ exp |z.im| := by
  have h1 : ‖Complex.exp (-z * Complex.I)‖ ≤ exp |z.im| := by
    rw [Complex.norm_exp, Complex.mul_I_re, Complex.neg_im, neg_neg]
    exact exp_le_exp.2 (le_abs_self _)
  have h2 : ‖Complex.exp (z * Complex.I)‖ ≤ exp |z.im| := by
    rw [Complex.norm_exp, Complex.mul_I_re]
    exact exp_le_exp.2 (neg_le_abs _)
  calc ‖Complex.sin z‖
      = ‖Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)‖ / 2 := by
        rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_two]
    _ ≤ (exp |z.im| + exp |z.im|) / 2 :=
        div_le_div_of_nonneg_right ((norm_sub_le _ _).trans (add_le_add h1 h2)) zero_le_two
    _ = exp |z.im| := add_self_div_two _

theorem majorant_integrable (r : ℕ) :
    Integrable (fun y : ℝ => (1 + |y|) ^ r * exp (-(π / 2) * |y|)) := by
  have hint : Integrable (fun y : ℝ => ((r + 2).factorial * exp 1) * (1 + ‖y‖) ^ (-(2 : ℝ))) :=
    (integrable_one_add_norm
      (by rw [Module.finrank_self, Nat.cast_one]; exact one_lt_two)).const_mul _
  refine hint.mono'
    ((((continuous_const.add continuous_abs).pow r).mul
      (continuous_const.mul continuous_abs).rexp).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun y => ?_))
  have hu : 0 < 1 + |y| := add_pos_of_pos_of_nonneg one_pos (abs_nonneg y)
  have hpi : |y| ≤ π / 2 * |y| := le_mul_of_one_le_left (abs_nonneg y) one_le_pi_div_two
  have hf := pow_div_factorial_le_exp (x := 1 + |y|) hu.le (r + 2)
  rw [exp_add, div_le_iff₀ (Nat.cast_pos.2 (Nat.factorial_pos _))] at hf
  have hf2 : (1 + |y|) ^ (r + 2) ≤ (r + 2).factorial * exp 1 * exp (π / 2 * |y|) := by
    refine hf.trans ?_
    rw [mul_comm (exp 1 * exp |y|), mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (exp_le_exp.2 hpi)
      (exp_pos 1).le) (Nat.cast_nonneg _)
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg hu.le r) (exp_pos _).le), Real.norm_eq_abs,
    rpow_neg hu.le, rpow_two, neg_mul, exp_neg, ← div_eq_mul_inv, ← div_eq_mul_inv,
    div_le_div_iff₀ (exp_pos _) (pow_pos hu 2), ← pow_add]
  exact hf2

theorem coarseMaj_eq (N : ℕ) : coarseMaj N =
    2 ^ (12 * N) * (Gamma (6 * N) * Gamma (11 * N + 1) / Gamma (17 * N + 1)) *
      (Gamma (3 * N) * Gamma (3 * N + 1) * (Gamma (4 * N) * Gamma (4 * N + 1) *
        (Gamma (5 * N) * Gamma (5 * N + 1)))) / Gamma (8 * N + 1) ^ 3 := by
  rw [coarseMaj, Finset.prod_insert (show (3 : ℕ) ∉ ({4, 5} : Finset ℕ) by decide),
    Finset.prod_insert (show (4 : ℕ) ∉ ({5} : Finset ℕ) by decide),
    Finset.prod_singleton]
  simp only [Nat.cast_ofNat]

theorem gamma_natMul_pos (c : ℝ) (hc : 0 < c) (N : ℕ) (hN : 1 ≤ N) : 0 < Gamma (c * N) :=
  Gamma_pos_of_pos (mul_pos hc (Nat.cast_pos.2 hN))

theorem gamma_natMul_add_one_pos (c : ℝ) (hc : 0 < c) (N : ℕ) : 0 < Gamma (c * N + 1) :=
  Gamma_pos_of_pos (add_pos_of_nonneg_of_pos (mul_nonneg hc.le (Nat.cast_nonneg N)) one_pos)

theorem coarseMaj_pos (N : ℕ) (hN : 1 ≤ N) : 0 < coarseMaj N := by
  rw [coarseMaj_eq]
  exact div_pos (mul_pos (mul_pos (pow_pos two_pos _)
    (div_pos (mul_pos (gamma_natMul_pos 6 Nat.ofNat_pos N hN)
      (gamma_natMul_add_one_pos 11 Nat.ofNat_pos N)) (gamma_natMul_add_one_pos 17 Nat.ofNat_pos N)))
    (mul_pos (mul_pos (gamma_natMul_pos 3 Nat.ofNat_pos N hN)
      (gamma_natMul_add_one_pos 3 Nat.ofNat_pos N))
      (mul_pos (mul_pos (gamma_natMul_pos 4 Nat.ofNat_pos N hN)
        (gamma_natMul_add_one_pos 4 Nat.ofNat_pos N))
        (mul_pos (gamma_natMul_pos 5 Nat.ofNat_pos N hN)
          (gamma_natMul_add_one_pos 5 Nat.ofNat_pos N)))))
    (pow_pos (gamma_natMul_add_one_pos 8 Nat.ofNat_pos N) 3)

theorem gamma_line_bound (m : ℕ) (hm : 0 < m) (a y : ℝ) (ha : a = m) (z : ℂ)
    (hz : z = a + y * Complex.I) :
    ‖Complex.Gamma z‖ ≤ Gamma a * √2 ^ m * exp (-(π / 4) * |y|) := by
  have hpos : 0 < a := by rw [ha]; exact Nat.cast_pos.2 hm
  have h := gamma_rotation_bound a y (π / 4) hpos (div_pos pi_pos four_pos)
    (div_lt_div_of_pos_left pi_pos two_pos (by norm_num))
  rw [hz]
  refine h.trans (le_of_eq ?_)
  rw [cos_pi_div_four, ha, rpow_neg (div_nonneg (sqrt_nonneg 2) zero_le_two), rpow_natCast,
    ← inv_pow, inv_div, div_sqrt]

theorem norm_t_pow_le (N r : ℕ) (hN : 1 ≤ N) (y : ℝ) :
    ‖(-(((6 * N : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I)) ^ r‖ ≤ (6 * N) ^ r * (1 + |y|) ^ r := by
  have h6 : (1 : ℝ) ≤ 6 * N :=
    one_le_mul_of_one_le_of_one_le Nat.one_le_ofNat (Nat.one_le_cast.2 hN)
  rw [norm_pow, norm_neg, ← mul_pow]
  refine pow_le_pow_left₀ (norm_nonneg _) ((norm_add_le _ _).trans ?_) r
  rw [norm_mul _ Complex.I, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_neg, abs_of_nonneg (zero_le_one.trans h6), mul_one_add]
  exact add_le_add le_rfl (le_mul_of_one_le_left (abs_nonneg y) h6)

theorem norm_beta_factor (N : ℕ) (hN : 1 ≤ N) (y : ℝ) :
    ‖-(Complex.Gamma (((6 * N : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I) *
        Complex.Gamma (11 * N + 1) /
        Complex.Gamma (((6 * N : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I + 11 * N + 1))‖ ≤
      Gamma (6 * N) * Gamma (11 * N + 1) / Gamma (17 * N + 1) := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have h := beta_bound (6 * N) (11 * N + 1) (-y) (mul_pos Nat.ofNat_pos hN')
    (add_pos (mul_pos Nat.ofNat_pos hN') one_pos)
  rw [show (6 : ℝ) * N + (11 * N + 1) = 17 * N + 1 by ring] at h
  have e1 : (11 * N + 1 : ℂ) = ((11 * N + 1 : ℝ) : ℂ) := by
    rw [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_one,
      Complex.ofReal_ofNat]
  have e2 : ((6 * N : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I + 11 * N + 1 =
      ((6 * N : ℝ) : ℂ) + ((11 * N + 1 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [norm_neg, e2, e1]
  exact h

theorem norm_sin_factor (N : ℕ) (y : ℝ) :
    ‖Complex.sin (π * (((6 * N : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I)) / π‖ ≤
      exp (π * |y|) / π := by
  rw [norm_div, Complex.norm_of_nonneg pi_pos.le]
  refine div_le_div_of_nonneg_right ((norm_sin_le_exp _).trans (le_of_eq ?_)) pi_pos.le
  rw [Complex.im_ofReal_mul, im_ofReal_add_mul_I, abs_mul, abs_of_pos pi_pos, abs_neg]

theorem mul6_le {a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆ : ℝ} (n₁ : 0 ≤ a₁) (n₂ : 0 ≤ a₂)
    (n₃ : 0 ≤ a₃) (n₄ : 0 ≤ a₄) (n₅ : 0 ≤ a₅) (n₆ : 0 ≤ a₆) (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂)
    (h₃ : a₃ ≤ b₃) (h₄ : a₄ ≤ b₄) (h₅ : a₅ ≤ b₅) (h₆ : a₆ ≤ b₆) :
    a₁ * a₂ * (a₃ * a₄ * (a₅ * a₆)) ≤ b₁ * b₂ * (b₃ * b₄ * (b₅ * b₆)) :=
  mul_le_mul (mul_le_mul h₁ h₂ n₂ (n₁.trans h₁))
    (mul_le_mul (mul_le_mul h₃ h₄ n₄ (n₃.trans h₃)) (mul_le_mul h₅ h₆ n₆ (n₅.trans h₅))
      (mul_nonneg n₅ n₆) (mul_nonneg (n₃.trans h₃) (n₄.trans h₄)))
    (mul_nonneg (mul_nonneg n₃ n₄) (mul_nonneg n₅ n₆)) (mul_nonneg (n₁.trans h₁) (n₂.trans h₂))

theorem mul4_div_le {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ d : ℝ} (n₁ : 0 ≤ a₁) (n₂ : 0 ≤ a₂) (n₃ : 0 ≤ a₃)
    (n₄ : 0 ≤ a₄) (hd : 0 ≤ d) (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) (h₃ : a₃ ≤ b₃) (h₄ : a₄ ≤ b₄) :
    a₁ * a₂ * a₃ * a₄ / d ≤ b₁ * b₂ * b₃ * b₄ / d :=
  div_le_div_of_nonneg_right (mul_le_mul (mul_le_mul (mul_le_mul h₁ h₂ n₂ (n₁.trans h₁)) h₃ n₃
    (mul_nonneg (n₁.trans h₁) (n₂.trans h₂))) h₄ n₄
    (mul_nonneg (mul_nonneg (n₁.trans h₁) (n₂.trans h₂)) (n₃.trans h₃))) hd

theorem norm_gamma_prod (N : ℕ) (hN : 1 ≤ N) (y : ℝ) :
    ‖∏ v ∈ ({1, 2, 3} : Finset ℕ),
        Complex.Gamma ((((6 * N : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I) - v * N) *
          Complex.Gamma ((v + 8) * N + 1 - (((6 * N : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I))‖ ≤
      Gamma (5 * N) * √2 ^ (5 * N) * exp (-(π / 4) * |-y|) *
          (Gamma (3 * N + 1) * √2 ^ (3 * N + 1) * exp (-(π / 4) * |y|)) *
        (Gamma (4 * N) * √2 ^ (4 * N) * exp (-(π / 4) * |-y|) *
            (Gamma (4 * N + 1) * √2 ^ (4 * N + 1) * exp (-(π / 4) * |y|)) *
          (Gamma (3 * N) * √2 ^ (3 * N) * exp (-(π / 4) * |-y|) *
            (Gamma (5 * N + 1) * √2 ^ (5 * N + 1) * exp (-(π / 4) * |y|)))) := by
  rw [Finset.prod_insert (show (1 : ℕ) ∉ ({2, 3} : Finset ℕ) by decide),
    Finset.prod_insert (show (2 : ℕ) ∉ ({3} : Finset ℕ) by decide), Finset.prod_singleton]
  simp only [norm_mul]
  exact mul6_le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _)
    (gamma_line_bound (5 * N) (by omega) _ _ (by rw [Nat.cast_mul, Nat.cast_ofNat]) _
      (by push_cast; ring))
    (gamma_line_bound (3 * N + 1) (by omega) _ _
      (by rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]) _ (by push_cast; ring))
    (gamma_line_bound (4 * N) (by omega) _ _ (by rw [Nat.cast_mul, Nat.cast_ofNat]) _
      (by push_cast; ring))
    (gamma_line_bound (4 * N + 1) (by omega) _ _
      (by rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]) _ (by push_cast; ring))
    (gamma_line_bound (3 * N) (by omega) _ _ (by rw [Nat.cast_mul, Nat.cast_ofNat]) _
      (by push_cast; ring))
    (gamma_line_bound (5 * N + 1) (by omega) _ _
      (by rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]) _ (by push_cast; ring))

theorem norm_five (a b c d e : ℂ) : ‖a * b * c * d / e‖ = ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ / ‖e‖ := by
  rw [norm_div, norm_mul, norm_mul, norm_mul]

theorem pointwise_bound (N r : ℕ) (hN : 1 ≤ N) (y : ℝ) (hy : y ≠ 0) :
    ‖((π : ℂ) / Complex.sin (π * Zeta2BarnesIdentities.lineAt (-((6 * N : ℕ) : ℝ)) y)) ^ 2 *
        Gint N r (Zeta2BarnesIdentities.lineAt (-((6 * N : ℕ) : ℝ)) y)‖ ≤
      6 ^ r * √2 ^ 3 / π * ((N : ℝ) ^ r * coarseMaj N) *
        ((1 + |y|) ^ r * exp (-(π / 2) * |y|)) := by
  have hline : Zeta2BarnesIdentities.lineAt (-((6 * N : ℕ) : ℝ)) y =
      -(((6 * N : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I) := by
    rw [Zeta2BarnesIdentities.lineAt]
    push_cast
    ring
  have him : (((6 * N : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I).im ≠ 0 := by
    rw [im_ofReal_add_mul_I]
    exact neg_ne_zero.2 hy
  have hE : exp (π * |y|) * exp (-(π / 4) * |y|) ^ 6 = exp (-(π / 2) * |y|) := by
    rw [← exp_nat_mul, ← exp_add]
    congr 1
    push_cast
    ring
  have h22 : (2 : ℝ) ^ (12 * N) = √2 ^ (2 * (12 * N)) := by rw [pow_mul (√2) 2, sq_sqrt zero_le_two]
  have hG8 : ‖Complex.Gamma (8 * N + 1) ^ 3‖ = Gamma (8 * N + 1) ^ 3 := by
    rw [norm_pow, show (8 : ℂ) * N + 1 = ((8 * N + 1 : ℝ) : ℂ) by push_cast; rfl,
      Complex.Gamma_ofReal, Complex.norm_of_nonneg (gamma_natMul_add_one_pos 8 Nat.ofNat_pos N).le]
  rw [hline, reflection_form N r _ him, norm_five, hG8]
  refine (mul4_div_le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (pow_nonneg (gamma_natMul_add_one_pos 8 Nat.ofNat_pos N).le 3) (norm_t_pow_le N r hN y)
    (norm_beta_factor N hN y) (norm_sin_factor N y) (norm_gamma_prod N hN y)).trans (le_of_eq ?_)
  rw [coarseMaj_eq, h22, ← hE, abs_neg]
  ring

theorem err_eq_integral (N : ℕ) (hN : 1 ≤ N) (r : Fin 3) :
    |(CN N : ℝ) * Err N r| = 1 / π * ‖∫ y : ℝ,
      ((π : ℂ) / Complex.sin (π * Zeta2BarnesIdentities.lineAt (-((6 * N : ℕ) : ℝ)) y)) ^ 2 *
        Gint N r (Zeta2BarnesIdentities.lineAt (-((6 * N : ℕ) : ℝ)) y)‖ := by
  have h := Zeta2ErrorIntegral.error_integral N r (6 * N) (by omega) (by omega)
  rw [show (fun s : ℂ => s ^ (r : ℕ) * aeval s (Fpoly N) * Lker (11 * N) s) = Gint N r from rfl,
    barnes_shift_6N N r hN, Zeta2BarnesIdentities.barnesAt] at h
  rw [← Real.norm_eq_abs, ← Complex.norm_real, h, norm_mul, norm_mul, norm_neg, Complex.norm_two,
    norm_div, norm_one, norm_mul, Complex.norm_two, Complex.norm_of_nonneg pi_pos.le]
  ring

/-- **Lemma 5 (the coarse bound (A3)).** There is `K_r > 0` with
`|C_N 𝖤_{N,r}| ≤ K_r N^r · coarseMaj N` for all `N ≥ 1`.
Assembly: `error_integral` with `η = 6N`, `barnes_shift_6N`, the substitution `s = -t`,
`reflection_form`, `gamma_rotation_bound` with `θ = π/4` for the six Gamma factors (real parts
`3N, 3N+1, 4N, 4N+1, 5N, 5N+1`, total factor `2^{12N+3/2} e^{-3π|y|/2}`), `beta_bound`,
`|sin πt| ≤ e^{π|y|}`, `|t|^r ≤ (6N + |y|)^r`, and `∫ (6N+|y|)^r e^{-π|y|/2} dy ≤ K' N^r`.

* Estimated length: 120 lines.
* Formalizable directly from the pdf: yes, given Lemmas 1–4 (§6.2 lists every factor). -/
theorem A3_bound (r : Fin 3) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 1 ≤ N →
      |(CN N : ℝ) * Err N r| ≤ K * (N : ℝ) ^ (r : ℕ) * coarseMaj N := by
  have hJ0 : 0 ≤ ∫ y : ℝ, (1 + |y|) ^ (r : ℕ) * exp (-(π / 2) * |y|) :=
    integral_nonneg (fun y => mul_nonneg (pow_nonneg (add_nonneg zero_le_one (abs_nonneg y)) _)
      (exp_pos _).le)
  have hC0 : 0 ≤ (6 : ℝ) ^ (r : ℕ) * √2 ^ 3 / π :=
    div_nonneg (mul_nonneg (pow_nonneg Nat.ofNat_pos.le _) (pow_nonneg (sqrt_nonneg 2) 3))
      pi_pos.le
  refine ⟨6 ^ (r : ℕ) * √2 ^ 3 / π * (∫ y : ℝ, (1 + |y|) ^ (r : ℕ) * exp (-(π / 2) * |y|)) / π + 1,
    add_pos_of_nonneg_of_pos (div_nonneg (mul_nonneg hC0 hJ0) pi_pos.le) one_pos, fun N hN => ?_⟩
  have hX : 0 ≤ (N : ℝ) ^ (r : ℕ) * coarseMaj N :=
    mul_nonneg (pow_nonneg (Nat.cast_nonneg N) _) (coarseMaj_pos N hN).le
  have hint := (majorant_integrable r).const_mul
    (6 ^ (r : ℕ) * √2 ^ 3 / π * ((N : ℝ) ^ (r : ℕ) * coarseMaj N))
  have hle := norm_integral_le_of_norm_le hint (by
    filter_upwards [Measure.ae_ne volume 0] with y hy
    exact pointwise_bound N r hN y hy)
  rw [integral_const_mul] at hle
  rw [err_eq_integral N hN r]
  calc _ ≤ 1 / π * (6 ^ (r : ℕ) * √2 ^ 3 / π * ((N : ℝ) ^ (r : ℕ) * coarseMaj N) *
        ∫ y : ℝ, (1 + |y|) ^ (r : ℕ) * exp (-(π / 2) * |y|)) :=
        mul_le_mul_of_nonneg_left hle (div_nonneg zero_le_one pi_pos.le)
    _ = 6 ^ (r : ℕ) * √2 ^ 3 / π * (∫ y : ℝ, (1 + |y|) ^ (r : ℕ) * exp (-(π / 2) * |y|)) / π *
          ((N : ℝ) ^ (r : ℕ) * coarseMaj N) := by ring
    _ ≤ (6 ^ (r : ℕ) * √2 ^ 3 / π * (∫ y : ℝ, (1 + |y|) ^ (r : ℕ) * exp (-(π / 2) * |y|)) / π + 1) *
          ((N : ℝ) ^ (r : ℕ) * coarseMaj N) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hX
    _ = _ := by ring

theorem log_gamma_nat_mul_add_one (k N : ℕ) (hk : 0 < k) (hN : 0 < N) :
    log (Gamma ((k : ℝ) * N + 1)) = k * N * log k + k * N * log N - k * N +
      (log (Stirling.stirlingSeq (k * N)) + 1 / 2 * (log 2 + log k + log N)) := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have h := Stirling.log_stirlingSeq_formula (k * N)
  rw [Nat.cast_mul, Real.log_div (mul_ne_zero hk' hN') (exp_ne_zero 1), Real.log_exp,
    Real.log_mul two_ne_zero (mul_ne_zero hk' hN'), Real.log_mul hk' hN'] at h
  rw [show (k : ℝ) * N + 1 = ((k * N : ℕ) : ℝ) + 1 by rw [Nat.cast_mul],
    Real.Gamma_nat_eq_factorial]
  linear_combination -h

theorem log_gamma_nat_mul (k N : ℕ) (hk : 0 < k) (hN : 0 < N) :
    log (Gamma ((k : ℝ) * N)) = log (Gamma ((k : ℝ) * N + 1)) - log k - log N := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hpos : (0 : ℝ) < k * N := mul_pos (Nat.cast_pos.2 hk) (Nat.cast_pos.2 hN)
  rw [Real.Gamma_add_one (mul_ne_zero hk' hN'),
    Real.log_mul (mul_ne_zero hk' hN') (Gamma_pos_of_pos hpos).ne', Real.log_mul hk' hN']
  ring

theorem log_maj_aux {K X A B C D G P₃ Q₃ P₄ Q₄ P₅ Q₅ : ℝ} (hK : 0 < K) (hX : 0 < X)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D) (hG : 0 < G) (h₃ : 0 < P₃)
    (h₃' : 0 < Q₃) (h₄ : 0 < P₄) (h₄' : 0 < Q₄) (h₅ : 0 < P₅) (h₅' : 0 < Q₅) :
    log (K * X * (A * (B * C / D) * (P₃ * Q₃ * (P₄ * Q₄ * (P₅ * Q₅))) / G ^ 3)) =
      log X + log K + log A + (log B + log C - log D) +
        (log P₃ + log Q₃ + (log P₄ + log Q₄ + (log P₅ + log Q₅))) - 3 * log G := by
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_pow, Nat.cast_ofNat]
  ring

theorem log_maj_eq (r N : ℕ) (hN : 1 ≤ N) (K : ℝ) (hK : 0 < K) :
    log (K * (N : ℝ) ^ r * coarseMaj N) = N * hconst +
      ((log K + 1 / 2 * (log 2 + log 6) - log 6 + 1 / 2 * (log 2 + log 11) -
          1 / 2 * (log 2 + log 17) + 3 * log 2 - 3 / 2 * (log 2 + log 8)) +
        ((r : ℝ) - 2) * log N +
        (log (Stirling.stirlingSeq (6 * N)) + log (Stirling.stirlingSeq (11 * N)) -
          log (Stirling.stirlingSeq (17 * N)) + 2 * log (Stirling.stirlingSeq (3 * N)) +
          2 * log (Stirling.stirlingSeq (4 * N)) + 2 * log (Stirling.stirlingSeq (5 * N)) -
          3 * log (Stirling.stirlingSeq (8 * N)))) := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
  rw [coarseMaj_eq, log_maj_aux hK (pow_pos hN' r) (pow_pos two_pos _)
    (gamma_natMul_pos 6 Nat.ofNat_pos N hN) (gamma_natMul_add_one_pos 11 Nat.ofNat_pos N)
    (gamma_natMul_add_one_pos 17 Nat.ofNat_pos N) (gamma_natMul_add_one_pos 8 Nat.ofNat_pos N)
    (gamma_natMul_pos 3 Nat.ofNat_pos N hN) (gamma_natMul_add_one_pos 3 Nat.ofNat_pos N)
    (gamma_natMul_pos 4 Nat.ofNat_pos N hN) (gamma_natMul_add_one_pos 4 Nat.ofNat_pos N)
    (gamma_natMul_pos 5 Nat.ofNat_pos N hN) (gamma_natMul_add_one_pos 5 Nat.ofNat_pos N),
    Real.log_pow, Real.log_pow]
  have h3 := log_gamma_nat_mul 3 N Nat.ofNat_pos hN
  have h4 := log_gamma_nat_mul 4 N Nat.ofNat_pos hN
  have h5 := log_gamma_nat_mul 5 N Nat.ofNat_pos hN
  have h6 := log_gamma_nat_mul 6 N Nat.ofNat_pos hN
  have g3 := log_gamma_nat_mul_add_one 3 N Nat.ofNat_pos hN
  have g4 := log_gamma_nat_mul_add_one 4 N Nat.ofNat_pos hN
  have g5 := log_gamma_nat_mul_add_one 5 N Nat.ofNat_pos hN
  have g6 := log_gamma_nat_mul_add_one 6 N Nat.ofNat_pos hN
  have g8 := log_gamma_nat_mul_add_one 8 N Nat.ofNat_pos hN
  have g11 := log_gamma_nat_mul_add_one 11 N Nat.ofNat_pos hN
  have g17 := log_gamma_nat_mul_add_one 17 N Nat.ofNat_pos hN
  simp only [Nat.cast_ofNat] at h3 h4 h5 h6 g3 g4 g5 g6 g8 g11 g17
  rw [h3, h4, h5, h6, g3, g4, g5, g6, g8, g11, g17, hconst]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem stirling_isLittleO (k : ℕ) (hk : 0 < k) :
    (fun N : ℕ => log (Stirling.stirlingSeq (k * N))) =o[atTop] (fun N : ℕ => (N : ℝ)) := by
  have h1 : Tendsto (fun N : ℕ => k * N) atTop atTop :=
    tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_left N hk) tendsto_id
  have h2 := (Stirling.tendsto_stirlingSeq_sqrt_pi.comp h1).log (Real.sqrt_ne_zero'.2 pi_pos)
  exact (h2.isBigO_one ℝ).trans_isLittleO (Asymptotics.isLittleO_const_left.2
    (Or.inr (tendsto_norm_atTop_atTop.comp tendsto_natCast_atTop_atTop)))

/-- **Lemma 6 (Stirling: the rate (A4) of the majorant).** For every `K > 0` the majorant
`K N^r coarseMaj N` is positive for `N ≥ 1` and `(1/N) log (K N^r coarseMaj N) → h`.

* Estimated length: 100 lines (`Real.Gamma_nat_eq_factorial`, `Real.Gamma_add_one`, Stirling
  `Stirling.factorial_isEquivalent_stirling` or `log n! = n log n - n + O(log n)`; the `N log N`
  terms cancel because `6 + 11 - 17 = 0` and `2(3+4+5) - 24 = 0`).
* Formalizable directly from the pdf: yes ("Stirling's formula gives"). -/
theorem coarse_rate (r : ℕ) (K : ℝ) (hK : 0 < K) :
    (∀ N : ℕ, 1 ≤ N → 0 < K * (N : ℝ) ^ r * coarseMaj N) ∧
      Tendsto (fun N : ℕ => log (K * (N : ℝ) ^ r * coarseMaj N) / N) atTop (𝓝 hconst) := by
  refine ⟨fun N hN => mul_pos (mul_pos hK (pow_pos (Nat.cast_pos.2 hN) r)) (coarseMaj_pos N hN),
    ?_⟩
  have hc : ∀ c : ℝ, (fun _ : ℕ => c) =o[atTop] (fun N : ℕ => (N : ℝ)) := fun c =>
    Asymptotics.isLittleO_const_left.2
      (Or.inr (tendsto_norm_atTop_atTop.comp tendsto_natCast_atTop_atTop))
  have hl : (fun N : ℕ => log (N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ)) :=
    isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  have hS := fun k (hk : 0 < k) => stirling_isLittleO k hk
  have hE := ((hc (log K + 1 / 2 * (log 2 + log 6) - log 6 + 1 / 2 * (log 2 + log 11) -
          1 / 2 * (log 2 + log 17) + 3 * log 2 - 3 / 2 * (log 2 + log 8))).add
      (hl.const_mul_left ((r : ℝ) - 2))).add
    ((((((((hS 6 Nat.ofNat_pos).add (hS 11 Nat.ofNat_pos)).sub (hS 17 Nat.ofNat_pos)).add
      ((hS 3 Nat.ofNat_pos).const_mul_left 2)).add ((hS 4 Nat.ofNat_pos).const_mul_left 2)).add
      ((hS 5 Nat.ofNat_pos).const_mul_left 2)).sub ((hS 8 Nat.ofNat_pos).const_mul_left 3)))
  have hT := hE.tendsto_div_nhds_zero.const_add hconst
  rw [add_zero] at hT
  refine hT.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.1 hN)
  rw [log_maj_eq r N hN K hK, add_div ((N : ℝ) * hconst), mul_div_cancel_left₀ _ hN']

/-- **Lemma 7 (numerical value of (A4)).** `h < -18`.

* Estimated length: 40 lines (rational enclosures of `log 2, log 3, log 5, log 11, log 17`, e.g.
  from `Real.log_two_gt_d9`/`Real.log_two_lt_d9` and the series used in the Python certificate;
  `log 4 = 2 log 2`, `log 6 = log 2 + log 3`, `log 8 = 3 log 2`).
* Formalizable directly from the pdf: no — the pdf only states the inequality; it is certified by
  `code/analytic/certify_analytic_rates.py` (assertion `hb[1] < -18`), whose rational
  log-enclosure argument (pdf §6.4) can be replayed with `norm_num`. -/
theorem hconst_lt : hconst < -18 := by
  have hR : (0 : ℝ) < 3 ^ 12 * 5 ^ 10 * 11 ^ 11 / (2 ^ 38 * 17 ^ 17) := by positivity
  have l4 : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow, Nat.cast_ofNat]
  have l6 : log 6 = log 2 + log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, log_mul two_ne_zero three_ne_zero]
  have l8 : log 8 = 3 * log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow, Nat.cast_ofNat]
  have lR : log (3 ^ 12 * 5 ^ 10 * 11 ^ 11 / (2 ^ 38 * 17 ^ 17) : ℝ) =
      12 * log 3 + 10 * log 5 + 11 * log 11 - (38 * log 2 + 17 * log 17) := by
    rw [log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity),
      log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
      log_pow, log_pow, log_pow, log_pow, log_pow]
    norm_num
  have hlog : hconst = log (3 ^ 12 * 5 ^ 10 * 11 ^ 11 / (2 ^ 38 * 17 ^ 17) : ℝ) := by
    rw [lR, hconst, l4, l6, l8]
    ring
  have he : exp 18 < (3 ^ 12 * 5 ^ 10 * 11 ^ 11 / (2 ^ 38 * 17 ^ 17) : ℝ)⁻¹ :=
    calc exp 18 = exp 1 ^ 18 := by rw [← exp_nat_mul, Nat.cast_ofNat, mul_one]
      _ < 2.7182818286 ^ 18 := pow_lt_pow_left₀ exp_one_lt_d9 (exp_pos 1).le (by norm_num)
      _ < (3 ^ 12 * 5 ^ 10 * 11 ^ 11 / (2 ^ 38 * 17 ^ 17) : ℝ)⁻¹ := by norm_num
  rw [hlog, log_lt_iff_lt_exp hR, exp_neg, lt_inv_comm₀ hR (exp_pos 18)]
  exact he

/-- **Coarse bound (A3)–(A4)** — restatement of `Zeta2Blueprint.error_coarse_bound`, proved from
Lemmas 5–7 (Lemmas 1–4 are the ingredients of Lemma 5). -/
theorem error_coarse_bound (r : Fin 3) :
    ∀ᶠ N : ℕ in atTop, |(CN N : ℝ) * Err N r| ≤ exp (-18 * N) := by
  obtain ⟨K, hK, hA3⟩ := A3_bound r
  obtain ⟨hpos, hlim⟩ := coarse_rate r K hK
  filter_upwards [hlim.eventually (gt_mem_nhds hconst_lt), eventually_ge_atTop 1] with N h hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_lt_iff₀ hN'] at h
  calc |(CN N : ℝ) * Err N r| ≤ K * (N : ℝ) ^ (r : ℕ) * coarseMaj N := hA3 N hN
    _ = exp (log (K * (N : ℝ) ^ (r : ℕ) * coarseMaj N)) := (exp_log (hpos N hN)).symm
    _ ≤ exp (-18 * N) := exp_le_exp.2 h.le

end Zeta2ErrorCoarseBound
