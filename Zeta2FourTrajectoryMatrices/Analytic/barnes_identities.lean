/-
# Blueprint: `barnes_identities` (§6.1 of the article)

Statement (`Zeta2Blueprint.barnes_identities`, restated verbatim below): for every `η : ℕ`,

* `𝓘_η(P) = J_η(P)` for every polynomial `P ∈ ℚ[X]`, and
* `𝓘_η(1/(s - j)) = H^{(2)}_{j+η} - ζ(2)` for every `j : ℕ`,

where `𝓘_η(g) = (2πi)⁻¹ ∫_{Re s = -η-1/2} (π / sin πs)² g(s) ds`.

Proof outline (article §6.1).
* The kernel `K(s) = (π / sin πs)²` is `1`-periodic, decays like `e^{-2π|Im s|}`, and has a double
  pole at every integer `n` with Laurent expansion `K(s) = (s-n)⁻² + π²/3 + O((s-n)²)`.
* Moving the line one unit to the right across the pole `n` changes the integral by the residue
  of `K g` at `n`, which is `g'(n)` for `g` holomorphic near `n` (`barnes_step`).
* Polynomials: by periodicity, `𝓘_η(P(s+1)) - 𝓘_η(P(s))` is the difference of the integrals over
  the lines `Re s = -η ± 1/2`, i.e. `P'(-η)` (`barnes_poly_delta`). The same identity holds for
  `J_η` (`Zeta2FirstThree.J_delta`, already proved), and `Δ` is onto (`delta_surj`).
* Resolvents: moving the line to `+∞` (`barnes_vanish_right`) and summing the residues
  `-(n-j)⁻²` (`barnes_step_resolvent`) and `π²/3` (`barnes_step_pole`) gives
  `𝓘_η(1/(s-j)) = ∑_{n ≥ -η, n ≠ j} (n-j)⁻² - π²/3 = H^{(2)}_{j+η} + ζ(2) - 2ζ(2)`
  (`resolvent_hasSum`).

The supporting lemmas are `sorry`; the main theorem is proved from them below.
Numerical diagnostic only (not a proof ingredient):
`results/zeta2_complete_proof/evidence/check_barnes_integral.py`.
-/
import Zeta2FourTrajectoryMatrices.FiniteReadout.blueprint_first_three
import Zeta2FourTrajectoryMatrices.Analytic.barnes_step_aux2

open Polynomial Filter Topology Real Finset MeasureTheory Zeta2Blueprint

noncomputable section

namespace Zeta2BarnesIdentities

/-- The point `c + i y` of the vertical line `Re s = c`. -/
def lineAt (c : ℝ) (y : ℝ) : ℂ := (c : ℂ) + y * Complex.I

/-- `(2πi)⁻¹ ∫_{Re s = c} (π / sin πs)² g(s) ds`, parametrised by `s = c + i y`. -/
def barnesAt (c : ℝ) (g : ℂ → ℂ) : ℂ :=
  (1 / (2 * π)) * ∫ y : ℝ,
    ((π : ℂ) / Complex.sin ((π : ℂ) * lineAt c y)) ^ 2 * g (lineAt c y)

/-- **Lemma 1 (the article's contour is the line `Re s = -η - 1/2`).**
`barnesI η = barnesAt (-η - 1/2)`.

* Estimated length: 5 lines (unfolding and `push_cast`).
* Formalizable directly from the pdf: yes (it is the definition of `𝓘_η`). -/
theorem barnesI_eq (η : ℕ) (g : ℂ → ℂ) : barnesI η g = barnesAt (-(η : ℝ) - 1 / 2) g := by
  have h : ∀ y : ℝ, barnesLine η y = lineAt (-(η : ℝ) - 1 / 2) y := fun y => by
    simp only [barnesLine, lineAt]
    push_cast
    ring
  simp only [barnesI, barnesAt, h]

/-- **Lemma 2 (periodicity of the kernel).** Translating the integrand by `1` is the same as
moving the line one unit to the right: `sin(π(s+1)) = -sin(πs)`, so `K(s+1) = K(s)`.

* Estimated length: 15 lines (`Complex.sin_add_pi`, change of the parametrisation).
* Formalizable directly from the pdf: yes (the pdf uses it implicitly in "moving the line one
  unit to the right"). -/
theorem barnes_translate (c : ℝ) (g : ℂ → ℂ) :
    barnesAt c (fun s => g (s + 1)) = barnesAt (c + 1) g := by
  have h : ∀ y : ℝ, lineAt (c + 1) y = lineAt c y + 1 := fun y => by
    rw [lineAt, lineAt, Complex.ofReal_add, Complex.ofReal_one, add_right_comm]
  have h2 : ∀ y : ℝ, ((π : ℂ) / Complex.sin ((π : ℂ) * lineAt c y)) ^ 2 * g (lineAt c y + 1) =
      ((π : ℂ) / Complex.sin ((π : ℂ) * lineAt (c + 1) y)) ^ 2 * g (lineAt (c + 1) y) :=
    fun y => by rw [h, mul_add, mul_one, Complex.sin_add_pi, div_neg, neg_sq]
  exact congrArg (fun F : ℝ → ℂ => (1 / (2 * π) : ℂ) * ∫ y : ℝ, F y) (funext h2)

/-- **Lemma 3 (crossing one double pole: the regular residue).** If `g` is holomorphic on the
open strip `|Re s - n| < 3/4` and has polynomial growth in `Im s` on the closed strip
`|Re s - n| ≤ 1/2`, then the integrals over the lines `Re s = n ± 1/2` differ by the residue of
`K g` at `n`, namely `g'(n)` (since `K(s) = (s-n)⁻² + π²/3 + O((s-n)²)`).

* Estimated length: 200 lines (rectangle Cauchy theorem `Complex.integral_boundary_rect_eq_zero_of_
  differentiableOn` applied to `K g - g(n)/(s-n)² - g'(n)/(s-n)`, explicit integrals of the two
  principal parts, the bound `|K(x+iy)| ≤ C e^{-2π|y|}` for the horizontal edges).
* Formalizable directly from the pdf: partially. The pdf states the residue `P'(-η)` and the decay
  of the horizontal segments; the Laurent expansion of `(π/sin πs)²` and the residue computation
  for a double pole must be supplied (Mathlib has no general residue theorem). -/
theorem barnes_step (n : ℤ) (g : ℂ → ℂ) (hd : DifferentiableOn ℂ g {s | |s.re - n| < 3 / 4})
    (C : ℝ) (d : ℕ) (hb : ∀ s : ℂ, |s.re - n| ≤ 1 / 2 → ‖g s‖ ≤ C * (1 + |s.im|) ^ d) :
    barnesAt (n + 1 / 2) g - barnesAt (n - 1 / 2) g = deriv g n :=
  Zeta2BarnesStep.barnes_step_core n g hd C d hb

theorem sin_line_normSq (x y : ℝ) :
    Complex.normSq (Complex.sin ((π : ℂ) * lineAt x y)) =
      Real.sin (π * x) ^ 2 + Real.sinh (π * y) ^ 2 := by
  have h : (π : ℂ) * lineAt x y = ((π * x : ℝ) : ℂ) + ((π * y : ℝ) : ℂ) * Complex.I := by
    rw [lineAt, Complex.ofReal_mul, Complex.ofReal_mul, mul_add, mul_assoc]
  rw [h, Complex.sin_add_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_cos,
    ← Complex.ofReal_sinh, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.normSq_add_mul_I,
    mul_pow, mul_pow, Real.cosh_sq, Real.cos_sq']
  ring

theorem kernel_norm (x y : ℝ) :
    ‖((π : ℂ) / Complex.sin ((π : ℂ) * lineAt x y)) ^ 2‖ =
      π ^ 2 / (Real.sin (π * x) ^ 2 + Real.sinh (π * y) ^ 2) := by
  rw [norm_pow, norm_div, Complex.norm_real, Real.norm_of_nonneg pi_pos.le, div_pow,
    Complex.sq_norm (Complex.sin _), sin_line_normSq]

theorem half_sin_sq (k : ℤ) : Real.sin (π * ((k : ℝ) + 1 / 2)) ^ 2 = 1 := by
  have h : Real.cos (π * ((k : ℝ) + 1 / 2)) = 0 := Real.cos_eq_zero_iff.2 ⟨k, by ring⟩
  have h2 := Real.sin_sq_add_cos_sq (π * ((k : ℝ) + 1 / 2))
  rwa [h, zero_pow two_ne_zero, add_zero] at h2

theorem exp_abs_le_two_cosh (y : ℝ) : exp |y| ≤ 2 * Real.cosh (π * y) := by
  have h1 : |y| ≤ |π * y| := by
    rw [abs_mul, abs_of_pos pi_pos]
    exact le_mul_of_one_le_left (abs_nonneg y) (one_le_two.trans Real.two_le_pi)
  have h2 : exp |π * y| ≤ exp (π * y) + exp (-(π * y)) := by
    rcases abs_choice (π * y) with h | h <;> rw [h]
    · exact le_add_of_nonneg_right (exp_pos _).le
    · exact le_add_of_nonneg_left (exp_pos _).le
  rw [Real.cosh_eq, mul_div_cancel₀ _ two_ne_zero]
  exact (exp_le_exp.2 h1).trans h2

theorem half_kernel_le (k : ℤ) (m : ℕ) (y : ℝ) :
    ‖((π : ℂ) / Complex.sin ((π : ℂ) * lineAt ((k : ℝ) + 1 / 2) y)) ^ 2‖ *
      ((1 + |y|) ^ m) ^ 2 ≤ π ^ 2 * (2 * exp 1 * (m.factorial : ℝ)) ^ 2 := by
  have hc : 0 < Real.cosh (π * y) := Real.cosh_pos _
  have h1 : (1 + |y|) ^ m ≤ 2 * exp 1 * (m.factorial : ℝ) * Real.cosh (π * y) := by
    have h2 := Real.pow_div_factorial_le_exp (1 + |y|) (add_nonneg zero_le_one (abs_nonneg y)) m
    rw [div_le_iff₀ (Nat.cast_pos.2 (Nat.factorial_pos m) : (0 : ℝ) < m.factorial),
      exp_add] at h2
    calc (1 + |y|) ^ m ≤ exp 1 * exp |y| * (m.factorial : ℝ) := h2
      _ ≤ exp 1 * (2 * Real.cosh (π * y)) * (m.factorial : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (exp_abs_le_two_cosh y)
            (exp_pos 1).le) (Nat.cast_nonneg _)
      _ = 2 * exp 1 * (m.factorial : ℝ) * Real.cosh (π * y) := by ring
  have hcs : 1 + Real.sinh (π * y) ^ 2 = Real.cosh (π * y) ^ 2 := by
    rw [Real.cosh_sq, add_comm]
  rw [kernel_norm, half_sin_sq, hcs, div_mul_eq_mul_div, div_le_iff₀ (pow_pos hc 2), mul_assoc,
    ← mul_pow _ (Real.cosh (π * y))]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (pow_nonneg (add_nonneg zero_le_one
    (abs_nonneg y)) m) h1 2) (sq_nonneg π)

theorem poly_bound (P : ℚ[X]) (a : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, |s.re| ≤ a →
    ‖aeval s P‖ ≤ C * (1 + |s.im|) ^ P.natDegree := by
  refine ⟨(∑ i ∈ range (P.natDegree + 1), |(P.coeff i : ℝ)|) * (1 + |a|) ^ P.natDegree,
    mul_nonneg (sum_nonneg fun i _ => abs_nonneg _)
      (pow_nonneg (add_nonneg zero_le_one (abs_nonneg a)) _), fun s hs => ?_⟩
  have h1 : 1 + ‖s‖ ≤ (1 + |a|) * (1 + |s.im|) := by
    have h2 := Complex.norm_le_abs_re_add_abs_im s
    have h3 : |s.re| ≤ |a| := hs.trans (le_abs_self a)
    calc 1 + ‖s‖ ≤ 1 + (|a| + |s.im|) :=
          add_le_add (le_refl 1) (h2.trans (add_le_add h3 (le_refl _)))
      _ ≤ 1 + (|a| + |s.im|) + |a| * |s.im| :=
          le_add_of_nonneg_right (mul_nonneg (abs_nonneg a) (abs_nonneg _))
      _ = (1 + |a|) * (1 + |s.im|) := by ring
  have h4 : ∀ i ∈ range (P.natDegree + 1), ‖P.coeff i • s ^ i‖ ≤
      |(P.coeff i : ℝ)| * ((1 + |a|) ^ P.natDegree * (1 + |s.im|) ^ P.natDegree) := by
    intro i hi
    rw [Rat.smul_def, norm_mul, Complex.norm_ratCast, norm_pow, ← mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc ‖s‖ ^ i ≤ (1 + ‖s‖) ^ i :=
          pow_le_pow_left₀ (norm_nonneg s) (le_add_of_nonneg_left zero_le_one) i
      _ ≤ (1 + ‖s‖) ^ P.natDegree := pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg s))
          (Nat.lt_succ_iff.1 (mem_range.1 hi))
      _ ≤ ((1 + |a|) * (1 + |s.im|)) ^ P.natDegree :=
          pow_le_pow_left₀ (add_nonneg zero_le_one (norm_nonneg s)) h1 _
  rw [aeval_eq_sum_range, mul_assoc, sum_mul]
  exact (norm_sum_le _ _).trans (sum_le_sum h4)

theorem lineAt_re (c y : ℝ) : (lineAt c y).re = c := by
  simp [lineAt]

theorem lineAt_im (c y : ℝ) : (lineAt c y).im = y := by
  simp [lineAt]

theorem continuous_lineAt (c : ℝ) : Continuous (lineAt c) :=
  continuous_const.add (Complex.continuous_ofReal.mul continuous_const)

theorem integrable_half_poly (k : ℤ) (P : ℚ[X]) :
    Integrable (fun y : ℝ => ((π : ℂ) / Complex.sin ((π : ℂ) * lineAt ((k : ℝ) + 1 / 2) y)) ^ 2 *
      aeval (lineAt ((k : ℝ) + 1 / 2) y) P) := by
  obtain ⟨C, hC0, hC⟩ := poly_bound P |(k : ℝ) + 1 / 2|
  set D := π ^ 2 * (2 * exp 1 * ((P.natDegree + 1).factorial : ℝ)) ^ 2
  have hs : ∀ y : ℝ, Complex.sin ((π : ℂ) * lineAt ((k : ℝ) + 1 / 2) y) ≠ 0 := fun y h => by
    have h2 := sin_line_normSq ((k : ℝ) + 1 / 2) y
    rw [h, map_zero, half_sin_sq] at h2
    exact (add_pos_of_pos_of_nonneg one_pos (sq_nonneg (Real.sinh (π * y)))).ne h2
  have hcont : Continuous (fun y : ℝ =>
      ((π : ℂ) / Complex.sin ((π : ℂ) * lineAt ((k : ℝ) + 1 / 2) y)) ^ 2 *
        aeval (lineAt ((k : ℝ) + 1 / 2) y) P) :=
    ((continuous_const.div (Complex.continuous_sin.comp
      (continuous_const.mul (continuous_lineAt _))) hs).pow 2).mul
      ((Polynomial.continuous_aeval P).comp (continuous_lineAt _))
  refine (integrable_inv_one_add_sq.const_mul (D * C)).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  have hu : 1 ≤ 1 + |y| := le_add_of_nonneg_right (abs_nonneg y)
  have hy : 1 + y ^ 2 ≤ (1 + |y|) ^ 2 := by
    rw [add_sq, one_pow, mul_one, sq_abs]
    exact add_le_add (le_add_of_nonneg_right (mul_nonneg zero_le_two (abs_nonneg y))) (le_refl _)
  have hp := hC (lineAt ((k : ℝ) + 1 / 2) y) (by rw [lineAt_re])
  rw [lineAt_im] at hp
  have hK := half_kernel_le k (P.natDegree + 1) y
  rw [norm_mul, ← div_eq_mul_inv, le_div_iff₀ (add_pos_of_pos_of_nonneg one_pos (sq_nonneg y))]
  set K := ‖((π : ℂ) / Complex.sin ((π : ℂ) * lineAt ((k : ℝ) + 1 / 2) y)) ^ 2‖
  have hK0 : 0 ≤ K := norm_nonneg _
  calc K * ‖aeval (lineAt ((k : ℝ) + 1 / 2) y) P‖ * (1 + y ^ 2)
      ≤ K * (C * (1 + |y|) ^ P.natDegree) * (1 + |y|) ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hp hK0) hy
          (add_nonneg zero_le_one (sq_nonneg y))
          (mul_nonneg hK0 (mul_nonneg hC0 (pow_nonneg (zero_le_one.trans hu) _)))
    _ = C * (K * (1 + |y|) ^ (P.natDegree + 2)) := by rw [pow_add]; ring
    _ ≤ C * (K * ((1 + |y|) ^ (P.natDegree + 1)) ^ 2) := by
        rw [← pow_mul]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hu (by omega)) hK0) hC0
    _ ≤ C * D := mul_le_mul_of_nonneg_left hK hC0
    _ = D * C := mul_comm C D

theorem barnesAt_sub (c : ℝ) (f g : ℂ → ℂ)
    (hf : Integrable (fun y : ℝ =>
      ((π : ℂ) / Complex.sin ((π : ℂ) * lineAt c y)) ^ 2 * f (lineAt c y)))
    (hg : Integrable (fun y : ℝ =>
      ((π : ℂ) / Complex.sin ((π : ℂ) * lineAt c y)) ^ 2 * g (lineAt c y))) :
    barnesAt c (fun s => f s - g s) = barnesAt c f - barnesAt c g := by
  unfold barnesAt
  rw [← mul_sub, ← integral_sub hf hg]
  simp only [mul_sub]

/-- **Lemma 4 (the difference identity for polynomials).** `𝓘_η(P(s+1) - P(s)) = P'(-η)`.
Proof: integrability of `K · P` on vertical lines (exponential decay against polynomial growth)
gives linearity; then `barnes_translate` and `barnes_step` at `n = -η`.

* Estimated length: 60 lines (integrability, `integral_sub`, `aeval` of `taylor`,
  `Polynomial.deriv_aeval`, growth bound for a polynomial on a strip).
* Formalizable directly from the pdf: yes, given Lemmas 2–3 (this is the "direct verification"
  paragraph of §6.1). -/
theorem barnes_poly_delta (η : ℕ) (R : ℚ[X]) :
    barnesI η (fun s => aeval s (taylor 1 R - R)) = ((R.derivative.eval (-(η : ℚ)) : ℚ) : ℂ) := by
  have hc0 : -(η : ℝ) - 1 / 2 = (((-(η : ℤ) - 1 : ℤ)) : ℝ) + 1 / 2 := by
    rw [Int.cast_sub, Int.cast_neg, Int.cast_natCast, Int.cast_one]; ring
  have hc1 : (((-(η : ℤ) - 1 : ℤ)) : ℝ) + 1 / 2 = ((-(η : ℤ) : ℤ) : ℝ) - 1 / 2 := by
    rw [Int.cast_sub, Int.cast_one]; ring
  have hc2 : (((-(η : ℤ) - 1 : ℤ)) : ℝ) + 1 / 2 + 1 = ((-(η : ℤ) : ℤ) : ℝ) + 1 / 2 := by
    rw [Int.cast_sub, Int.cast_one]; ring
  have ht : (fun s : ℂ => aeval s (taylor 1 R)) = fun s : ℂ => (fun s : ℂ => aeval s R) (s + 1) :=
    funext fun s => by rw [taylor_apply, aeval_comp, map_add, aeval_X, aeval_C, map_one]
  obtain ⟨C, -, hC⟩ := poly_bound R (1 / 2 + |((-(η : ℤ) : ℤ) : ℝ)|)
  have hb : ∀ s : ℂ, |s.re - ((-(η : ℤ) : ℤ) : ℝ)| ≤ 1 / 2 →
      ‖aeval s R‖ ≤ C * (1 + |s.im|) ^ R.natDegree := fun s hs =>
    hC s (sub_le_iff_le_add.1 ((abs_sub_abs_le_abs_sub _ _).trans hs))
  have hn : (((-(η : ℤ) : ℤ)) : ℂ) = algebraMap ℚ ℂ (-(η : ℚ)) := by
    rw [eq_ratCast, Rat.cast_neg, Rat.cast_natCast, Int.cast_neg, Int.cast_natCast]
  have hs : (fun s : ℂ => aeval s (taylor 1 R - R)) =
      fun s => (fun s : ℂ => aeval s (taylor 1 R)) s - (fun s : ℂ => aeval s R) s :=
    funext fun s => map_sub _ _ _
  have e1 := barnesAt_sub ((((-(η : ℤ) - 1 : ℤ)) : ℝ) + 1 / 2) (fun s : ℂ => aeval s (taylor 1 R))
    (fun s : ℂ => aeval s R) (integrable_half_poly (-(η : ℤ) - 1) (taylor 1 R))
    (integrable_half_poly (-(η : ℤ) - 1) R)
  have e2 := barnes_translate ((((-(η : ℤ) - 1 : ℤ)) : ℝ) + 1 / 2) (fun s : ℂ => aeval s R)
  have e3 := barnes_step (-(η : ℤ)) (fun s : ℂ => aeval s R)
    (Polynomial.differentiable_aeval R).differentiableOn C R.natDegree hb
  rw [← ht, hc2] at e2
  rw [← hs] at e1
  rw [barnesI_eq, hc0, e1, e2, hc1, e3, Polynomial.deriv_aeval, hn,
    aeval_algebraMap_apply_eq_algebraMap_eval, eq_ratCast]

theorem delta_mem_range (n : ℕ) :
    (X : ℚ[X]) ^ n ∈ LinearMap.range ((taylor (1 : ℚ)) - LinearMap.id) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  set D : ℚ[X] →ₗ[ℚ] ℚ[X] := (taylor (1 : ℚ)) - LinearMap.id with hD
  have hS : ∑ i ∈ range n, X ^ i * 1 ^ (n + 1 - i) * (((n + 1).choose i : ℕ) : ℚ[X]) ∈
      LinearMap.range D := by
    refine Submodule.sum_mem _ fun i hi => ?_
    rw [one_pow, mul_one, mul_comm, ← nsmul_eq_mul]
    exact Submodule.smul_of_tower_mem _ _ (ih i (mem_range.1 hi))
  have hE : X ^ n = ((n : ℚ) + 1)⁻¹ • (D (X ^ (n + 1)) -
      ∑ i ∈ range n, X ^ i * 1 ^ (n + 1 - i) * (((n + 1).choose i : ℕ) : ℚ[X])) := by
    rw [hD, LinearMap.sub_apply, taylor_X_pow, LinearMap.id_apply, C_1, add_pow, sum_range_succ,
      sum_range_succ, Nat.choose_succ_self_right, Nat.choose_self, Nat.sub_self, pow_zero,
      mul_one, Nat.cast_one, mul_one, add_sub_cancel_right, add_sub_cancel_left,
      show n + 1 - n = 1 by omega, pow_one, mul_one, smul_eq_C_mul, ← C_eq_natCast, mul_comm,
      mul_assoc, ← C_mul, Nat.cast_succ, mul_inv_cancel₀ (Nat.cast_add_one_ne_zero n), C_1,
      mul_one]
  rw [hE]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (LinearMap.mem_range_self D _) hS)

/-- **Lemma 5 (the forward difference is onto `ℚ[X]`).** Every polynomial is `P(X+1) - P(X)`.

* Estimated length: 30 lines (strong induction on the degree; the leading coefficient of
  `Δ X^{n+1}` is `n+1`).
* Formalizable directly from the pdf: yes ("the forward-difference map on polynomials is onto"). -/
theorem delta_surj (Q : ℚ[X]) : ∃ R : ℚ[X], taylor 1 R - R = Q := by
  have hQ : Q ∈ LinearMap.range ((taylor (1 : ℚ)) - LinearMap.id) := by
    rw [Q.as_sum_range_C_mul_X_pow]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (delta_mem_range i)
  obtain ⟨R, hR⟩ := hQ
  exact ⟨R, by rw [← hR, LinearMap.sub_apply, LinearMap.id_apply]⟩

/-- **Lemma 6 (residue of `K(s)/(s-j)` at an integer `n ≠ j`).** It equals
`d/ds (s-j)⁻¹ |_{s=n} = -(n-j)⁻²`.

* Estimated length: 25 lines (Lemma 3 with `g = (s-j)⁻¹`, which is holomorphic on
  `|Re s - n| < 3/4` and bounded by `2` on `|Re s - n| ≤ 1/2`; derivative of the inverse).
* Formalizable directly from the pdf: yes, given Lemma 3. -/
theorem barnes_step_resolvent (n : ℤ) (j : ℕ) (h : n ≠ j) :
    barnesAt (n + 1 / 2) (fun s => 1 / (s - j)) - barnesAt (n - 1 / 2) (fun s => 1 / (s - j)) =
      -1 / ((n : ℂ) - j) ^ 2 := by
  have h1 : (1 : ℝ) ≤ |(n : ℝ) - (j : ℝ)| := by
    have h2 := Int.one_le_abs (sub_ne_zero.2 h)
    rw [← Int.cast_natCast j, ← Int.cast_sub, ← Int.cast_abs]
    exact_mod_cast h2
  have hne : ∀ s : ℂ, |s.re - n| < 3 / 4 → s - j ≠ 0 := fun s hs h0 => by
    have h3 : s.re = j := by
      rw [← Complex.natCast_re j, ← sub_eq_zero, ← Complex.sub_re, h0, Complex.zero_re]
    rw [h3, abs_sub_comm] at hs
    linarith
  have hd : DifferentiableOn ℂ (fun s : ℂ => 1 / (s - j)) {s | |s.re - n| < 3 / 4} :=
    fun s hs => (show DifferentiableAt ℂ (fun s : ℂ => 1 / (s - j)) s from
      (differentiableAt_const _).div (differentiableAt_id.sub_const _)
        (hne s hs)).differentiableWithinAt
  have hb : ∀ s : ℂ, |s.re - n| ≤ 1 / 2 → ‖1 / (s - j)‖ ≤ 2 * (1 + |s.im|) ^ 0 := by
    intro s hs
    have h4 : 1 / 2 ≤ ‖s - j‖ := by
      have h5 := Complex.abs_re_le_norm (s - j)
      rw [Complex.sub_re, Complex.natCast_re] at h5
      have h6 := abs_sub_le (n : ℝ) s.re j
      rw [abs_sub_comm (n : ℝ) s.re] at h6
      linarith
    rw [pow_zero, mul_one, norm_div, norm_one, div_le_iff₀ (by linarith)]
    linarith
  have hderiv : HasDerivAt (fun s : ℂ => 1 / (s - j)) (-1 / ((n : ℂ) - j) ^ 2) n := by
    have h7 := ((hasDerivAt_id' (n : ℂ)).sub_const (j : ℂ)).inv
      (hne n (by rw [Complex.intCast_re, sub_self, abs_zero]; exact div_pos three_pos four_pos))
    have hfun : (fun s : ℂ => 1 / (s - j)) = fun s : ℂ => (s - j)⁻¹ :=
      funext fun s => one_div _
    rw [hfun]
    exact h7
  rw [barnes_step n _ hd 2 0 hb, hderiv.deriv]

theorem pole_kernel_le (m : ℤ) (y : ℝ) :
    ‖((π : ℂ) / Complex.sin ((π : ℂ) * lineAt ((m : ℝ) + 1 / 2) y)) ^ 2‖ ≤
      π ^ 2 * (2 * exp 1 * ((1 : ℕ).factorial : ℝ)) ^ 2 * (1 + y ^ 2)⁻¹ := by
  have hK := half_kernel_le m 1 y
  have hy : 1 + y ^ 2 ≤ ((1 + |y|) ^ 1) ^ 2 := by
    rw [pow_one, add_sq, one_pow, mul_one, sq_abs]
    exact add_le_add (le_add_of_nonneg_right (mul_nonneg zero_le_two (abs_nonneg y))) (le_refl _)
  rw [← div_eq_mul_inv, le_div_iff₀ (add_pos_of_pos_of_nonneg one_pos (sq_nonneg y))]
  exact (mul_le_mul_of_nonneg_left hy (norm_nonneg _)).trans hK

theorem pole_resolvent_le (j : ℕ) (m : ℤ) (t y : ℝ) (ht : 0 < t)
    (hm : t ≤ |(m : ℝ) + 1 / 2 - j|) : ‖1 / (lineAt ((m : ℝ) + 1 / 2) y - j)‖ ≤ t⁻¹ := by
  rw [norm_div, norm_one, one_div]
  apply inv_anti₀ ht
  have h2 := Complex.abs_re_le_norm (lineAt ((m : ℝ) + 1 / 2) y - j)
  rw [Complex.sub_re, lineAt_re, Complex.natCast_re] at h2
  exact hm.trans h2

theorem pole_barnes_le (j : ℕ) (m : ℤ) (t : ℝ) (ht : 0 < t)
    (hm : t ≤ |(m : ℝ) + 1 / 2 - j|) :
    ‖barnesAt ((m : ℝ) + 1 / 2) (fun s => 1 / (s - j))‖ ≤
      ‖(1 / (2 * π) : ℂ)‖ * (π ^ 2 * (2 * exp 1 * ((1 : ℕ).factorial : ℝ)) ^ 2 * π) * t⁻¹ := by
  set D := π ^ 2 * (2 * exp 1 * ((1 : ℕ).factorial : ℝ)) ^ 2 with hD
  have hD0 : 0 ≤ D := mul_nonneg (sq_nonneg π) (sq_nonneg _)
  rw [mul_assoc ‖(1 / (2 * π) : ℂ)‖]
  unfold barnesAt
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hint : ∫ y : ℝ, D * t⁻¹ * (1 + y ^ 2)⁻¹ = D * π * t⁻¹ := by
    rw [integral_const_mul, integral_univ_inv_one_add_sq, mul_right_comm]
  rw [← hint]
  refine norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul _)
    (Eventually.of_forall fun y => ?_)
  rw [norm_mul, mul_right_comm D]
  exact mul_le_mul (pole_kernel_le m y) (pole_resolvent_le j m t y ht hm) (norm_nonneg _)
    (mul_nonneg hD0 (inv_nonneg.2 (add_nonneg zero_le_one (sq_nonneg y))))

theorem pole_tendsto_zero (u : ℕ → ℂ) (B : ℝ) (hu : ∀ n : ℕ, ‖u n‖ ≤ B * ((n : ℝ) + 1 / 2)⁻¹) :
    Tendsto u atTop (𝓝 0) := by
  refine squeeze_zero_norm hu ?_
  have h3 := (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (1 / 2 : ℝ)
    tendsto_natCast_atTop_atTop)).const_mul B
  rw [mul_zero] at h3
  exact h3

theorem pole_telescope (u f : ℕ → ℂ) (S : ℂ) (hf : HasSum f S)
    (h : ∀ n : ℕ, u n - u (n + 1) = f n) (hu : Tendsto u atTop (𝓝 0)) : u 0 = S := by
  have h1 := hf.tendsto_sum_nat
  have h2 : (fun N : ℕ => ∑ i ∈ range N, f i) = fun N => u 0 - u N :=
    funext fun N => by rw [← sum_range_sub' u N]; exact sum_congr rfl fun i _ => (h i).symm
  rw [h2] at h1
  have h3 := (tendsto_const_nhds (x := u 0)).sub hu
  rw [sub_zero] at h3
  exact tendsto_nhds_unique h3 h1

theorem pole_zeta_sum : HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ 2) ((π : ℂ) ^ 2 / 6) := by
  have h2 := (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
  rw [sum_range_one, Nat.cast_zero, zero_pow two_ne_zero, div_zero, sub_zero] at h2
  have h3 := Complex.ofRealCLM.hasSum h2
  have h4 : (fun n : ℕ => Complex.ofRealCLM (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) =
      fun n : ℕ => 1 / ((n : ℂ) + 1) ^ 2 := funext fun n => by
    rw [Complex.ofRealCLM_apply, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow,
      Complex.ofReal_natCast, Nat.cast_succ]
  rw [h4, Complex.ofRealCLM_apply, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_ofNat] at h3
  exact h3

theorem pole_line_step (j : ℕ) (m : ℤ) (hm : m ≠ j) :
    barnesAt (((m - 1 : ℤ) : ℝ) + 1 / 2) (fun s => 1 / (s - j)) -
      barnesAt ((m : ℝ) + 1 / 2) (fun s => 1 / (s - j)) = 1 / ((m : ℂ) - j) ^ 2 := by
  have e : (((m - 1 : ℤ)) : ℝ) + 1 / 2 = (m : ℝ) - 1 / 2 := by
    rw [Int.cast_sub, Int.cast_one]; ring
  rw [e, ← neg_sub, barnes_step_resolvent m j hm, neg_div, neg_neg]

/-- **Lemma 7 (residue of `K(s)/(s-j)` at `s = j`).** It is the constant term `π²/3 = 2ζ(2)` of
the Laurent expansion of `K` at `j`.

* Estimated length: 120 lines (as Lemma 3, now subtracting the principal part
  `(s-j)⁻³ + (π²/3)(s-j)⁻¹`; the expansion `π/sin πz = z⁻¹ + π² z/6 + O(z³)`).
* Formalizable directly from the pdf: partially (the pdf states the residue value only). -/
theorem barnes_step_pole (j : ℕ) :
    barnesAt ((j : ℤ) + 1 / 2) (fun s => 1 / (s - j)) -
        barnesAt ((j : ℤ) - 1 / 2) (fun s => 1 / (s - j)) = (π : ℂ) ^ 2 / 3 := by
  set B := ‖(1 / (2 * π) : ℂ)‖ * (π ^ 2 * (2 * exp 1 * ((1 : ℕ).factorial : ℝ)) ^ 2 * π)
  have htp : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 / 2 := fun n =>
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) one_half_pos
  have hr := pole_telescope (fun n : ℕ => barnesAt ((((j : ℤ) + n : ℤ) : ℝ) + 1 / 2)
    (fun s => 1 / (s - j))) _ _ pole_zeta_sum (fun n => by
      have h := pole_line_step j ((j : ℤ) + ((n + 1 : ℕ) : ℤ)) (by omega)
      rw [show (j : ℤ) + ((n + 1 : ℕ) : ℤ) - 1 = (j : ℤ) + n by omega,
        show (((j : ℤ) + ((n + 1 : ℕ) : ℤ) : ℤ) : ℂ) - j = (n : ℂ) + 1 by push_cast; ring] at h
      exact h)
    (pole_tendsto_zero _ B fun n => pole_barnes_le j _ _ (htp n) (by
      rw [show (((j : ℤ) + n : ℤ) : ℝ) + 1 / 2 - j = (n : ℝ) + 1 / 2 by push_cast; ring]
      exact le_abs_self _))
  have hl := pole_telescope (fun n : ℕ => barnesAt ((((j : ℤ) - 1 - n : ℤ) : ℝ) + 1 / 2)
    (fun s => 1 / (s - j))) _ _ pole_zeta_sum.neg (fun n => by
      have h := pole_line_step j ((j : ℤ) - 1 - n) (by omega)
      rw [show (j : ℤ) - 1 - n - 1 = (j : ℤ) - 1 - ((n + 1 : ℕ) : ℤ) by omega,
        show (((j : ℤ) - 1 - n : ℤ) : ℂ) - j = -((n : ℂ) + 1) by push_cast; ring, neg_sq] at h
      rw [← h, neg_sub])
    (pole_tendsto_zero _ B fun n => pole_barnes_le j _ _ (htp n) (by
      rw [show (((j : ℤ) - 1 - n : ℤ) : ℝ) + 1 / 2 - j = -((n : ℝ) + 1 / 2) by push_cast; ring,
        abs_neg]
      exact le_abs_self _))
  have e1 : (((j : ℤ) + ((0 : ℕ) : ℤ) : ℤ) : ℝ) + 1 / 2 = ((j : ℤ) : ℝ) + 1 / 2 := by
    rw [Nat.cast_zero, add_zero]
  have e2 : (((j : ℤ) - 1 - ((0 : ℕ) : ℤ) : ℤ) : ℝ) + 1 / 2 = ((j : ℤ) : ℝ) - 1 / 2 := by
    push_cast; ring
  simp only [e1, e2] at hr hl
  rw [hr, hl]
  ring

theorem sq_le_sinh_sq (t : ℝ) : t ^ 2 ≤ Real.sinh t ^ 2 := by
  rw [← sq_abs t, ← sq_abs (Real.sinh t), Real.abs_sinh]
  exact pow_le_pow_left₀ (abs_nonneg t) (Real.self_le_sinh_iff.2 (abs_nonneg t)) 2

theorem kernel_le (x y : ℝ) (hx : Real.sin (π * x) ≠ 0) :
    ‖((π : ℂ) / Complex.sin ((π : ℂ) * lineAt x y)) ^ 2‖ ≤
      π ^ 2 / min (Real.sin (π * x) ^ 2) (π ^ 2) * (1 + y ^ 2)⁻¹ := by
  have hm : 0 < min (Real.sin (π * x) ^ 2) (π ^ 2) :=
    lt_min (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hx))) (pow_pos pi_pos 2)
  have h1 : min (Real.sin (π * x) ^ 2) (π ^ 2) * (1 + y ^ 2) ≤
      Real.sin (π * x) ^ 2 + Real.sinh (π * y) ^ 2 := by
    calc min (Real.sin (π * x) ^ 2) (π ^ 2) * (1 + y ^ 2)
        = min (Real.sin (π * x) ^ 2) (π ^ 2) + min (Real.sin (π * x) ^ 2) (π ^ 2) * y ^ 2 := by
          rw [mul_add, mul_one]
      _ ≤ Real.sin (π * x) ^ 2 + π ^ 2 * y ^ 2 := add_le_add (min_le_left _ _)
          (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg y))
      _ ≤ Real.sin (π * x) ^ 2 + Real.sinh (π * y) ^ 2 := by
          rw [← mul_pow]
          exact add_le_add (le_refl _) (sq_le_sinh_sq _)
  rw [kernel_norm, ← div_eq_mul_inv, div_div]
  exact div_le_div_of_nonneg_left (sq_nonneg π) (mul_pos hm (by positivity)) h1

/-- **Lemma 8 (the distant right edge).** For a line avoiding the integers, the integral of
`K(s)/(s-j)` over `Re s = c + n` tends to `0` as `n → ∞`: `∫ |K|` over these lines is constant by
periodicity and `|1/(s-j)| ≤ 1/(c+n-j) → 0`.

* Estimated length: 40 lines (dominated bound, `tendsto_inv_atTop_zero`).
* Formalizable directly from the pdf: yes ("the integral on the distant right edge tends to
  zero"). -/
theorem barnes_vanish_right (c : ℝ) (hc : ∀ m : ℤ, c ≠ m) (j : ℕ) :
    Tendsto (fun n : ℕ => barnesAt (c + n) (fun s => 1 / (s - j))) atTop (𝓝 0) := by
  have hs : Real.sin (π * c) ≠ 0 := fun h => by
    obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.1 h
    exact hc m (mul_left_cancel₀ pi_ne_zero (hm.symm.trans (mul_comm _ _)))
  have hsn : ∀ n : ℕ, Real.sin (π * (c + n)) ^ 2 = Real.sin (π * c) ^ 2 := fun n => by
    rw [mul_add, mul_comm π (n : ℝ), Real.sin_add_nat_mul_pi, mul_pow, ← pow_mul, mul_comm n 2,
      pow_mul, neg_one_sq, one_pow, one_mul]
  set B := π ^ 2 / min (Real.sin (π * c) ^ 2) (π ^ 2)
  have key : ∀ n : ℕ, (j : ℝ) - c + 1 ≤ n → ‖barnesAt (c + n) (fun s => 1 / (s - j))‖ ≤
      ‖(1 / (2 * π) : ℂ)‖ * (B * π) * (c - j + n)⁻¹ := by
    intro n hn
    have hpos : 0 < c - j + n := by linarith
    have hsn0 : Real.sin (π * (c + n)) ≠ 0 := fun h =>
      hs ((pow_eq_zero_iff two_ne_zero).1 ((hsn n).symm.trans (by rw [h, zero_pow two_ne_zero])))
    unfold barnesAt
    rw [norm_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hint : ∫ y : ℝ, B * (c - j + n)⁻¹ * (1 + y ^ 2)⁻¹ = B * π * (c - j + n)⁻¹ := by
      rw [integral_const_mul, integral_univ_inv_one_add_sq, mul_right_comm]
    rw [← hint]
    refine norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul _)
      (Eventually.of_forall fun y => ?_)
    rw [norm_mul]
    have hk := kernel_le (c + n) y hsn0
    rw [hsn n] at hk
    have hr : ‖1 / (lineAt (c + n) y - j)‖ ≤ (c - j + n)⁻¹ := by
      rw [norm_div, norm_one, one_div]
      apply inv_anti₀ hpos
      have h2 := Complex.re_le_norm (lineAt (c + n) y - j)
      rw [Complex.sub_re, lineAt_re, Complex.natCast_re] at h2
      linarith
    calc ‖((π : ℂ) / Complex.sin ((π : ℂ) * lineAt (c + n) y)) ^ 2‖ *
          ‖1 / (lineAt (c + n) y - j)‖ ≤ B * (1 + y ^ 2)⁻¹ * (c - j + n)⁻¹ :=
          mul_le_mul hk hr (norm_nonneg _) (by positivity)
      _ = B * (c - j + n)⁻¹ * (1 + y ^ 2)⁻¹ := mul_right_comm _ _ _
  refine squeeze_zero_norm' ((tendsto_natCast_atTop_atTop.eventually_ge_atTop
    ((j : ℝ) - c + 1)).mono key) ?_
  have h3 := (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop (c - j)
    tendsto_natCast_atTop_atTop)).const_mul (‖(1 / (2 * π) : ℂ)‖ * (B * π))
  rw [mul_zero] at h3
  exact h3

/-- **Lemma 9 (the residue sum).** Indexing the poles right of the line `Re s = -η - 1/2` by
`s = n - η`, `n ∈ ℕ`:
`∑_{n ≠ j+η} (n - (j+η))⁻² = H^{(2)}_{j+η} + π²/6`
(the terms `n < j+η` give `H^{(2)}_{j+η}`, the terms `n > j+η` give `ζ(2) = π²/6`).

* Estimated length: 40 lines (`hasSum_zeta_two`, `hasSum_nat_add_iff'`, reindexing a finite
  part).
* Formalizable directly from the pdf: yes. -/
theorem resolvent_hasSum (j η : ℕ) :
    HasSum (fun n : ℕ => if n = j + η then (0 : ℝ) else 1 / ((n : ℝ) - (j + η : ℕ)) ^ 2)
      (harm2 (j + η) + π ^ 2 / 6) := by
  set k := j + η
  set f := fun n : ℕ => if n = k then (0 : ℝ) else 1 / ((n : ℝ) - (k : ℕ)) ^ 2 with hf
  have h1 : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
    have h2 := (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
    rw [sum_range_one, Nat.cast_zero, zero_pow two_ne_zero, div_zero, sub_zero] at h2
    simpa only [Nat.cast_add, Nat.cast_one] using h2
  have h2 : (fun n : ℕ => f (n + (k + 1))) = fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 :=
    funext fun n => by
      simp only [hf]
      rw [ite_eq_right (by omega), Nat.cast_add, Nat.cast_add, Nat.cast_one]
      ring
  have h4 : ∀ i ∈ range k, f (k - 1 - i) = 1 / ((i : ℝ) + 1) ^ 2 := fun i hi => by
    have hi' := mem_range.1 hi
    simp only [hf]
    rw [ite_eq_right (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
    ring
  have h5 : ∑ m ∈ Icc 1 k, 1 / (m : ℝ) ^ 2 = ∑ i ∈ range k, 1 / ((i : ℝ) + 1) ^ 2 := by
    rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    refine sum_congr rfl fun i _ => ?_
    rw [Nat.cast_add, Nat.cast_one, add_comm]
  have hfk : f k = 0 := ite_eq_left rfl
  have h3 : ∑ i ∈ range (k + 1), f i = (harm2 k : ℝ) := by
    rw [sum_range_succ, ← sum_range_reflect, sum_congr rfl h4, hfk, add_zero, harm2, ← h5]
    push_cast
    rfl
  rw [← hasSum_nat_add_iff' (k + 1), h2, h3, add_sub_cancel_left]
  exact h1

/-- **The Barnes integral (§6.1)** — restatement of `Zeta2Blueprint.barnes_identities`,
proved from Lemmas 1–9. -/
theorem barnes_identities (η : ℕ) :
    (∀ P : ℚ[X], barnesI η (fun s => aeval s P) = (Jfun η P : ℂ)) ∧
      ∀ j : ℕ, barnesI η (fun s => 1 / (s - j)) = (harm2 (j + η) : ℂ) - (zeta2 : ℂ) := by
  refine ⟨fun P => ?_, fun j => ?_⟩
  · obtain ⟨R, rfl⟩ := delta_surj P
    rw [barnes_poly_delta, Zeta2FirstThree.J_delta]
  · set g : ℂ → ℂ := fun s => 1 / (s - j) with hg
    set c : ℕ → ℂ := fun n => barnesAt (-(η : ℝ) - 1 / 2 + n) g with hc
    -- the jump of `c` across the pole `n - η`
    set k : ℕ := j + η with hk
    have hstep : ∀ n : ℕ, c (n + 1) - c n =
        (if n = k then (π : ℂ) ^ 2 / 3 else 0) -
          (((if n = k then (0 : ℝ) else 1 / ((n : ℝ) - (k : ℕ)) ^ 2) : ℝ) : ℂ) := by
      intro n
      have e1 : -(η : ℝ) - 1 / 2 + ((n + 1 : ℕ) : ℝ) = (((n : ℤ) - η : ℤ) : ℝ) + 1 / 2 := by
        push_cast; ring
      have e2 : -(η : ℝ) - 1 / 2 + (n : ℝ) = (((n : ℤ) - η : ℤ) : ℝ) - 1 / 2 := by
        push_cast; ring
      simp only [hc, e1, e2]
      by_cases hn : n = k
      · have hj : ((n : ℤ) - η : ℤ) = ((j : ℕ) : ℤ) := by omega
        rw [hj, barnes_step_pole j]
        simp [hn]
      · have hj : ((n : ℤ) - η : ℤ) ≠ ((j : ℕ) : ℤ) := by omega
        rw [barnes_step_resolvent _ j hj]
        rw [ite_eq_right hn, ite_eq_right hn, zero_sub, hk]
        push_cast
        ring
    have hsum : HasSum (fun n : ℕ => c (n + 1) - c n)
        ((π : ℂ) ^ 2 / 3 - (((harm2 k + π ^ 2 / 6 : ℝ)) : ℂ)) := by
      simp only [hstep]
      refine (hasSum_ite_eq k _).sub ?_
      exact (Complex.ofRealCLM.hasSum (resolvent_hasSum j η))
    have hlim1 : Tendsto (fun N : ℕ => c N - c 0) atTop
        (𝓝 ((π : ℂ) ^ 2 / 3 - (((harm2 k + π ^ 2 / 6 : ℝ)) : ℂ))) := by
      have := hsum.tendsto_sum_nat
      simp only [sum_range_sub (fun n => c n)] at this
      exact this
    have hlim2 : Tendsto (fun N : ℕ => c N - c 0) atTop (𝓝 (0 - c 0)) :=
      (barnes_vanish_right (-(η : ℝ) - 1 / 2) (fun m h => by
        have h2 : (2 : ℝ) * (-(η : ℝ) - 1 / 2) = 2 * m := by rw [h]
        have h3 : ((-2 * (η : ℤ) - 1 : ℤ) : ℝ) = ((2 * m : ℤ) : ℝ) := by push_cast; linarith
        have h4 := Int.cast_inj.1 h3
        omega) j).sub tendsto_const_nhds
    have heq := tendsto_nhds_unique hlim2 hlim1
    have hz : (zeta2 : ℂ) = (π : ℂ) ^ 2 / 6 := by
      have h := riemannZeta_two
      rw [zeta2, h]
      rw [show (π : ℂ) ^ 2 / 6 = ((π ^ 2 / 6 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
    have hc0 : barnesI η g = c 0 := by
      rw [barnesI_eq]
      simp only [hc, Nat.cast_zero, add_zero]
    rw [hc0, hz]
    push_cast at heq ⊢
    linear_combination -heq

end Zeta2BarnesIdentities
