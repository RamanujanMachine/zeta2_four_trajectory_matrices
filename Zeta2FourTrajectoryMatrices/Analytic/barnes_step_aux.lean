import Zeta2FourTrajectoryMatrices.FiniteReadout.blueprint_first_three

open Polynomial Filter Topology Real Finset MeasureTheory Zeta2Blueprint

noncomputable section

namespace Zeta2BarnesStep

def lineB (c : ℝ) (y : ℝ) : ℂ := (c : ℂ) + y * Complex.I

def kerK (s : ℂ) : ℂ := ((π : ℂ) / Complex.sin ((π : ℂ) * s)) ^ 2

def sinS (n : ℤ) : ℂ → ℂ := dslope (fun s : ℂ => Complex.sin ((π : ℂ) * s)) n

def regF (n : ℤ) (g : ℂ → ℂ) (s : ℂ) : ℂ :=
  ((π : ℂ) / sinS n s) ^ 2 * dslope (dslope g n) n s

def chK (y : ℝ) : ℝ := π ^ 2 / Real.cosh (π * y) ^ 2

def stripO (n : ℤ) : Set ℂ := {s | |s.re - n| < 3 / 4}

theorem lineB_re (c y : ℝ) : (lineB c y).re = c := by
  simp only [lineB, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

theorem lineB_im (c y : ℝ) : (lineB c y).im = y := by
  simp only [lineB, Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]

theorem continuous_lineB (c : ℝ) : Continuous (lineB c) :=
  continuous_const.add (Complex.continuous_ofReal.mul continuous_const)

theorem sinB_normSq (x y : ℝ) :
    Complex.normSq (Complex.sin ((π : ℂ) * lineB x y)) =
      Real.sin (π * x) ^ 2 + Real.sinh (π * y) ^ 2 := by
  have h : (π : ℂ) * lineB x y = ((π * x : ℝ) : ℂ) + ((π * y : ℝ) : ℂ) * Complex.I := by
    rw [lineB, Complex.ofReal_mul, Complex.ofReal_mul, mul_add, mul_assoc]
  rw [h, Complex.sin_add_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_cos,
    ← Complex.ofReal_sinh, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.normSq_add_mul_I,
    mul_pow, mul_pow, Real.cosh_sq, Real.cos_sq']
  ring

theorem kerK_norm (x y : ℝ) :
    ‖kerK (lineB x y)‖ = π ^ 2 / (Real.sin (π * x) ^ 2 + Real.sinh (π * y) ^ 2) := by
  rw [kerK, norm_pow, norm_div, Complex.norm_real, Real.norm_of_nonneg pi_pos.le, div_pow,
    Complex.sq_norm (Complex.sin _), sinB_normSq]

theorem exp_abs_le_cosh2 (y : ℝ) : exp |y| ≤ 2 * Real.cosh (π * y) := by
  have h1 : |y| ≤ |π * y| := by
    rw [abs_mul, abs_of_pos pi_pos]
    exact le_mul_of_one_le_left (abs_nonneg y) (one_le_two.trans Real.two_le_pi)
  have h2 : exp |π * y| ≤ exp (π * y) + exp (-(π * y)) := by
    rcases abs_choice (π * y) with h | h <;> rw [h]
    · exact le_add_of_nonneg_right (exp_pos _).le
    · exact le_add_of_nonneg_left (exp_pos _).le
  rw [Real.cosh_eq, mul_div_cancel₀ _ two_ne_zero]
  exact (exp_le_exp.2 h1).trans h2

theorem sq_le_sinh_sq2 (t : ℝ) : t ^ 2 ≤ Real.sinh t ^ 2 := by
  rw [← sq_abs t, ← sq_abs (Real.sinh t), Real.abs_sinh]
  exact pow_le_pow_left₀ (abs_nonneg t) (Real.self_le_sinh_iff.2 (abs_nonneg t)) 2

theorem pow_le_cosh2 (k : ℕ) (y : ℝ) :
    (1 + |y|) ^ k ≤ 2 * exp 1 * (k.factorial : ℝ) * Real.cosh (π * y) := by
  have h2 := Real.pow_div_factorial_le_exp (1 + |y|) (add_nonneg zero_le_one (abs_nonneg y)) k
  rw [div_le_iff₀ (Nat.cast_pos.2 (Nat.factorial_pos k) : (0 : ℝ) < k.factorial), exp_add] at h2
  calc (1 + |y|) ^ k ≤ exp 1 * exp |y| * (k.factorial : ℝ) := h2
    _ ≤ exp 1 * (2 * Real.cosh (π * y)) * (k.factorial : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (exp_abs_le_cosh2 y)
          (exp_pos 1).le) (Nat.cast_nonneg _)
    _ = 2 * exp 1 * (k.factorial : ℝ) * Real.cosh (π * y) := by ring

theorem kerK_cosh_le (x y : ℝ) (hy : 1 ≤ |y|) :
    ‖kerK (lineB x y)‖ * Real.cosh (π * y) ^ 2 ≤ 2 * π ^ 2 := by
  have h1 : 1 ≤ Real.sinh (π * y) ^ 2 := by
    have hp : (1 : ℝ) ≤ π ^ 2 := (one_le_sq_iff_one_le_abs π).2
      (by rw [abs_of_pos pi_pos]; exact one_le_two.trans Real.two_le_pi)
    have hy2 : (1 : ℝ) ≤ y ^ 2 := (one_le_sq_iff_one_le_abs y).2 hy
    have h3 : (1 : ℝ) ≤ (π * y) ^ 2 := by
      rw [mul_pow]; exact one_le_mul_of_one_le_of_one_le hp hy2
    exact h3.trans (sq_le_sinh_sq2 _)
  have h2 : Real.cosh (π * y) ^ 2 ≤ 2 * (Real.sin (π * x) ^ 2 + Real.sinh (π * y) ^ 2) := by
    rw [Real.cosh_sq]
    calc Real.sinh (π * y) ^ 2 + 1 ≤ Real.sinh (π * y) ^ 2 + Real.sinh (π * y) ^ 2 :=
          add_le_add le_rfl h1
      _ = 2 * Real.sinh (π * y) ^ 2 := (two_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (sq_nonneg _)) zero_le_two
  rw [kerK_norm, div_mul_eq_mul_div]
  refine div_le_of_le_mul₀ (add_nonneg (sq_nonneg _) (sq_nonneg _))
    (mul_nonneg zero_le_two (sq_nonneg π)) ?_
  calc π ^ 2 * Real.cosh (π * y) ^ 2
      ≤ π ^ 2 * (2 * (Real.sin (π * x) ^ 2 + Real.sinh (π * y) ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg π)
    _ = 2 * π ^ 2 * (Real.sin (π * x) ^ 2 + Real.sinh (π * y) ^ 2) := by ring

theorem sin_ne_zero_far (x y : ℝ) (hy : 1 ≤ |y|) : Complex.sin ((π : ℂ) * lineB x y) ≠ 0 :=
  fun h => by
    have h2 := sinB_normSq x y
    rw [h, map_zero] at h2
    have hy0 : y ≠ 0 := fun h0 => by
      rw [h0, abs_zero] at hy
      exact absurd hy (not_le.2 zero_lt_one)
    have h3 := sq_le_sinh_sq2 (π * y)
    have h4 : 0 < (π * y) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (mul_ne_zero pi_ne_zero hy0)))
    have h5 := sq_nonneg (Real.sin (π * x))
    linarith

theorem tanh_sub_one_le (t : ℝ) : ‖Real.sinh t / Real.cosh t - 1‖ ≤ exp (-t) := by
  have hc : 0 < Real.cosh t := Real.cosh_pos t
  have h : Real.sinh t / Real.cosh t - 1 = -(exp (-t) / Real.cosh t) := by
    rw [← Real.cosh_sub_sinh, sub_div, div_self hc.ne', neg_sub]
  rw [h, norm_neg, Real.norm_of_nonneg (div_nonneg (exp_pos _).le hc.le)]
  exact div_le_self (exp_pos _).le (Real.one_le_cosh t)

theorem tendsto_tanhB : Tendsto (fun t : ℝ => Real.sinh t / Real.cosh t) atTop (𝓝 1) :=
  tendsto_iff_norm_sub_tendsto_zero.2
    (squeeze_zero (fun _ => norm_nonneg _) tanh_sub_one_le Real.tendsto_exp_neg_atTop_nhds_zero)

theorem hasDerivAt_tanhB (y : ℝ) :
    HasDerivAt (fun y : ℝ => π * (Real.sinh (π * y) / Real.cosh (π * y))) (chK y) y := by
  have hl : HasDerivAt (fun y : ℝ => π * y) π y :=
    ((hasDerivAt_id y).const_mul π).congr_deriv (mul_one π)
  have h := ((Real.hasDerivAt_sinh (π * y)).comp y hl).div
    ((Real.hasDerivAt_cosh (π * y)).comp y hl) (Real.cosh_pos _).ne'
  refine (h.const_mul π).congr_deriv ?_
  simp only [Function.comp_apply]
  have e : Real.cosh (π * y) * π * Real.cosh (π * y) - Real.sinh (π * y) *
      (Real.sinh (π * y) * π) = π := by
    linear_combination π * Real.cosh_sq_sub_sinh_sq (π * y)
  rw [e, chK, mul_div_assoc', ← sq]

theorem continuous_chK : Continuous chK :=
  continuous_const.div ((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).pow 2)
    fun _ => pow_ne_zero 2 (Real.cosh_pos _).ne'

theorem chK_nonneg (y : ℝ) : 0 ≤ chK y := div_nonneg (sq_nonneg π) (sq_nonneg _)

theorem chK_weight (y : ℝ) :
    chK y * (1 + |y|) ≤ π ^ 2 * (2 * exp 1 * ((Nat.factorial 3 : ℕ) : ℝ)) * (1 + y ^ 2)⁻¹ := by
  have hc : 0 < Real.cosh (π * y) := Real.cosh_pos _
  have hp := pow_le_cosh2 3 y
  have hu : 0 ≤ 1 + |y| := add_nonneg zero_le_one (abs_nonneg y)
  have hy2 : 1 + y ^ 2 ≤ (1 + |y|) ^ 2 := by
    rw [add_sq, one_pow, mul_one, sq_abs]
    exact add_le_add (le_add_of_nonneg_right (mul_nonneg zero_le_two (abs_nonneg y))) le_rfl
  have hpos : 0 < 1 + y ^ 2 := add_pos_of_pos_of_nonneg one_pos (sq_nonneg y)
  have hE : 0 ≤ 2 * exp 1 * ((Nat.factorial 3 : ℕ) : ℝ) :=
    mul_nonneg (mul_nonneg zero_le_two (exp_pos 1).le) (Nat.cast_nonneg _)
  rw [le_mul_inv_iff₀ hpos, chK, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (pow_pos hc 2)]
  calc π ^ 2 * (1 + |y|) * (1 + y ^ 2) ≤ π ^ 2 * (1 + |y|) * (1 + |y|) ^ 2 :=
        mul_le_mul_of_nonneg_left hy2 (mul_nonneg (sq_nonneg π) hu)
    _ = π ^ 2 * (1 + |y|) ^ 3 := by ring
    _ ≤ π ^ 2 * (2 * exp 1 * ((Nat.factorial 3 : ℕ) : ℝ) * Real.cosh (π * y)) :=
        mul_le_mul_of_nonneg_left hp (sq_nonneg π)
    _ ≤ π ^ 2 * (2 * exp 1 * ((Nat.factorial 3 : ℕ) : ℝ) * Real.cosh (π * y) ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (le_self_pow₀ (Real.one_le_cosh _) two_ne_zero) hE) (sq_nonneg π)
    _ = _ := by ring

theorem integrable_chK : Integrable chK :=
  (integrable_inv_one_add_sq.const_mul (π ^ 2 * (2 * exp 1 * ((Nat.factorial 3 : ℕ) : ℝ)))).mono'
    continuous_chK.aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (chK_nonneg y)]
      exact (le_mul_of_one_le_right (chK_nonneg y)
        (le_add_of_nonneg_right (abs_nonneg y))).trans (chK_weight y))

theorem integral_chK : ∫ y, chK y = 2 * π := by
  have htop : Tendsto (fun y : ℝ => π * (Real.sinh (π * y) / Real.cosh (π * y))) atTop
      (𝓝 (π * 1)) :=
    (tendsto_tanhB.comp (Tendsto.const_mul_atTop pi_pos tendsto_id)).const_mul π
  have hbot : Tendsto (fun y : ℝ => π * (Real.sinh (π * y) / Real.cosh (π * y))) atBot
      (𝓝 (π * -1)) := by
    have h := ((tendsto_tanhB.comp
      (Tendsto.const_mul_atTop pi_pos tendsto_neg_atBot_atTop)).neg).const_mul π
    refine h.congr fun y => ?_
    simp only [Function.comp, mul_neg, Real.sinh_neg, Real.cosh_neg, neg_div, neg_neg]
  rw [integral_of_hasDerivAt_of_tendsto hasDerivAt_tanhB integrable_chK hbot htop]
  ring

theorem norm_lineB_sub (n : ℤ) (c : ℝ) (hc : |c - n| ≤ 1 / 2) (y : ℝ) :
    ‖lineB c y - n‖ ≤ 1 + |y| := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [Complex.sub_re, Complex.sub_im, lineB_re, lineB_im, Complex.intCast_re, Complex.intCast_im,
    sub_zero]
  exact add_le_add (hc.trans (by norm_num)) le_rfl

theorem integrable_chK_lin (n : ℤ) (c : ℝ) (hc : |c - n| ≤ 1 / 2) :
    Integrable (fun y : ℝ => (chK y : ℂ) * (lineB c y - n)) :=
  (integrable_inv_one_add_sq.const_mul (π ^ 2 * (2 * exp 1 * ((Nat.factorial 3 : ℕ) : ℝ)))).mono'
    ((Complex.continuous_ofReal.comp continuous_chK).mul
      ((continuous_lineB c).sub continuous_const)).aestronglyMeasurable
    (Eventually.of_forall fun y => by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (chK_nonneg y)]
      exact (mul_le_mul_of_nonneg_left (norm_lineB_sub n c hc y) (chK_nonneg y)).trans
        (chK_weight y))

theorem sin_half_line (c : ℝ) (hc : Real.cos (π * c) = 0) (y : ℝ) :
    Complex.sin ((π : ℂ) * lineB c y) = ((Real.sin (π * c) * Real.cosh (π * y) : ℝ) : ℂ) := by
  have h : (π : ℂ) * lineB c y = ((π * c : ℝ) : ℂ) + ((π * y : ℝ) : ℂ) * Complex.I := by
    rw [lineB, Complex.ofReal_mul, Complex.ofReal_mul, mul_add, mul_assoc]
  rw [h, Complex.sin_add_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_cos,
    hc, Complex.ofReal_zero, zero_mul, zero_mul, add_zero, Complex.ofReal_mul]

theorem sin_sq_half (c : ℝ) (hc : Real.cos (π * c) = 0) : Real.sin (π * c) ^ 2 = 1 := by
  have h2 := Real.sin_sq_add_cos_sq (π * c)
  rwa [hc, zero_pow two_ne_zero, add_zero] at h2

theorem sin_half_ne (c : ℝ) (hc : Real.cos (π * c) = 0) (y : ℝ) :
    Complex.sin ((π : ℂ) * lineB c y) ≠ 0 := by
  have hs : Real.sin (π * c) ≠ 0 := fun h => by
    have h2 := sin_sq_half c hc
    rw [h, zero_pow two_ne_zero] at h2
    exact zero_ne_one h2
  rw [sin_half_line c hc y]
  exact Complex.ofReal_ne_zero.2 (mul_ne_zero hs (Real.cosh_pos _).ne')

theorem kerK_half (c : ℝ) (hc : Real.cos (π * c) = 0) (y : ℝ) :
    kerK (lineB c y) = (chK y : ℂ) := by
  rw [kerK, sin_half_line c hc y, ← Complex.ofReal_div, ← Complex.ofReal_pow, div_pow, mul_pow,
    sin_sq_half c hc, one_mul, chK]

theorem sin_int_pi (n : ℤ) : Complex.sin ((π : ℂ) * n) = 0 := by
  rw [mul_comm]
  exact Complex.sin_int_mul_pi n

theorem sin_eq_sinS (n : ℤ) (s : ℂ) : Complex.sin ((π : ℂ) * s) = (s - n) * sinS n s := by
  have h := sub_smul_dslope (fun s : ℂ => Complex.sin ((π : ℂ) * s)) (n : ℂ) s
  simp only [smul_eq_mul, sin_int_pi, sub_zero] at h
  exact h.symm

theorem sinS_self_ne (n : ℤ) : sinS n n ≠ 0 := by
  have hd : HasDerivAt (fun s : ℂ => Complex.sin ((π : ℂ) * s))
      (Complex.cos ((π : ℂ) * n) * ((π : ℂ) * 1)) n :=
    (Complex.hasDerivAt_sin ((π : ℂ) * n)).comp (n : ℂ) ((hasDerivAt_id (n : ℂ)).const_mul (π : ℂ))
  have hc : Complex.cos ((π : ℂ) * n) ≠ 0 := fun h => by
    have h2 := Complex.sin_sq_add_cos_sq ((π : ℂ) * n)
    rw [h, sin_int_pi, zero_pow two_ne_zero, add_zero] at h2
    exact zero_ne_one h2
  rw [sinS, dslope_same, hd.deriv, mul_one]
  exact mul_ne_zero hc (Complex.ofReal_ne_zero.2 pi_ne_zero)

theorem int_eq_of_abs_lt (k n : ℤ) (h : |(k : ℝ) - n| < 3 / 4) : k = n := by
  have h1 : |((k - n : ℤ) : ℝ)| < 1 := by
    rw [Int.cast_sub]
    exact h.trans (by norm_num)
  rw [← Int.cast_abs, ← Int.cast_one, Int.cast_lt] at h1
  exact sub_eq_zero.1 (Int.abs_lt_one_iff.1 h1)

theorem sinS_ne_zero (n : ℤ) (s : ℂ) (hs : s ∈ stripO n) : sinS n s ≠ 0 := by
  by_cases h0 : s = n
  · rw [h0]
    exact sinS_self_ne n
  intro h
  have h1 := sin_eq_sinS n s
  rw [h, mul_zero] at h1
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.1 h1
  have hsk : s = k := by
    rw [mul_comm] at hk
    exact mul_right_cancel₀ (Complex.ofReal_ne_zero.2 pi_ne_zero) hk
  have hs2 : |(k : ℝ) - n| < 3 / 4 := by
    have h3 : |s.re - n| < 3 / 4 := hs
    rw [hsk, Complex.intCast_re] at h3
    exact h3
  exact h0 (by rw [hsk, int_eq_of_abs_lt k n hs2])

theorem stripO_mem_nhds (n : ℤ) : stripO n ∈ 𝓝 (n : ℂ) := by
  have ho : IsOpen (stripO n) :=
    isOpen_lt (continuous_abs.comp (Complex.continuous_re.sub continuous_const)) continuous_const
  refine ho.mem_nhds ?_
  change |(n : ℂ).re - n| < 3 / 4
  rw [Complex.intCast_re, sub_self, abs_zero]
  norm_num

theorem differentiableOn_regF (n : ℤ) (g : ℂ → ℂ) (hd : DifferentiableOn ℂ g (stripO n)) :
    DifferentiableOn ℂ (regF n g) (stripO n) := by
  have hm := stripO_mem_nhds n
  have hS : DifferentiableOn ℂ (sinS n) (stripO n) :=
    (Complex.differentiableOn_dslope hm).2
      (Complex.differentiable_sin.comp (differentiable_id.const_mul (π : ℂ))).differentiableOn
  have hq : DifferentiableOn ℂ (dslope (dslope g n) n) (stripO n) :=
    (Complex.differentiableOn_dslope hm).2 ((Complex.differentiableOn_dslope hm).2 hd)
  exact (((differentiableOn_const _).div hS fun s hs => sinS_ne_zero n s hs).pow 2).mul hq

theorem g_expand (n : ℤ) (g : ℂ → ℂ) (s : ℂ) :
    g s = g n + (s - n) * (deriv g n + (s - n) * dslope (dslope g n) n s) := by
  have h1 := sub_smul_dslope g (n : ℂ) s
  have h2 := sub_smul_dslope (dslope g n) (n : ℂ) s
  rw [dslope_same, smul_eq_mul] at h2
  rw [smul_eq_mul] at h1
  rw [h2, add_sub_cancel, h1, add_sub_cancel]

theorem kerK_decomp (n : ℤ) (g : ℂ → ℂ) (s : ℂ) (hs : Complex.sin ((π : ℂ) * s) ≠ 0) :
    kerK s * g s = g n * kerK s + deriv g n * (kerK s * (s - n)) + regF n g s := by
  have h1 := sin_eq_sinS n s
  rw [h1] at hs
  have hu : s - n ≠ 0 := left_ne_zero_of_mul hs
  have hv : sinS n s ≠ 0 := right_ne_zero_of_mul hs
  rw [kerK, regF, h1, g_expand n g s]
  field_simp
  ring

theorem regF_far (n : ℤ) (g : ℂ → ℂ) (s : ℂ) (hs : Complex.sin ((π : ℂ) * s) ≠ 0) :
    regF n g s = kerK s * (g s - g n - deriv g n * (s - n)) := by
  have h := kerK_decomp n g s hs
  linear_combination -h

theorem line_integral_decomp (n : ℤ) (g : ℂ → ℂ) (c : ℝ) (hc : Real.cos (π * c) = 0)
    (hc1 : |c - n| ≤ 1 / 2) (hF : Integrable (fun y : ℝ => regF n g (lineB c y))) :
    ∫ y, kerK (lineB c y) * g (lineB c y) = g n * (∫ y, (chK y : ℂ)) +
      deriv g n * (∫ y, (chK y : ℂ) * (lineB c y - n)) + ∫ y, regF n g (lineB c y) := by
  have hpt : (fun y => kerK (lineB c y) * g (lineB c y)) = fun y => g n * (chK y : ℂ) +
      deriv g n * ((chK y : ℂ) * (lineB c y - n)) + regF n g (lineB c y) := funext fun y => by
    rw [kerK_decomp n g _ (sin_half_ne c hc y), kerK_half c hc y]
  have h0 : Integrable (fun y : ℝ => (chK y : ℂ)) := integrable_chK.ofReal
  have h1 := integrable_chK_lin n c hc1
  have h01 : Integrable (fun y : ℝ =>
      g n * (chK y : ℂ) + deriv g n * ((chK y : ℂ) * (lineB c y - n))) :=
    (h0.const_mul _).add (h1.const_mul _)
  rw [hpt, integral_add h01 hF,
    integral_add (h0.const_mul _) (h1.const_mul _), integral_const_mul, integral_const_mul]

end Zeta2BarnesStep
