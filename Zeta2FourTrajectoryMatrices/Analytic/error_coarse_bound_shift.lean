import Zeta2FourTrajectoryMatrices.Analytic.error_integral

open Polynomial Filter Topology Real Finset MeasureTheory Zeta2Blueprint Zeta2BarnesIdentities

noncomputable section

namespace Zeta2ECBShift

def kerG (N r : ℕ) (s : ℂ) : ℂ :=
  ((π : ℂ) / Complex.sin ((π : ℂ) * s)) ^ 2 * (s ^ r * aeval s (Fpoly N) * Lker (11 * N) s)

def stripS (N : ℕ) : Set ℂ :=
  {s | -((6 * N : ℕ) : ℝ) - 1 / 2 ≤ s.re ∧ s.re ≤ -((6 * N : ℕ) : ℝ)}

theorem prod_sub_ne_zero (m : ℕ) (s : ℂ) (hs : s.re < 0) : ∏ j ∈ range (m + 1), (s - j) ≠ 0 :=
  prod_ne_zero_iff.2 fun j _ h => by
    have h2 : (s - j).re = 0 := by rw [h, Complex.zero_re]
    rw [Complex.sub_re, Complex.natCast_re] at h2
    exact (sub_neg.2 (hs.trans_le (Nat.cast_nonneg j))).ne h2

theorem one_le_norm_sub (s : ℂ) (hs : s.re ≤ -1) (j : ℕ) : 1 ≤ ‖s - j‖ := by
  have h := Complex.re_le_norm ((j : ℂ) - s)
  rw [Complex.sub_re, Complex.natCast_re, norm_sub_rev] at h
  have h2 : (1 : ℝ) ≤ (j : ℝ) - s.re := by
    have h3 := Nat.cast_nonneg (α := ℝ) j
    linarith
  exact h2.trans h

theorem norm_Lker_le (m : ℕ) (s : ℂ) (hs : s.re ≤ -1) : ‖Lker m s‖ ≤ m.factorial := by
  have h1 : 1 ≤ ∏ j ∈ range (m + 1), ‖s - j‖ := one_le_prod₀ fun j _ => one_le_norm_sub s hs j
  rw [Lker, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_natCast, norm_prod]
  exact div_le_self (Nat.cast_nonneg _) h1

theorem differentiableAt_Lker (m : ℕ) (s : ℂ) (hs : s.re < 0) :
    DifferentiableAt ℂ (Lker m) s :=
  (differentiableAt_const _).div (DifferentiableAt.fun_finsetProd fun _ _ =>
    differentiableAt_id.sub_const _) (prod_sub_ne_zero m s hs)

theorem differentiableAt_kerG (N r : ℕ) (s : ℂ) (hs : s.re < 0)
    (hsin : Complex.sin ((π : ℂ) * s) ≠ 0) : DifferentiableAt ℂ (kerG N r) s := by
  have h1 : DifferentiableAt ℂ (fun t : ℂ => Complex.sin ((π : ℂ) * t)) s :=
    ((differentiableAt_const (π : ℂ)).mul differentiableAt_fun_id).csin
  have h2 : DifferentiableAt ℂ (fun t : ℂ => ((π : ℂ) / Complex.sin ((π : ℂ) * t)) ^ 2) s :=
    ((differentiableAt_const _).div h1 hsin).pow 2
  have h3 : DifferentiableAt ℂ (fun t : ℂ => t ^ r * aeval t (Fpoly N) * Lker (11 * N) t) s :=
    ((differentiableAt_fun_id.pow r).mul (Polynomial.differentiable_aeval _ s)).mul
      (differentiableAt_Lker _ s hs)
  exact h2.mul h3

theorem sin_sq_lower (t : ℝ) (h1 : -(1 / 2) ≤ t) (h2 : t ≤ 0) :
    4 * t ^ 2 ≤ Real.sin (π * t) ^ 2 := by
  have ha : 0 ≤ -(π * t) := neg_nonneg.2 (mul_nonpos_of_nonneg_of_nonpos pi_pos.le h2)
  have hb : -(π * t) ≤ π / 2 := by
    rw [neg_mul_eq_mul_neg, ← mul_one_div]
    exact mul_le_mul_of_nonneg_left (neg_le.1 h1) pi_pos.le
  have h3 := Real.mul_le_sin ha hb
  rw [Real.sin_neg, mul_neg, ← mul_assoc, div_mul_cancel₀ 2 pi_ne_zero] at h3
  calc 4 * t ^ 2 = (-(2 * t)) ^ 2 := by ring
    _ ≤ (-Real.sin (π * t)) ^ 2 := pow_le_pow_left₀ (by linarith) h3 2
    _ = Real.sin (π * t) ^ 2 := neg_sq _

theorem norm_sin_lower (M : ℕ) (s : ℂ) (h1 : -(M : ℝ) - 1 / 2 ≤ s.re) (h2 : s.re ≤ -(M : ℝ)) :
    4 * ‖s - -(M : ℂ)‖ ^ 2 ≤ ‖Complex.sin ((π : ℂ) * s)‖ ^ 2 := by
  have hs := sin_line_normSq s.re s.im
  rw [lineAt, Complex.re_add_im] at hs
  have ht := sin_sq_lower (s.re + M) (by linarith) (by linarith)
  have hx : π * s.re = π * (s.re + M) - M * π := by ring
  have hsh := sq_le_sinh_sq (π * s.im)
  have hpi : (4 : ℝ) ≤ π ^ 2 := by
    have h := pow_le_pow_left₀ zero_le_two Real.two_le_pi 2
    norm_num at h
    exact h
  rw [Complex.sq_norm, Complex.sq_norm, hs, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.neg_re, Complex.neg_im, Complex.natCast_re, Complex.natCast_im, neg_zero, sub_zero,
    sub_neg_eq_add, hx, Real.sin_sub_nat_mul_pi, mul_pow, ← pow_mul, mul_comm M 2, pow_mul,
    neg_one_sq, one_pow, one_mul]
  calc 4 * ((s.re + M) * (s.re + M) + s.im * s.im) = 4 * (s.re + M) ^ 2 + 4 * s.im ^ 2 := by ring
    _ ≤ Real.sin (π * (s.re + M)) ^ 2 + (π * s.im) ^ 2 := add_le_add ht (by
        rw [mul_pow]; exact mul_le_mul_of_nonneg_right hpi (sq_nonneg _))
    _ ≤ _ := add_le_add le_rfl hsh

theorem isRoot_binomPoly (m a k : ℕ) (h1 : m ≤ a) (h2 : a - m < k) :
    (binomPoly ℚ (a : ℚ) k).IsRoot (-(m : ℚ)) := by
  rw [IsRoot.def, binomPoly, eval_mul, eval_C, eval_comp, eval_add, eval_X, eval_C,
    neg_add_eq_sub, ← Nat.cast_sub h1, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_zero_iff_lt.2 h2, Nat.cast_zero, mul_zero]

theorem dvd_Fpoly (N : ℕ) (hN : 1 ≤ N) : (X - C (-((6 * N : ℕ) : ℚ))) ^ 3 ∣ Fpoly N := by
  have h : ∀ a : ℕ, 6 * N ≤ a → a - 6 * N < 8 * N →
      X - C (-((6 * N : ℕ) : ℚ)) ∣ binomPoly ℚ (a : ℚ) (8 * N) :=
    fun a h1 h2 => dvd_iff_isRoot.2 (isRoot_binomPoly (6 * N) a (8 * N) h1 h2)
  rw [pow_three', Fpoly]
  exact mul_dvd_mul (mul_dvd_mul (h _ (by omega) (by omega)) (h _ (by omega) (by omega)))
    (h _ (by omega) (by omega))

theorem G_factor (N r : ℕ) (Q : ℚ[X]) (hQ : Fpoly N = (X - C (-((6 * N : ℕ) : ℚ))) ^ 3 * Q)
    (s : ℂ) : s ^ r * aeval s (Fpoly N) * Lker (11 * N) s =
      (s - -((6 * N : ℕ) : ℂ)) ^ 3 * (s ^ r * aeval s Q * Lker (11 * N) s) := by
  rw [hQ, map_mul, map_pow, map_sub, aeval_X, aeval_C, map_neg, map_natCast]
  ring

theorem kerG_near (N r : ℕ) (Q : ℚ[X]) (hQ : Fpoly N = (X - C (-((6 * N : ℕ) : ℚ))) ^ 3 * Q)
    (s : ℂ) (hs : s ∈ stripS N) :
    ‖kerG N r s‖ ≤
      π ^ 2 / 4 * (‖s - -((6 * N : ℕ) : ℂ)‖ * ‖s ^ r * aeval s Q * Lker (11 * N) s‖) := by
  have hl := norm_sin_lower (6 * N) s hs.1 hs.2
  rw [kerG, G_factor N r Q hQ, norm_mul, norm_mul, norm_pow, norm_pow, norm_div, Complex.norm_real,
    Real.norm_of_nonneg pi_pos.le]
  set w := ‖s - -((6 * N : ℕ) : ℂ)‖
  set H := ‖s ^ r * aeval s Q * Lker (11 * N) s‖
  set D := ‖Complex.sin ((π : ℂ) * s)‖
  have hk : (π / D) ^ 2 * w ^ 2 ≤ π ^ 2 / 4 := by
    rw [div_pow, div_mul_eq_mul_div]
    refine div_le_of_le_mul₀ (sq_nonneg _) (div_nonneg (sq_nonneg _) zero_le_four) ?_
    calc π ^ 2 * w ^ 2 = π ^ 2 / 4 * (4 * w ^ 2) := by ring
      _ ≤ π ^ 2 / 4 * D ^ 2 :=
        mul_le_mul_of_nonneg_left hl (div_nonneg (sq_nonneg _) zero_le_four)
  calc (π / D) ^ 2 * (w ^ 3 * H) = (π / D) ^ 2 * w ^ 2 * (w * H) := by ring
    _ ≤ π ^ 2 / 4 * (w * H) :=
      mul_le_mul_of_nonneg_right hk (mul_nonneg (norm_nonneg _) (norm_nonneg _))

theorem neg_six_lt (N : ℕ) (hN : 1 ≤ N) : -((6 * N : ℕ) : ℝ) < 0 :=
  neg_lt_zero.2 (Nat.cast_pos.2 (by omega))

theorem continuousOn_kerG (N r : ℕ) (hN : 1 ≤ N) : ContinuousOn (kerG N r) (stripS N) := by
  obtain ⟨Q, hQ⟩ := dvd_Fpoly N hN
  intro s hs
  have hre : s.re < 0 := hs.2.trans_lt (neg_six_lt N hN)
  by_cases h0 : s = -((6 * N : ℕ) : ℂ)
  · have hH : ContinuousAt (fun t : ℂ => π ^ 2 / 4 * (‖t - -((6 * N : ℕ) : ℂ)‖ *
        ‖t ^ r * aeval t Q * Lker (11 * N) t‖)) s :=
      continuousAt_const.mul ((continuousAt_id.sub continuousAt_const).norm.mul
        (((continuousAt_id.pow r).mul (Polynomial.continuous_aeval Q).continuousAt).mul
          (differentiableAt_Lker _ s hre).continuousAt).norm)
    have hz : kerG N r s = 0 := by
      have h := kerG_near N r Q hQ s hs
      rw [h0, sub_self, norm_zero, zero_mul, mul_zero] at h
      rw [h0]
      exact norm_le_zero_iff.1 h
    have ht : Tendsto (fun t : ℂ => π ^ 2 / 4 * (‖t - -((6 * N : ℕ) : ℂ)‖ *
        ‖t ^ r * aeval t Q * Lker (11 * N) t‖)) (𝓝 s) (𝓝 0) := by
      convert hH.tendsto using 2
      simp only [h0, sub_self, norm_zero, zero_mul, mul_zero]
    rw [ContinuousWithinAt, hz]
    exact squeeze_zero_norm' (eventually_nhdsWithin_of_forall fun t ht =>
      kerG_near N r Q hQ t ht) (tendsto_nhdsWithin_of_tendsto_nhds ht)
  · have hsin : Complex.sin ((π : ℂ) * s) ≠ 0 := fun h => by
      have h1 := norm_sin_lower (6 * N) s hs.1 hs.2
      rw [h, norm_zero, zero_pow two_ne_zero] at h1
      exact absurd h1 (not_le.2 (mul_pos four_pos (pow_pos (norm_pos_iff.2 (sub_ne_zero.2 h0)) 2)))
    exact (differentiableAt_kerG N r s hre hsin).continuousAt.continuousWithinAt

theorem pow_le_cosh (k : ℕ) (y : ℝ) :
    (1 + |y|) ^ k ≤ 2 * exp 1 * (k.factorial : ℝ) * Real.cosh (π * y) := by
  have h2 := Real.pow_div_factorial_le_exp (1 + |y|) (add_nonneg zero_le_one (abs_nonneg y)) k
  rw [div_le_iff₀ (Nat.cast_pos.2 (Nat.factorial_pos k) : (0 : ℝ) < k.factorial), exp_add] at h2
  calc (1 + |y|) ^ k ≤ exp 1 * exp |y| * (k.factorial : ℝ) := h2
    _ ≤ exp 1 * (2 * Real.cosh (π * y)) * (k.factorial : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (exp_abs_le_two_cosh y)
          (exp_pos 1).le) (Nat.cast_nonneg _)
    _ = 2 * exp 1 * (k.factorial : ℝ) * Real.cosh (π * y) := by ring

theorem kernel_cosh_le (x y : ℝ) (hy : 1 ≤ |y|) :
    ‖((π : ℂ) / Complex.sin ((π : ℂ) * lineAt x y)) ^ 2‖ * Real.cosh (π * y) ^ 2 ≤ 2 * π ^ 2 := by
  have h1 : 1 ≤ Real.sinh (π * y) ^ 2 := by
    have hp : (1 : ℝ) ≤ π ^ 2 := (one_le_sq_iff_one_le_abs π).2
      (by rw [abs_of_pos pi_pos]; exact one_le_two.trans Real.two_le_pi)
    have hy2 : (1 : ℝ) ≤ y ^ 2 := (one_le_sq_iff_one_le_abs y).2 hy
    have h3 : (1 : ℝ) ≤ (π * y) ^ 2 := by
      rw [mul_pow]; exact one_le_mul_of_one_le_of_one_le hp hy2
    exact h3.trans (sq_le_sinh_sq _)
  have h2 : Real.cosh (π * y) ^ 2 ≤ 2 * (Real.sin (π * x) ^ 2 + Real.sinh (π * y) ^ 2) := by
    rw [Real.cosh_sq]
    calc Real.sinh (π * y) ^ 2 + 1 ≤ Real.sinh (π * y) ^ 2 + Real.sinh (π * y) ^ 2 :=
          add_le_add le_rfl h1
      _ = 2 * Real.sinh (π * y) ^ 2 := (two_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (sq_nonneg _)) zero_le_two
  rw [kernel_norm, div_mul_eq_mul_div]
  refine div_le_of_le_mul₀ (add_nonneg (sq_nonneg _) (sq_nonneg _))
    (mul_nonneg zero_le_two (sq_nonneg π)) ?_
  calc π ^ 2 * Real.cosh (π * y) ^ 2
      ≤ π ^ 2 * (2 * (Real.sin (π * x) ^ 2 + Real.sinh (π * y) ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg π)
    _ = 2 * π ^ 2 * (Real.sin (π * x) ^ 2 + Real.sinh (π * y) ^ 2) := by ring

theorem G_bound (N r : ℕ) (hN : 1 ≤ N) : ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ s : ℂ, s ∈ stripS N →
    ‖s ^ r * aeval s (Fpoly N) * Lker (11 * N) s‖ ≤ C * (1 + |s.im|) ^ d := by
  obtain ⟨C, hC0, hC⟩ := poly_bound (X ^ r * Fpoly N) ((6 * N : ℕ) + 1)
  refine ⟨C * ((11 * N).factorial : ℝ), mul_nonneg hC0 (Nat.cast_nonneg _),
    (X ^ r * Fpoly N).natDegree, fun s hs => ?_⟩
  have h6 : (1 : ℝ) ≤ ((6 * N : ℕ) : ℝ) := Nat.one_le_cast.2 (by omega)
  have ha : |s.re| ≤ ((6 * N : ℕ) : ℝ) + 1 := abs_le.2 ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hl := norm_Lker_le (11 * N) s (by linarith [hs.2])
  have hp := hC s ha
  rw [map_mul, map_pow, aeval_X] at hp
  rw [norm_mul]
  refine (mul_le_mul hp hl (norm_nonneg _) (mul_nonneg hC0 (pow_nonneg (add_nonneg zero_le_one
    (abs_nonneg _)) _))).trans (le_of_eq ?_)
  ring

theorem sin_ne_zero_of (N : ℕ) (s : ℂ) (hs : s ∈ stripS N) (h0 : s ≠ -((6 * N : ℕ) : ℂ)) :
    Complex.sin ((π : ℂ) * s) ≠ 0 := fun h => by
  have h1 := norm_sin_lower (6 * N) s hs.1 hs.2
  rw [h, norm_zero, zero_pow two_ne_zero] at h1
  exact absurd h1 (not_le.2 (mul_pos four_pos (pow_pos (norm_pos_iff.2 (sub_ne_zero.2 h0)) 2)))

theorem kerG_far (N r : ℕ) (hN : 1 ≤ N) : ∃ M : ℝ, ∀ x y : ℝ, lineAt x y ∈ stripS N →
    1 ≤ |y| → ‖kerG N r (lineAt x y)‖ * (1 + y ^ 2) ≤ M := by
  obtain ⟨C, hC0, d, hC⟩ := G_bound N r hN
  refine ⟨2 * π ^ 2 * (C * (2 * exp 1 * ((d + 2).factorial : ℝ))), fun x y hs hy => ?_⟩
  have hG := hC _ hs
  rw [lineAt_im] at hG
  have hk := kernel_cosh_le x y hy
  have hE : 0 ≤ 2 * exp 1 * ((d + 2).factorial : ℝ) :=
    mul_nonneg (mul_nonneg zero_le_two (exp_pos 1).le) (Nat.cast_nonneg _)
  have hpc : (1 + |y|) ^ (d + 2) ≤ 2 * exp 1 * ((d + 2).factorial : ℝ) * Real.cosh (π * y) ^ 2 :=
    (pow_le_cosh (d + 2) y).trans (mul_le_mul_of_nonneg_left
      (le_self_pow₀ (Real.one_le_cosh _) two_ne_zero) hE)
  have hy1 : 0 ≤ 1 + |y| := add_nonneg zero_le_one (abs_nonneg y)
  have hy2 : 1 + y ^ 2 ≤ (1 + |y|) ^ 2 := by
    rw [add_sq, one_pow, mul_one, sq_abs]
    exact add_le_add (le_add_of_nonneg_right (mul_nonneg zero_le_two (abs_nonneg y))) le_rfl
  rw [kerG, norm_mul]
  set K := ‖((π : ℂ) / Complex.sin ((π : ℂ) * lineAt x y)) ^ 2‖
  set G := ‖lineAt x y ^ r * aeval (lineAt x y) (Fpoly N) * Lker (11 * N) (lineAt x y)‖
  have hK0 : 0 ≤ K := norm_nonneg _
  calc K * G * (1 + y ^ 2) ≤ K * (C * (1 + |y|) ^ d) * (1 + |y|) ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hG hK0) hy2
          (add_nonneg zero_le_one (sq_nonneg y))
          (mul_nonneg hK0 (mul_nonneg hC0 (pow_nonneg hy1 _)))
    _ = C * (K * (1 + |y|) ^ (d + 2)) := by ring
    _ ≤ C * (K * (2 * exp 1 * ((d + 2).factorial : ℝ) * Real.cosh (π * y) ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpc hK0) hC0
    _ = K * Real.cosh (π * y) ^ 2 * (C * (2 * exp 1 * ((d + 2).factorial : ℝ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hk (mul_nonneg hC0 hE)

theorem strip_le (N : ℕ) : -((6 * N : ℕ) : ℝ) - 1 / 2 ≤ -((6 * N : ℕ) : ℝ) :=
  sub_le_self _ one_half_pos.le

theorem kerG_bound (N r : ℕ) (hN : 1 ≤ N) : ∃ M : ℝ, ∀ x y : ℝ, lineAt x y ∈ stripS N →
    ‖kerG N r (lineAt x y)‖ ≤ M * (1 + y ^ 2)⁻¹ := by
  obtain ⟨M2, hM2⟩ := kerG_far N r hN
  have hc := strip_le N
  have hR : IsCompact (Set.uIcc (-((6 * N : ℕ) : ℝ) - 1 / 2) (-((6 * N : ℕ) : ℝ)) ×ℂ
      Set.uIcc (-1 : ℝ) 1) := isCompact_uIcc.reProdIm isCompact_uIcc
  have hsub : Set.uIcc (-((6 * N : ℕ) : ℝ) - 1 / 2) (-((6 * N : ℕ) : ℝ)) ×ℂ
      Set.uIcc (-1 : ℝ) 1 ⊆ stripS N := fun s hs => by
    rw [Complex.mem_reProdIm, Set.uIcc_of_le hc] at hs
    exact hs.1
  obtain ⟨C1, hC1⟩ := hR.exists_bound_of_continuousOn ((continuousOn_kerG N r hN).mono hsub)
  refine ⟨max (2 * C1) M2, fun x y hs => ?_⟩
  have hpos : 0 < 1 + y ^ 2 := add_pos_of_pos_of_nonneg one_pos (sq_nonneg y)
  rw [le_mul_inv_iff₀ hpos]
  rcases le_or_gt |y| 1 with hy | hy
  · have hm : lineAt x y ∈ Set.uIcc (-((6 * N : ℕ) : ℝ) - 1 / 2) (-((6 * N : ℕ) : ℝ)) ×ℂ
        Set.uIcc (-1 : ℝ) 1 := Complex.mem_reProdIm.2 ⟨by rw [Set.uIcc_of_le hc]; exact hs,
          by rw [lineAt_im]; exact Set.mem_uIcc.2 (Or.inl (abs_le.1 hy))⟩
    have h1 := hC1 _ hm
    have h2 : 1 + y ^ 2 ≤ 2 := by
      have h3 := (sq_le_one_iff_abs_le_one y).2 hy
      linarith
    calc ‖kerG N r (lineAt x y)‖ * (1 + y ^ 2) ≤ C1 * 2 :=
          mul_le_mul h1 h2 hpos.le ((norm_nonneg _).trans h1)
      _ = 2 * C1 := mul_comm _ _
      _ ≤ _ := le_max_left _ _
  · exact (hM2 x y hs hy.le).trans (le_max_right _ _)

theorem integrable_line (N r : ℕ) (hN : 1 ≤ N) (c : ℝ) (h1 : -((6 * N : ℕ) : ℝ) - 1 / 2 ≤ c)
    (h2 : c ≤ -((6 * N : ℕ) : ℝ)) : Integrable (fun y : ℝ => kerG N r (lineAt c y)) := by
  obtain ⟨M, hM⟩ := kerG_bound N r hN
  have hm : ∀ y, lineAt c y ∈ stripS N := fun y =>
    ⟨by rw [lineAt_re]; exact h1, by rw [lineAt_re]; exact h2⟩
  have hcont : Continuous (fun y : ℝ => kerG N r (lineAt c y)) :=
    (continuousOn_kerG N r hN).comp_continuous (continuous_lineAt c) hm
  exact (integrable_inv_one_add_sq.const_mul M).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun y => hM c y (hm y))

theorem horiz_bound (N r : ℕ) (hN : 1 ≤ N) : ∃ M : ℝ, ∀ t : ℝ,
    ‖∫ x : ℝ in (-((6 * N : ℕ) : ℝ) - 1 / 2)..(-((6 * N : ℕ) : ℝ)),
      kerG N r (x + t * Complex.I)‖ ≤
      M * (1 + t ^ 2)⁻¹ * |(-((6 * N : ℕ) : ℝ)) - (-((6 * N : ℕ) : ℝ) - 1 / 2)| := by
  obtain ⟨M, hM⟩ := kerG_bound N r hN
  refine ⟨M, fun t => intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_⟩
  rw [Set.uIoc_of_le (strip_le N)] at hx
  exact hM x t ⟨by rw [lineAt_re]; exact hx.1.le, by rw [lineAt_re]; exact hx.2⟩

theorem rect_eq (N r : ℕ) (hN : 1 ≤ N) (T : ℝ) :
    (∫ x : ℝ in (-((6 * N : ℕ) : ℝ) - 1 / 2)..(-((6 * N : ℕ) : ℝ)),
        kerG N r (x + ((-T : ℝ) : ℂ) * Complex.I)) -
      (∫ x : ℝ in (-((6 * N : ℕ) : ℝ) - 1 / 2)..(-((6 * N : ℕ) : ℝ)),
        kerG N r (x + T * Complex.I)) +
      Complex.I • (∫ y : ℝ in (-T)..T, kerG N r (((-((6 * N : ℕ) : ℝ) : ℝ) : ℂ) + y * Complex.I)) -
      Complex.I • (∫ y : ℝ in (-T)..T,
        kerG N r (((-((6 * N : ℕ) : ℝ) - 1 / 2 : ℝ) : ℂ) + y * Complex.I)) = 0 := by
  have hc := strip_le N
  have h := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn (kerG N r)
    (lineAt (-((6 * N : ℕ) : ℝ) - 1 / 2) (-T)) (lineAt (-((6 * N : ℕ) : ℝ)) T)
  rw [lineAt_re, lineAt_re, lineAt_im, lineAt_im, min_eq_left hc, max_eq_right hc,
    Set.uIcc_of_le hc] at h
  refine h ((continuousOn_kerG N r hN).mono fun s hs => (Complex.mem_reProdIm.1 hs).1)
    (fun s hs => ?_)
  have hs1 := (Complex.mem_reProdIm.1 hs).1
  have hne : s ≠ -((6 * N : ℕ) : ℂ) := fun he => by
    have h2 := congrArg Complex.re he
    rw [Complex.neg_re, Complex.natCast_re] at h2
    exact hs1.2.ne h2
  exact (differentiableAt_kerG N r s (hs1.2.trans (neg_six_lt N hN))
    (sin_ne_zero_of N s ⟨hs1.1.le, hs1.2.le⟩ hne)).differentiableWithinAt

theorem line_integrals_eq (N r : ℕ) (hN : 1 ≤ N) :
    ∫ y : ℝ, kerG N r (lineAt (-((6 * N : ℕ) : ℝ) - 1 / 2) y) =
      ∫ y : ℝ, kerG N r (lineAt (-((6 * N : ℕ) : ℝ)) y) := by
  obtain ⟨M, hM⟩ := horiz_bound N r hN
  have hc := strip_le N
  set K := |(-((6 * N : ℕ) : ℝ)) - (-((6 * N : ℕ) : ℝ) - 1 / 2)|
  have hinv : Tendsto (fun T : ℝ => M * (1 + T ^ 2)⁻¹ * K) atTop (𝓝 0) := by
    have h := ((tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop 1
      (tendsto_pow_atTop two_ne_zero))).const_mul M).mul_const K
    rwa [mul_zero, zero_mul] at h
  have htop := squeeze_zero_norm hM hinv
  have hbot : Tendsto (fun T : ℝ => ∫ x : ℝ in (-((6 * N : ℕ) : ℝ) - 1 / 2)..(-((6 * N : ℕ) : ℝ)),
      kerG N r (x + ((-T : ℝ) : ℂ) * Complex.I)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun T => by have h := hM (-T); rwa [neg_sq] at h) hinv
  have hv0 := intervalIntegral_tendsto_integral (integrable_line N r hN _ hc le_rfl)
    tendsto_neg_atTop_atBot tendsto_id
  have hv1 := intervalIntegral_tendsto_integral (integrable_line N r hN _ le_rfl hc)
    tendsto_neg_atTop_atBot tendsto_id
  have hlim := ((hbot.sub htop).add (hv0.const_smul Complex.I)).sub (hv1.const_smul Complex.I)
  have heq := tendsto_nhds_unique (hlim.congr fun T => rect_eq N r hN T) tendsto_const_nhds
  rw [sub_self, zero_add, smul_eq_mul, smul_eq_mul, ← mul_sub, mul_eq_zero] at heq
  exact (sub_eq_zero.1 (heq.resolve_left Complex.I_ne_zero)).symm

theorem barnes_shift_core (N r : ℕ) (hN : 1 ≤ N) :
    barnesI (6 * N) (fun s => s ^ r * aeval s (Fpoly N) * Lker (11 * N) s) =
      Zeta2BarnesIdentities.barnesAt (-((6 * N : ℕ) : ℝ))
        (fun s => s ^ r * aeval s (Fpoly N) * Lker (11 * N) s) := by
  rw [barnesI_eq]
  exact congrArg (fun z : ℂ => (1 / (2 * π) : ℂ) * z) (line_integrals_eq N r hN)

end Zeta2ECBShift
