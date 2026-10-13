import Zeta2FourTrajectoryMatrices.Analytic.barnes_step_aux

open Polynomial Filter Topology Real Finset MeasureTheory Zeta2Blueprint

noncomputable section

namespace Zeta2BarnesStep

def stripC (n : ℤ) : Set ℂ := {s | (n : ℝ) - 1 / 2 ≤ s.re ∧ s.re ≤ n + 1 / 2}

theorem stripC_le (n : ℤ) : (n : ℝ) - 1 / 2 ≤ n + 1 / 2 := by linarith

theorem abs_of_stripC (n : ℤ) (x : ℝ) (h1 : (n : ℝ) - 1 / 2 ≤ x) (h2 : x ≤ n + 1 / 2) :
    |x - n| ≤ 1 / 2 :=
  abs_le.2 ⟨by linarith, by linarith⟩

theorem stripC_of_abs (n : ℤ) (x : ℝ) (h : |x - n| ≤ 1 / 2) :
    (n : ℝ) - 1 / 2 ≤ x ∧ x ≤ n + 1 / 2 := by
  have h1 := abs_le.1 h
  exact ⟨by linarith [h1.1], by linarith [h1.2]⟩

theorem stripC_sub (n : ℤ) : stripC n ⊆ stripO n := fun s hs =>
  (abs_of_stripC n s.re hs.1 hs.2).trans_lt (by norm_num)

theorem gRem_bound (n : ℤ) (g : ℂ → ℂ) (C : ℝ) (d : ℕ)
    (hb : ∀ s : ℂ, |s.re - n| ≤ 1 / 2 → ‖g s‖ ≤ C * (1 + |s.im|) ^ d) (s : ℂ)
    (hs : |s.re - n| ≤ 1 / 2) :
    ‖g s - g n - deriv g n * (s - n)‖ ≤
      (|C| + ‖g n‖ + ‖deriv g n‖) * (1 + |s.im|) ^ (d + 1) := by
  have hu : 1 ≤ 1 + |s.im| := le_add_of_nonneg_right (abs_nonneg _)
  have hP : 1 + |s.im| ≤ (1 + |s.im|) ^ (d + 1) := le_self_pow₀ hu (Nat.succ_ne_zero d)
  have hd : (1 + |s.im|) ^ d ≤ (1 + |s.im|) ^ (d + 1) := pow_le_pow_right₀ hu (Nat.le_succ d)
  have hsn : ‖s - n‖ ≤ 1 + |s.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.sub_re, Complex.sub_im, Complex.intCast_re, Complex.intCast_im, sub_zero]
    exact add_le_add (hs.trans (by norm_num)) le_rfl
  have h1 : ‖g s‖ ≤ |C| * (1 + |s.im|) ^ (d + 1) := (hb s hs).trans
    (mul_le_mul (le_abs_self C) hd (pow_nonneg (zero_le_one.trans hu) _) (abs_nonneg C))
  have h2 : ‖g n‖ ≤ ‖g n‖ * (1 + |s.im|) ^ (d + 1) :=
    le_mul_of_one_le_right (norm_nonneg _) (hu.trans hP)
  have h3 : ‖deriv g n * (s - n)‖ ≤ ‖deriv g n‖ * (1 + |s.im|) ^ (d + 1) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hsn.trans hP) (norm_nonneg _)
  calc ‖g s - g n - deriv g n * (s - n)‖ ≤ ‖g s‖ + ‖g n‖ + ‖deriv g n * (s - n)‖ :=
        (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    _ ≤ |C| * (1 + |s.im|) ^ (d + 1) + ‖g n‖ * (1 + |s.im|) ^ (d + 1) +
        ‖deriv g n‖ * (1 + |s.im|) ^ (d + 1) := add_le_add (add_le_add h1 h2) h3
    _ = _ := by rw [add_mul, add_mul]

theorem regF_far_bound (n : ℤ) (g : ℂ → ℂ) (C : ℝ) (d : ℕ)
    (hb : ∀ s : ℂ, |s.re - n| ≤ 1 / 2 → ‖g s‖ ≤ C * (1 + |s.im|) ^ d) :
    ∃ M : ℝ, ∀ x y : ℝ, |x - n| ≤ 1 / 2 → 1 ≤ |y| →
      ‖regF n g (lineB x y)‖ * (1 + y ^ 2) ≤ M := by
  have hA : 0 ≤ |C| + ‖g n‖ + ‖deriv g n‖ :=
    add_nonneg (add_nonneg (abs_nonneg C) (norm_nonneg _)) (norm_nonneg _)
  refine ⟨2 * π ^ 2 * ((|C| + ‖g n‖ + ‖deriv g n‖) * (2 * exp 1 * ((d + 3).factorial : ℝ))),
    fun x y hx hy => ?_⟩
  have hG := gRem_bound n g C d hb (lineB x y) (by rw [lineB_re]; exact hx)
  rw [lineB_im] at hG
  have hk := kerK_cosh_le x y hy
  have hE : 0 ≤ 2 * exp 1 * ((d + 3).factorial : ℝ) :=
    mul_nonneg (mul_nonneg zero_le_two (exp_pos 1).le) (Nat.cast_nonneg _)
  have hpc : (1 + |y|) ^ (d + 3) ≤ 2 * exp 1 * ((d + 3).factorial : ℝ) * Real.cosh (π * y) ^ 2 :=
    (pow_le_cosh2 (d + 3) y).trans (mul_le_mul_of_nonneg_left
      (le_self_pow₀ (Real.one_le_cosh _) two_ne_zero) hE)
  have hy1 : 0 ≤ 1 + |y| := add_nonneg zero_le_one (abs_nonneg y)
  have hy2 : 1 + y ^ 2 ≤ (1 + |y|) ^ 2 := by
    rw [add_sq, one_pow, mul_one, sq_abs]
    exact add_le_add (le_add_of_nonneg_right (mul_nonneg zero_le_two (abs_nonneg y))) le_rfl
  rw [regF_far n g _ (sin_ne_zero_far x y hy), norm_mul]
  set A := |C| + ‖g n‖ + ‖deriv g n‖
  set K := ‖kerK (lineB x y)‖
  set G := ‖g (lineB x y) - g n - deriv g n * (lineB x y - n)‖
  have hK0 : 0 ≤ K := norm_nonneg _
  calc K * G * (1 + y ^ 2) ≤ K * (A * (1 + |y|) ^ (d + 1)) * (1 + |y|) ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hG hK0) hy2
          (add_nonneg zero_le_one (sq_nonneg y))
          (mul_nonneg hK0 (mul_nonneg hA (pow_nonneg hy1 _)))
    _ = A * (K * (1 + |y|) ^ (d + 3)) := by ring
    _ ≤ A * (K * (2 * exp 1 * ((d + 3).factorial : ℝ) * Real.cosh (π * y) ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpc hK0) hA
    _ = K * Real.cosh (π * y) ^ 2 * (A * (2 * exp 1 * ((d + 3).factorial : ℝ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hk (mul_nonneg hA hE)

theorem continuousOn_regF (n : ℤ) (g : ℂ → ℂ) (hd : DifferentiableOn ℂ g (stripO n)) :
    ContinuousOn (regF n g) (stripC n) :=
  ((differentiableOn_regF n g hd).mono (stripC_sub n)).continuousOn

theorem regF_bound (n : ℤ) (g : ℂ → ℂ) (hd : DifferentiableOn ℂ g (stripO n)) (C : ℝ) (d : ℕ)
    (hb : ∀ s : ℂ, |s.re - n| ≤ 1 / 2 → ‖g s‖ ≤ C * (1 + |s.im|) ^ d) :
    ∃ M : ℝ, ∀ x y : ℝ, |x - n| ≤ 1 / 2 → ‖regF n g (lineB x y)‖ ≤ M * (1 + y ^ 2)⁻¹ := by
  obtain ⟨M2, hM2⟩ := regF_far_bound n g C d hb
  have hc := stripC_le n
  have hR : IsCompact (Set.uIcc ((n : ℝ) - 1 / 2) (n + 1 / 2) ×ℂ Set.uIcc (-1 : ℝ) 1) :=
    isCompact_uIcc.reProdIm isCompact_uIcc
  have hsub : Set.uIcc ((n : ℝ) - 1 / 2) (n + 1 / 2) ×ℂ Set.uIcc (-1 : ℝ) 1 ⊆ stripC n :=
    fun s hs => by
      rw [Complex.mem_reProdIm, Set.uIcc_of_le hc] at hs
      exact hs.1
  obtain ⟨C1, hC1⟩ := hR.exists_bound_of_continuousOn ((continuousOn_regF n g hd).mono hsub)
  refine ⟨max (2 * C1) M2, fun x y hx => ?_⟩
  have hpos : 0 < 1 + y ^ 2 := add_pos_of_pos_of_nonneg one_pos (sq_nonneg y)
  rw [le_mul_inv_iff₀ hpos]
  rcases le_or_gt |y| 1 with hy | hy
  · have hm : lineB x y ∈ Set.uIcc ((n : ℝ) - 1 / 2) (n + 1 / 2) ×ℂ Set.uIcc (-1 : ℝ) 1 :=
      Complex.mem_reProdIm.2 ⟨by rw [Set.uIcc_of_le hc, lineB_re]; exact stripC_of_abs n x hx,
        by rw [lineB_im]; exact Set.mem_uIcc.2 (Or.inl (abs_le.1 hy))⟩
    have h1 := hC1 _ hm
    have h2 : 1 + y ^ 2 ≤ 2 := by
      have h3 := (sq_le_one_iff_abs_le_one y).2 hy
      linarith
    calc ‖regF n g (lineB x y)‖ * (1 + y ^ 2) ≤ C1 * 2 :=
          mul_le_mul h1 h2 hpos.le ((norm_nonneg _).trans h1)
      _ = 2 * C1 := mul_comm _ _
      _ ≤ _ := le_max_left _ _
  · exact (hM2 x y hx hy.le).trans (le_max_right _ _)

theorem integrable_regF_line (n : ℤ) (g : ℂ → ℂ) (hd : DifferentiableOn ℂ g (stripO n)) (C : ℝ)
    (d : ℕ) (hb : ∀ s : ℂ, |s.re - n| ≤ 1 / 2 → ‖g s‖ ≤ C * (1 + |s.im|) ^ d) (c : ℝ)
    (hc : |c - n| ≤ 1 / 2) : Integrable (fun y : ℝ => regF n g (lineB c y)) := by
  obtain ⟨M, hM⟩ := regF_bound n g hd C d hb
  have hm : ∀ y, lineB c y ∈ stripC n := fun y => by
    change (n : ℝ) - 1 / 2 ≤ (lineB c y).re ∧ (lineB c y).re ≤ n + 1 / 2
    rw [lineB_re]
    exact stripC_of_abs n c hc
  have hcont : Continuous (fun y : ℝ => regF n g (lineB c y)) :=
    (continuousOn_regF n g hd).comp_continuous (continuous_lineB c) hm
  exact (integrable_inv_one_add_sq.const_mul M).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun y => hM c y hc)

theorem horiz_regF (n : ℤ) (g : ℂ → ℂ) (hd : DifferentiableOn ℂ g (stripO n)) (C : ℝ) (d : ℕ)
    (hb : ∀ s : ℂ, |s.re - n| ≤ 1 / 2 → ‖g s‖ ≤ C * (1 + |s.im|) ^ d) : ∃ M : ℝ, ∀ t : ℝ,
    ‖∫ x : ℝ in ((n : ℝ) - 1 / 2)..((n : ℝ) + 1 / 2), regF n g (x + t * Complex.I)‖ ≤
      M * (1 + t ^ 2)⁻¹ * |((n : ℝ) + 1 / 2) - ((n : ℝ) - 1 / 2)| := by
  obtain ⟨M, hM⟩ := regF_bound n g hd C d hb
  refine ⟨M, fun t => intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_⟩
  rw [Set.uIoc_of_le (stripC_le n)] at hx
  exact hM x t (abs_of_stripC n x hx.1.le hx.2)

theorem rect_regF (n : ℤ) (g : ℂ → ℂ) (hd : DifferentiableOn ℂ g (stripO n)) (T : ℝ) :
    (∫ x : ℝ in ((n : ℝ) - 1 / 2)..((n : ℝ) + 1 / 2),
        regF n g (x + ((-T : ℝ) : ℂ) * Complex.I)) -
      (∫ x : ℝ in ((n : ℝ) - 1 / 2)..((n : ℝ) + 1 / 2), regF n g (x + T * Complex.I)) +
      Complex.I • (∫ y : ℝ in (-T)..T, regF n g ((((n : ℝ) + 1 / 2 : ℝ) : ℂ) + y * Complex.I)) -
      Complex.I • (∫ y : ℝ in (-T)..T,
        regF n g ((((n : ℝ) - 1 / 2 : ℝ) : ℂ) + y * Complex.I)) = 0 := by
  have hc := stripC_le n
  have h := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn (regF n g)
    (lineB ((n : ℝ) - 1 / 2) (-T)) (lineB ((n : ℝ) + 1 / 2) T)
  rw [lineB_re, lineB_re, lineB_im, lineB_im, min_eq_left hc, max_eq_right hc,
    Set.uIcc_of_le hc] at h
  refine h ((continuousOn_regF n g hd).mono fun s hs => (Complex.mem_reProdIm.1 hs).1)
    (((differentiableOn_regF n g hd).mono fun s hs => ?_))
  have hs1 := (Complex.mem_reProdIm.1 hs).1
  exact stripC_sub n ⟨hs1.1.le, hs1.2.le⟩

theorem regF_lines_eq (n : ℤ) (g : ℂ → ℂ) (hd : DifferentiableOn ℂ g (stripO n)) (C : ℝ)
    (d : ℕ) (hb : ∀ s : ℂ, |s.re - n| ≤ 1 / 2 → ‖g s‖ ≤ C * (1 + |s.im|) ^ d)
    (h0 : |((n : ℝ) - 1 / 2) - n| ≤ 1 / 2) (h1 : |((n : ℝ) + 1 / 2) - n| ≤ 1 / 2) :
    ∫ y : ℝ, regF n g (lineB ((n : ℝ) - 1 / 2) y) =
      ∫ y : ℝ, regF n g (lineB ((n : ℝ) + 1 / 2) y) := by
  obtain ⟨M, hM⟩ := horiz_regF n g hd C d hb
  set K := |((n : ℝ) + 1 / 2) - ((n : ℝ) - 1 / 2)|
  have hinv : Tendsto (fun T : ℝ => M * (1 + T ^ 2)⁻¹ * K) atTop (𝓝 0) := by
    have h := ((tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop 1
      (tendsto_pow_atTop two_ne_zero))).const_mul M).mul_const K
    rwa [mul_zero, zero_mul] at h
  have htop := squeeze_zero_norm hM hinv
  have hbot : Tendsto (fun T : ℝ => ∫ x : ℝ in ((n : ℝ) - 1 / 2)..((n : ℝ) + 1 / 2),
      regF n g (x + ((-T : ℝ) : ℂ) * Complex.I)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun T => by have h := hM (-T); rwa [neg_sq] at h) hinv
  have hv0 := intervalIntegral_tendsto_integral (integrable_regF_line n g hd C d hb _ h0)
    tendsto_neg_atTop_atBot tendsto_id
  have hv1 := intervalIntegral_tendsto_integral (integrable_regF_line n g hd C d hb _ h1)
    tendsto_neg_atTop_atBot tendsto_id
  have hlim := ((hbot.sub htop).add (hv1.const_smul Complex.I)).sub (hv0.const_smul Complex.I)
  have heq := tendsto_nhds_unique (hlim.congr fun T => rect_regF n g hd T) tendsto_const_nhds
  rw [sub_self, zero_add, smul_eq_mul, smul_eq_mul, ← mul_sub, mul_eq_zero] at heq
  exact (sub_eq_zero.1 (heq.resolve_left Complex.I_ne_zero)).symm

theorem barnes_step_core (n : ℤ) (g : ℂ → ℂ) (hd : DifferentiableOn ℂ g {s | |s.re - n| < 3 / 4})
    (C : ℝ) (d : ℕ) (hb : ∀ s : ℂ, |s.re - n| ≤ 1 / 2 → ‖g s‖ ≤ C * (1 + |s.im|) ^ d) :
    (1 / (2 * π)) * (∫ y : ℝ, ((π : ℂ) / Complex.sin ((π : ℂ) * (((n + 1 / 2 : ℝ) : ℂ) +
        y * Complex.I))) ^ 2 * g (((n + 1 / 2 : ℝ) : ℂ) + y * Complex.I)) -
      (1 / (2 * π)) * (∫ y : ℝ, ((π : ℂ) / Complex.sin ((π : ℂ) * (((n - 1 / 2 : ℝ) : ℂ) +
        y * Complex.I))) ^ 2 * g (((n - 1 / 2 : ℝ) : ℂ) + y * Complex.I)) = deriv g n := by
  have hd' : DifferentiableOn ℂ g (stripO n) := hd
  have hcos1 : Real.cos (π * ((n : ℝ) + 1 / 2)) = 0 := Real.cos_eq_zero_iff.2 ⟨n, by ring⟩
  have hcos0 : Real.cos (π * ((n : ℝ) - 1 / 2)) = 0 :=
    Real.cos_eq_zero_iff.2 ⟨n - 1, by rw [Int.cast_sub, Int.cast_one]; ring⟩
  have hab1 : |((n : ℝ) + 1 / 2) - n| ≤ 1 / 2 := by
    rw [add_sub_cancel_left, abs_of_pos one_half_pos]
  have hab0 : |((n : ℝ) - 1 / 2) - n| ≤ 1 / 2 := by
    rw [sub_sub_cancel_left, abs_neg, abs_of_pos one_half_pos]
  have h1 := line_integral_decomp n g _ hcos1 hab1 (integrable_regF_line n g hd' C d hb _ hab1)
  have h0 := line_integral_decomp n g _ hcos0 hab0 (integrable_regF_line n g hd' C d hb _ hab0)
  have hF := regF_lines_eq n g hd' C d hb hab0 hab1
  have hL : ∫ y, (chK y : ℂ) * (lineB ((n : ℝ) + 1 / 2) y - n) =
      ∫ y, ((chK y : ℂ) * (lineB ((n : ℝ) - 1 / 2) y - n) + (chK y : ℂ)) := by
    congr 1
    funext y
    rw [lineB, lineB, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  have hc0 : Integrable (fun y : ℝ => (chK y : ℂ)) := integrable_chK.ofReal
  rw [integral_add (integrable_chK_lin n _ hab0) hc0] at hL
  have hch : ∫ y, (chK y : ℂ) = 2 * π := by
    rw [integral_complex_ofReal, integral_chK, Complex.ofReal_mul, Complex.ofReal_ofNat]
  have hpi : (2 * (π : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 pi_ne_zero)
  change (1 / (2 * (π : ℂ))) * (∫ y, kerK (lineB ((n : ℝ) + 1 / 2) y) *
      g (lineB ((n : ℝ) + 1 / 2) y)) - (1 / (2 * (π : ℂ))) *
      (∫ y, kerK (lineB ((n : ℝ) - 1 / 2) y) * g (lineB ((n : ℝ) - 1 / 2) y)) = deriv g n
  rw [h1, h0, hF, hL, hch, ← mul_sub]
  field_simp
  ring

end Zeta2BarnesStep
