import Zeta2FourTrajectoryMatrices.Analytic.error_integral

open Polynomial Filter Topology Real Finset MeasureTheory Zeta2Blueprint

noncomputable section

namespace Zeta2ECBGamma

theorem rot_norm_integrand (z c : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (z - 1) * Complex.exp (-(c * t))‖ = t ^ (z.re - 1) * exp (-(c.re * t)) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp, Complex.neg_re,
    Complex.re_mul_ofReal, Complex.sub_re, Complex.one_re]

theorem rot_meas (z c : ℂ) :
    Measurable (fun t : ℝ => (t : ℂ) ^ (z - 1) * Complex.exp (-(c * t))) :=
  (Complex.measurable_ofReal.pow_const _).mul
    (measurable_const.mul Complex.measurable_ofReal).neg.cexp

theorem rot_real_int {s b : ℝ} (hs : -1 < s) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t ^ s * exp (-(b * t))) (Set.Ioi 0) :=
  (integrableOn_rpow_mul_exp_neg_mul_rpow hs one_pos hb).congr_fun
    (fun t _ => by dsimp only; rw [rpow_one, neg_mul]) measurableSet_Ioi

theorem rot_re_sub_one {z : ℂ} (hz : 0 < z.re) : -1 < z.re - 1 :=
  zero_sub (1 : ℝ) ▸ sub_lt_sub_right hz 1

theorem rot_integrableOn (z c : ℂ) (hz : 0 < z.re) (hc : 0 < c.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 1) * Complex.exp (-(c * t))) (Set.Ioi 0) :=
  Integrable.mono' (rot_real_int (rot_re_sub_one hz) hc) (rot_meas z c).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun _ ht => (rot_norm_integrand z c ht).le))

theorem rot_hasDerivAt (z : ℂ) (t : ℝ) (c : ℂ) :
    HasDerivAt (fun c : ℂ => (t : ℂ) ^ (z - 1) * Complex.exp (-(c * t)))
      ((t : ℂ) ^ (z - 1) * (Complex.exp (-(c * t)) * -(1 * t))) c :=
  (((hasDerivAt_id' c).mul_const (t : ℂ)).neg.cexp).const_mul _

theorem rot_deriv_bound (z c₀ c : ℂ) (hc : c ∈ Metric.ball c₀ (c₀.re / 2)) {t : ℝ}
    (ht : 0 < t) :
    ‖(t : ℂ) ^ (z - 1) * (Complex.exp (-(c * t)) * -(1 * t))‖ ≤
      t ^ z.re * exp (-(c₀.re / 2 * t)) := by
  have h1 : |(c - c₀).re| ≤ ‖c - c₀‖ := Complex.abs_re_le_norm _
  rw [Metric.mem_ball, dist_eq_norm] at hc
  rw [Complex.sub_re] at h1
  have h2 : c₀.re / 2 ≤ c.re := by linarith [neg_abs_le (c.re - c₀.re)]
  rw [norm_mul, norm_mul, norm_neg, one_mul, Complex.norm_real, norm_of_nonneg ht.le,
    Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp, Complex.neg_re,
    Complex.re_mul_ofReal, Complex.sub_re, Complex.one_re, mul_comm (exp _), ← mul_assoc,
    ← rpow_add_one ht.ne', sub_add_cancel]
  exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (neg_le_neg
    (mul_le_mul_of_nonneg_right h2 ht.le))) (rpow_nonneg ht.le _)

theorem rot_hasDerivAt_integral (z c₀ : ℂ) (hz : 0 < z.re) (hc : 0 < c₀.re) :
    HasDerivAt (fun c => ∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ (z - 1) * Complex.exp (-(c * t)))
      (∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ (z - 1) * (Complex.exp (-(c₀ * t)) * -(1 * t))) c₀ :=
  (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun t : ℝ => t ^ z.re * exp (-(c₀.re / 2 * t)))
    (Metric.ball_mem_nhds c₀ (half_pos hc))
    (Eventually.of_forall fun c => (rot_meas z c).aestronglyMeasurable)
    (rot_integrableOn z c₀ hz hc)
    ((Complex.measurable_ofReal.pow_const _).mul
      ((measurable_const.mul Complex.measurable_ofReal).neg.cexp.mul
        (measurable_const.mul Complex.measurable_ofReal).neg)).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun _ ht c hc' => rot_deriv_bound z c₀ c hc' ht))
    (rot_real_int ((neg_lt_zero.mpr one_pos).trans hz) (half_pos hc))
    (ae_of_all _ fun t c _ => rot_hasDerivAt z t c)).2

theorem rot_lhs_analytic (z : ℂ) (hz : 0 < z.re) :
    AnalyticOnNhd ℂ (fun c => ∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ (z - 1) * Complex.exp (-(c * t)))
      {c : ℂ | 0 < c.re} :=
  DifferentiableOn.analyticOnNhd
    (fun c hc => (rot_hasDerivAt_integral z c hz hc).differentiableAt.differentiableWithinAt)
    (isOpen_lt continuous_const Complex.continuous_re)

theorem rot_one_div_mem {c : ℂ} (hc : 0 < c.re) : 1 / c ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff, one_div, Complex.inv_re]
  exact Or.inl (div_pos hc (Complex.normSq_pos.mpr (Complex.ne_zero_of_re_pos hc)))

theorem rot_rhs_analytic (z : ℂ) :
    AnalyticOnNhd ℂ (fun c : ℂ => (1 / c) ^ z * Complex.Gamma z) {c : ℂ | 0 < c.re} :=
  DifferentiableOn.analyticOnNhd
    (fun _ hc => ((((differentiableAt_const (1 : ℂ)).div differentiableAt_id
      (Complex.ne_zero_of_re_pos hc)).cpow_const (rot_one_div_mem hc)).mul_const
        _).differentiableWithinAt)
    (isOpen_lt continuous_const Complex.continuous_re)

theorem rot_tendsto_ofReal :
    Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · exact (Complex.ofReal_one ▸ Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left
      nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact fun h => (ne_of_gt hr) (Complex.ofReal_eq_one.mp h)

theorem rot_frequently (z : ℂ) (hz : 0 < z.re) :
    ∃ᶠ c in 𝓝[≠] (1 : ℂ), (∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ (z - 1) * Complex.exp (-(c * t))) =
      (1 / c) ^ z * Complex.Gamma z := by
  refine rot_tendsto_ofReal.frequently (Eventually.frequently ?_)
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact Complex.integral_cpow_mul_exp_neg_mul_Ioi hz (lt_trans one_pos hr)

theorem rot_euler (z c : ℂ) (hz : 0 < z.re) (hc : 0 < c.re) :
    ∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ (z - 1) * Complex.exp (-(c * t)) =
      (1 / c) ^ z * Complex.Gamma z :=
  (rot_lhs_analytic z hz).eqOn_of_preconnected_of_frequently_eq (rot_rhs_analytic z)
    (convex_halfSpace_re_gt 0).isPreconnected
    (show (0 : ℝ) < (1 : ℂ).re from Complex.one_re ▸ one_pos) (rot_frequently z hz) hc

theorem rot_norm_le (z c : ℂ) (hz : 0 < z.re) (hc : 0 < c.re) :
    ‖∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ (z - 1) * Complex.exp (-(c * t))‖ ≤
      (1 / c.re) ^ z.re * Gamma z.re :=
  (norm_integral_le_integral_norm _).trans (le_of_eq
    ((setIntegral_congr_fun measurableSet_Ioi fun _ ht => rot_norm_integrand z c ht).trans
      (integral_rpow_mul_exp_neg_mul_Ioi hz hc)))

theorem rot_im_ofReal_add_mul_I (a y : ℝ) : ((a : ℂ) + y * Complex.I).im = y := by
  rw [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, Complex.I_im, mul_one, zero_add]

theorem rot_re_ofReal_add_mul_I (a y : ℝ) : ((a : ℂ) + y * Complex.I).re = a := by
  rw [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero, add_zero]

theorem rot_norm_cpow (a y φ : ℝ) (hφ : |φ| < π / 2) :
    ‖(1 / Complex.exp (φ * Complex.I)) ^ ((a : ℂ) + y * Complex.I)‖ = exp (φ * y) := by
  have h := abs_lt.mp hφ
  have harg : Complex.arg (Complex.exp ((-φ : ℝ) * Complex.I)) = -φ := by
    rw [Complex.arg_exp_mul_I, toIocMod_eq_self]
    constructor <;> linarith [pi_pos]
  rw [one_div, ← Complex.exp_neg, ← neg_mul, ← Complex.ofReal_neg,
    Complex.norm_cpow_of_ne_zero (Complex.exp_ne_zero _), Complex.norm_exp_ofReal_mul_I, one_rpow,
    harg, rot_im_ofReal_add_mul_I, one_div, ← exp_neg, neg_mul, neg_neg]

theorem rot_bound_phi (a y φ : ℝ) (ha : 0 < a) (hφ : |φ| < π / 2) :
    ‖Complex.Gamma (a + y * Complex.I)‖ ≤ Gamma a * (cos φ) ^ (-a) * exp (-(φ * y)) := by
  have hcos : 0 < cos φ := cos_pos_of_mem_Ioo ⟨(abs_lt.mp hφ).1, (abs_lt.mp hφ).2⟩
  have hz : 0 < ((a : ℂ) + y * Complex.I).re := (rot_re_ofReal_add_mul_I a y).symm ▸ ha
  have hc : 0 < (Complex.exp (φ * Complex.I)).re := (Complex.exp_ofReal_mul_I_re φ).symm ▸ hcos
  have hG := rot_norm_le _ _ hz hc
  rw [rot_euler _ _ hz hc, norm_mul, rot_norm_cpow a y φ hφ, rot_re_ofReal_add_mul_I,
    Complex.exp_ofReal_mul_I_re, one_div, inv_rpow hcos.le, ← rpow_neg hcos.le] at hG
  calc ‖Complex.Gamma (a + y * Complex.I)‖
      = exp (-(φ * y)) * (exp (φ * y) * ‖Complex.Gamma (a + y * Complex.I)‖) := by
        rw [← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul]
    _ ≤ exp (-(φ * y)) * (cos φ ^ (-a) * Gamma a) := mul_le_mul_of_nonneg_left hG (exp_pos _).le
    _ = Gamma a * cos φ ^ (-a) * exp (-(φ * y)) := by
        rw [mul_comm, mul_comm (cos φ ^ (-a))]

theorem gamma_rotation_bound_core (a y θ : ℝ) (ha : 0 < a) (hθ₀ : 0 < θ) (hθ : θ < π / 2) :
    ‖Complex.Gamma (a + y * Complex.I)‖ ≤ Gamma a * (cos θ) ^ (-a) * exp (-θ * |y|) := by
  rcases le_total 0 y with hy | hy
  · have h := rot_bound_phi a y θ ha ((abs_of_pos hθ₀).symm ▸ hθ)
    rwa [abs_of_nonneg hy, neg_mul]
  · have h := rot_bound_phi a y (-θ) ha ((abs_neg θ).symm ▸ (abs_of_pos hθ₀).symm ▸ hθ)
    rw [cos_neg, neg_mul, neg_neg] at h
    rwa [abs_of_nonpos hy, neg_mul_neg]

end Zeta2ECBGamma
