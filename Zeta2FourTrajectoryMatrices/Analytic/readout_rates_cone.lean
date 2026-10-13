import Zeta2FourTrajectoryMatrices.Analytic.blueprint_bounded_gap

open Polynomial Filter Topology Real Finset Zeta2Blueprint Zeta2BoundedGap
open scoped Matrix

noncomputable section

namespace Zeta2Cone

def HL (Λ : ℝ) : Prop := 17400086428 < Λ ∧ Λ < 17400086429 ∧ aeval (-Λ) Ainf.charpoly = 0 ∧
  (Zeta2LimitSpectrum.c0 : ℝ) / Λ < 1

def Ai : Matrix (Fin 3) (Fin 3) ℝ := rc Ainf

def bt (Λ : ℝ) : ℝ := (Zeta2LimitSpectrum.c2 : ℝ) - Λ

def gm (Λ : ℝ) : ℝ := (Zeta2LimitSpectrum.c0 : ℝ) / Λ

def mu (Λ : ℝ) : ℝ := Λ ^ 2 - bt Λ * Λ + gm Λ

def Mm (Λ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := Ai * Ai + bt Λ • Ai + gm Λ • 1

def Pm (Λ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := (mu Λ)⁻¹ • Mm Λ

def Qm (Λ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := 1 - Pm Λ

def sc (Λ : ℝ) : ℝ := Real.sqrt (gm Λ - bt Λ ^ 2 / 4)

def Mt (Λ : ℝ) : Matrix (Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  Matrix.fromCols (Ai + (bt Λ / 2) • 1) (sc Λ • 1)

def Tp (Λ : ℝ) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) := Matrix.vecMulLinear (Pm Λ)

def Tq (Λ : ℝ) : (Fin 3 → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3 ⊕ Fin 3) :=
  (WithLp.linearEquiv 2 ℝ (Fin 3 ⊕ Fin 3 → ℝ)).symm.toLinearMap ∘ₗ
    Matrix.vecMulLinear (Qm Λ * Mt Λ)

theorem one_lt_lam {Λ : ℝ} (h : HL Λ) : 1 < Λ := lt_trans (by norm_num) h.1

theorem ch_Ai : Ai * (Ai * Ai) + (Zeta2LimitSpectrum.c2 : ℝ) • (Ai * Ai) +
    (Zeta2LimitSpectrum.c1 : ℝ) • Ai + (Zeta2LimitSpectrum.c0 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
    = 0 := by
  have h := Matrix.aeval_self_charpoly Ai
  rw [Ai, rc, RingHom.mapMatrix_apply, Matrix.charpoly_map, Zeta2LimitSpectrum.charpoly_Ainf] at h
  simp only [Polynomial.map_add, Polynomial.map_mul, map_X, map_C, map_add,
    map_mul, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    pow_three, sq, eq_ratCast] at h
  exact h

theorem root_rel {Λ : ℝ} (h : HL Λ) : (Zeta2LimitSpectrum.c1 : ℝ) = gm Λ + Λ * bt Λ ∧
    (Zeta2LimitSpectrum.c0 : ℝ) = Λ * gm Λ ∧ (Zeta2LimitSpectrum.c2 : ℝ) = bt Λ + Λ := by
  have hΛ : Λ ≠ 0 := (zero_lt_one.trans (one_lt_lam h)).ne'
  have hg : Zeta2LimitSpectrum.g Λ = 0 :=
    neg_eq_zero.1 ((Zeta2LimitSpectrum.aeval_charpoly Λ).symm.trans h.2.2.1)
  have h0 : (Zeta2LimitSpectrum.c0 : ℝ) = Λ * gm Λ := (mul_div_cancel₀ _ hΛ).symm
  refine ⟨mul_left_cancel₀ hΛ ?_, h0, (sub_add_cancel _ _).symm⟩
  rw [Zeta2LimitSpectrum.g] at hg
  rw [bt, mul_add, ← h0]
  linear_combination hg

theorem AM {Λ : ℝ} (h : HL Λ) : Ai * Mm Λ = -Λ • Mm Λ := by
  obtain ⟨h1, h0, h2⟩ := root_rel h
  have hc := ch_Ai
  rw [h1, h0, h2] at hc
  rw [← sub_eq_zero, ← hc, Mm, mul_add, mul_add, mul_smul_comm, mul_smul_comm, mul_one]
  module

theorem MA (Λ : ℝ) : Mm Λ * Ai = Ai * Mm Λ := by
  rw [Mm, add_mul, add_mul, mul_add, mul_add, smul_mul_assoc, smul_mul_assoc, mul_smul_comm,
    mul_smul_comm, one_mul, mul_one, mul_assoc]

theorem MM {Λ : ℝ} (h : HL Λ) : Mm Λ * Mm Λ = mu Λ • Mm Λ := by
  have e : Mm Λ * Mm Λ = Ai * (Ai * Mm Λ) + bt Λ • (Ai * Mm Λ) + gm Λ • Mm Λ := by
    nth_rewrite 1 [Mm]
    rw [add_mul, add_mul, mul_assoc, smul_mul_assoc, smul_mul_assoc, one_mul]
  rw [e, AM h, mul_smul_comm, AM h, mu]
  module

theorem disc_fact {Λ : ℝ} (h : HL Λ) : bt Λ ^ 2 - 4 * gm Λ < 0 ∧ mu Λ ≠ 0 := by
  obtain ⟨h1, h0, h2⟩ := root_rel h
  have hd : 18 * (Zeta2LimitSpectrum.c2 : ℝ) * Zeta2LimitSpectrum.c1 * Zeta2LimitSpectrum.c0 -
      4 * (Zeta2LimitSpectrum.c2 : ℝ) ^ 3 * Zeta2LimitSpectrum.c0 +
      (Zeta2LimitSpectrum.c2 : ℝ) ^ 2 * (Zeta2LimitSpectrum.c1 : ℝ) ^ 2 -
      4 * (Zeta2LimitSpectrum.c1 : ℝ) ^ 3 - 27 * (Zeta2LimitSpectrum.c0 : ℝ) ^ 2 < 0 := by
    exact_mod_cast Zeta2LimitSpectrum.disc_neg
  have e : ∀ b g L : ℝ, 18 * (b + L) * (g + L * b) * (L * g) - 4 * (b + L) ^ 3 * (L * g) +
      (b + L) ^ 2 * (g + L * b) ^ 2 - 4 * (g + L * b) ^ 3 - 27 * (L * g) ^ 2 =
      (b ^ 2 - 4 * g) * (L ^ 2 - b * L + g) ^ 2 := fun b g L => by ring
  rw [h1, h0, h2, e, ← mu] at hd
  refine ⟨Left.neg_of_mul_neg_left hd (sq_nonneg _), fun hm => ?_⟩
  rw [hm, zero_pow two_ne_zero, mul_zero] at hd
  exact lt_irrefl 0 hd

theorem gm_pos {Λ : ℝ} (h : HL Λ) : 0 < gm Λ := by
  have := (disc_fact h).1
  nlinarith [sq_nonneg (bt Λ)]

theorem sc_pos {Λ : ℝ} (h : HL Λ) : 0 < sc Λ := by
  have := (disc_fact h).1
  exact Real.sqrt_pos.2 (by linarith)

theorem sc_sq {Λ : ℝ} (h : HL Λ) : sc Λ ^ 2 = gm Λ - bt Λ ^ 2 / 4 := by
  have := (disc_fact h).1
  exact Real.sq_sqrt (by linarith)

theorem PA {Λ : ℝ} (h : HL Λ) : Pm Λ * Ai = -Λ • Pm Λ := by
  rw [Pm, smul_mul_assoc, MA, AM h, smul_comm]

theorem AP {Λ : ℝ} (h : HL Λ) : Ai * Pm Λ = -Λ • Pm Λ := by
  rw [Pm, mul_smul_comm, AM h, smul_comm]

theorem QA {Λ : ℝ} (h : HL Λ) : Qm Λ * Ai = Ai * Qm Λ := by
  rw [Qm, sub_mul, mul_sub, one_mul, mul_one, PA h, AP h]

theorem QM {Λ : ℝ} (h : HL Λ) : Qm Λ * Mm Λ = 0 := by
  rw [Qm, Pm, sub_mul, one_mul, smul_mul_assoc, MM h, smul_smul, inv_mul_cancel₀ (disc_fact h).2,
    one_smul, sub_self]

theorem Tp_scale {Λ : ℝ} (h : HL Λ) (y : Fin 3 → ℝ) : ‖Tp Λ (y ᵥ* Ai)‖ = Λ * ‖Tp Λ y‖ := by
  change ‖y ᵥ* Ai ᵥ* Pm Λ‖ = Λ * ‖y ᵥ* Pm Λ‖
  rw [Matrix.vecMul_vecMul, AP h, Matrix.vecMul_smul, norm_smul, norm_neg, Real.norm_eq_abs,
    abs_of_pos (zero_lt_one.trans (one_lt_lam h))]

theorem Mt_sq (Λ : ℝ) (v : Fin 3 → ℝ) :
    ‖(WithLp.toLp 2 (v ᵥ* Mt Λ) : EuclideanSpace ℝ (Fin 3 ⊕ Fin 3))‖ ^ 2 =
      ∑ i, ((v ᵥ* Ai) i + bt Λ / 2 * v i) ^ 2 + ∑ i, (sc Λ * v i) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type]
  simp only [Mt, Matrix.vecMul_fromCols, Sum.elim_inl, Sum.elim_inr,
    Matrix.vecMul_add, Matrix.vecMul_smul, Matrix.vecMul_one, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]

theorem Mt_inr (Λ : ℝ) (v : Fin 3 → ℝ) (i : Fin 3) : (v ᵥ* Mt Λ) (Sum.inr i) = sc Λ * v i := by
  rw [Mt, Matrix.vecMul_fromCols, Sum.elim_inr, Matrix.vecMul_smul, Matrix.vecMul_one]
  rfl

theorem Mt_low {Λ : ℝ} (h : HL Λ) (v : Fin 3 → ℝ) :
    ‖v‖ ≤ ‖(WithLp.toLp 2 (v ᵥ* Mt Λ) : EuclideanSpace ℝ (Fin 3 ⊕ Fin 3))‖ / sc Λ := by
  refine (pi_norm_le_iff_of_nonneg (div_nonneg (norm_nonneg _) (sc_pos h).le)).2 fun i => ?_
  rw [le_div_iff₀ (sc_pos h)]
  have hi := PiLp.norm_apply_le
    (WithLp.toLp 2 (v ᵥ* Mt Λ) : EuclideanSpace ℝ (Fin 3 ⊕ Fin 3)) (Sum.inr i)
  rw [PiLp.toLp_apply, Mt_inr, norm_mul, Real.norm_eq_abs (sc Λ), abs_of_pos (sc_pos h)] at hi
  rw [mul_comm]
  exact hi

theorem core_quad {Λ : ℝ} (h : HL Λ) (w : Fin 3 → ℝ) (hw : w ᵥ* Mm Λ = 0) :
    ‖(WithLp.toLp 2 (w ᵥ* Ai ᵥ* Mt Λ) : EuclideanSpace ℝ (Fin 3 ⊕ Fin 3))‖ =
      Real.sqrt (gm Λ) * ‖(WithLp.toLp 2 (w ᵥ* Mt Λ) : EuclideanSpace ℝ (Fin 3 ⊕ Fin 3))‖ := by
  have hs := sc_sq h
  rw [Mm, Matrix.vecMul_add, Matrix.vecMul_add, Matrix.vecMul_smul, Matrix.vecMul_smul,
    Matrix.vecMul_one, ← Matrix.vecMul_vecMul] at hw
  have e : ‖(WithLp.toLp 2 (w ᵥ* Ai ᵥ* Mt Λ) : EuclideanSpace ℝ (Fin 3 ⊕ Fin 3))‖ ^ 2 =
      gm Λ * ‖(WithLp.toLp 2 (w ᵥ* Mt Λ) : EuclideanSpace ℝ (Fin 3 ⊕ Fin 3))‖ ^ 2 := by
    rw [Mt_sq, Mt_sq, mul_add, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    have hi := congrFun hw i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
    linear_combination ((w ᵥ* Ai ᵥ* Ai) i - gm Λ * w i) * hi +
      ((w ᵥ* Ai) i ^ 2 - gm Λ * w i ^ 2) * hs
  rw [← Real.sqrt_sq (norm_nonneg _), e, Real.sqrt_mul (gm_pos h).le, Real.sqrt_sq (norm_nonneg _)]

theorem Tq_scale {Λ : ℝ} (h : HL Λ) (y : Fin 3 → ℝ) :
    ‖Tq Λ (y ᵥ* Ai)‖ = Real.sqrt (gm Λ) * ‖Tq Λ y‖ := by
  change ‖(WithLp.toLp 2 (y ᵥ* Ai ᵥ* (Qm Λ * Mt Λ)) : EuclideanSpace ℝ (Fin 3 ⊕ Fin 3))‖ =
    Real.sqrt (gm Λ) * ‖(WithLp.toLp 2 (y ᵥ* (Qm Λ * Mt Λ)) : EuclideanSpace ℝ (Fin 3 ⊕ Fin 3))‖
  rw [Matrix.vecMul_vecMul, ← Matrix.mul_assoc, ← QA h, Matrix.mul_assoc, ← Matrix.vecMul_vecMul,
    ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]
  exact core_quad h _ (by rw [Matrix.vecMul_vecMul, QM h, Matrix.vecMul_zero])

theorem norm_split {Λ : ℝ} (h : HL Λ) (x : Fin 3 → ℝ) :
    ‖x‖ ≤ (1 + (sc Λ)⁻¹) * (‖Tp Λ x‖ + ‖Tq Λ x‖) := by
  have hx : x = x ᵥ* Pm Λ + x ᵥ* Qm Λ := by
    rw [Qm, Matrix.vecMul_sub, Matrix.vecMul_one, add_sub_cancel]
  have h1 := Mt_low h (x ᵥ* Qm Λ)
  rw [Matrix.vecMul_vecMul] at h1
  have h2 : ‖x‖ ≤ ‖Tp Λ x‖ + ‖Tq Λ x‖ / sc Λ :=
    calc ‖x‖ = ‖x ᵥ* Pm Λ + x ᵥ* Qm Λ‖ := congrArg _ hx
      _ ≤ ‖x ᵥ* Pm Λ‖ + ‖x ᵥ* Qm Λ‖ := norm_add_le _ _
      _ ≤ ‖Tp Λ x‖ + ‖Tq Λ x‖ / sc Λ := add_le_add_right h1 _
  have h3 : 0 ≤ ‖Tq Λ x‖ + ‖Tp Λ x‖ * (sc Λ)⁻¹ :=
    add_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (inv_nonneg.2 (sc_pos h).le))
  rw [div_eq_mul_inv] at h2
  linarith

end Zeta2Cone
