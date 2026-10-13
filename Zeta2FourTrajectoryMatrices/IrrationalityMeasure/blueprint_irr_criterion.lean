import Zeta2FourTrajectoryMatrices.Blueprint.defs

open Filter Topology Real Finset Zeta2Blueprint

noncomputable section

namespace Zeta2IrrCriterion

theorem finite_of_bounds (α : ℝ) (S : Set (ℤ × ℕ)) (B : ℕ)
    (hS : ∀ q ∈ S, 0 < q.2 ∧ q.2 ≤ B ∧ |α - q.1 / q.2| < 1) : S.Finite := by
  set M : ℤ := ⌈(B : ℝ) * (|α| + 1)⌉ with hM
  have hbound : ∀ q ∈ S, |q.1| ≤ M := by
    intro q hq
    obtain ⟨h0, hB, h1⟩ := hS q hq
    have hb : (0 : ℝ) < q.2 := by exact_mod_cast h0
    have hbB : (q.2 : ℝ) ≤ B := by exact_mod_cast hB
    have h2 : |(q.1 : ℝ) / q.2| ≤ |α| + 1 := by
      have := abs_sub_abs_le_abs_sub ((q.1 : ℝ) / q.2) α
      rw [abs_sub_comm] at this
      linarith
    rw [abs_div, abs_of_pos hb, div_le_iff₀ hb] at h2
    have h3 : |(q.1 : ℝ)| ≤ (B : ℝ) * (|α| + 1) := by
      rw [mul_comm]
      exact h2.trans (mul_le_mul_of_nonneg_left hbB (by positivity : (0 : ℝ) ≤ |α| + 1))
    have h4 : ((|q.1| : ℤ) : ℝ) ≤ (M : ℝ) := by
      rw [Int.cast_abs]
      exact h3.trans (Int.le_ceil _)
    exact_mod_cast h4
  refine Set.Finite.subset (Finset.finite_toSet (Icc (-M) M ×ˢ Icc 1 B)) fun q hq => ?_
  rw [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_coe, Finset.mem_Icc,
    Finset.mem_Icc]
  exact ⟨abs_le.1 (hbound q hq), (hS q hq).1, (hS q hq).2.1⟩

theorem delta_pos (σ τ ε : ℝ) (hσ : 0 ≤ σ) (hτ : 0 < τ) (hε : 0 < ε) :
    0 < ε * τ ^ 2 / (2 * τ + 2 * σ + ε * τ) ∧ ε * τ ^ 2 / (2 * τ + 2 * σ + ε * τ) < τ ∧
      σ + ε * τ ^ 2 / (2 * τ + 2 * σ + ε * τ) =
        (σ / τ + ε / 2) * (τ - ε * τ ^ 2 / (2 * τ + 2 * σ + ε * τ)) := by
  have hden : 0 < 2 * τ + 2 * σ + ε * τ := by positivity
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_lt_iff₀ hden]
    nlinarith [mul_pos hτ hτ, mul_nonneg hτ.le hσ]
  · field_simp
    ring

theorem key_bound (α σ τ : ℝ) (hσ : 0 ≤ σ) (hτ : 0 < τ) (P Q : ℕ → ℤ)
    (hQ : ∀ ε > 0, ∀ᶠ N : ℕ in atTop, |(Q N : ℝ)| ≤ exp ((σ + ε) * N))
    (hE : ∀ ε > 0, ∀ᶠ N : ℕ in atTop, |(Q N : ℝ) * α - P N| ≤ exp ((-τ + ε) * N))
    (hgap : ∀ᶠ N : ℕ in atTop, ∀ (a : ℤ) (b : ℕ), 0 < b →
      ∃ i : Fin 3, (b : ℤ) * P (N + i) - a * Q (N + i) ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, ∀ (a : ℤ) (b : ℕ), 0 < b → |α - a / b| < (b : ℝ) ^ (-(1 + σ / τ + ε)) →
      (b : ℝ) ^ (ε / 2) ≤ B := by
  obtain ⟨hδ0, hδτ, hθ⟩ := delta_pos σ τ ε hσ hτ hε
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = σ / τ + ε / 2 := ⟨_, rfl⟩
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ε * τ ^ 2 / (2 * τ + 2 * σ + ε * τ) := ⟨_, rfl⟩
  rw [← hθdef, ← hδdef] at hθ
  rw [← hδdef] at hδ0 hδτ
  have hθ0 : 0 ≤ θ := by rw [hθdef]; positivity
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 ((hQ δ hδ0).and ((hE δ hδ0).and hgap))
  set K : ℝ := exp ((σ + δ) * (n₀ + 3)) with hK
  refine ⟨2 * K * (2 : ℝ) ^ θ, fun a b hb happ => ?_⟩
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hlog : 0 ≤ Real.log (2 * b) := Real.log_nonneg (by linarith)
  set L : ℝ := Real.log (2 * b) / (τ - δ) with hL
  have hL0 : 0 ≤ L := div_nonneg hlog (by linarith)
  obtain ⟨i, hi⟩ := (hn₀ (n₀ + ⌈L⌉₊) (by omega)).2.2 a b hb
  set N : ℕ := n₀ + ⌈L⌉₊ + i with hN
  obtain ⟨hQN, hEN, -⟩ := hn₀ N (by omega)
  have hNL : L ≤ N := by
    have h1 : (⌈L⌉₊ : ℝ) ≤ N := by exact_mod_cast (show ⌈L⌉₊ ≤ N by omega)
    exact (Nat.le_ceil L).trans h1
  have hNU : (N : ℝ) ≤ n₀ + L + 3 := by
    have h1 : (N : ℝ) = n₀ + ⌈L⌉₊ + (i : ℕ) := by rw [hN]; push_cast; rfl
    have h2 : (⌈L⌉₊ : ℝ) < L + 1 := Nat.ceil_lt_add_one hL0
    have h3 : ((i : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (show (i : ℕ) ≤ 2 by omega)
    linarith
  have hE1 : exp ((-τ + δ) * N) ≤ 1 / (2 * b) := by
    rw [show (1 : ℝ) / (2 * b) = exp (-Real.log (2 * b)) by
      rw [Real.exp_neg, Real.exp_log (by linarith), one_div]]
    refine Real.exp_le_exp.2 ?_
    have : Real.log (2 * b) = (τ - δ) * L := by
      rw [hL, mul_div_cancel₀ _ (by linarith)]
    rw [this]
    nlinarith
  have hQ1 : exp ((σ + δ) * N) ≤ K * (2 * b) ^ θ := by
    rw [Real.rpow_def_of_pos (by linarith), hK, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have : Real.log (2 * b) * θ = (σ + δ) * L := by
      rw [hθ, hL, mul_assoc, mul_div_cancel₀ _ (by linarith)]
      ring
    rw [this]
    nlinarith [add_nonneg hσ hδ0.le]
  have h1 : (1 : ℝ) ≤ |(b : ℝ) * P N - a * Q N| := by
    have := Int.one_le_abs hi
    have h' : ((1 : ℤ) : ℝ) ≤ ((|(b : ℤ) * P (N) - a * Q (N)| : ℤ) : ℝ) := by
      rw [hN]; exact_mod_cast this
    rw [Int.cast_abs] at h'
    push_cast at h'
    exact h'
  have h2 : |(b : ℝ) * P N - a * Q N| ≤
      b * |(Q N : ℝ) * α - P N| + |(Q N : ℝ)| * (b * |α - a / b|) := by
    have hid : (b : ℝ) * P N - a * Q N =
        -(b * ((Q N : ℝ) * α - P N)) + Q N * (b * (α - a / b)) := by
      field_simp
      ring
    rw [hid]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg, abs_mul, abs_mul, abs_mul, abs_of_pos hb0]
  have h3 : (1 : ℝ) / 2 ≤ |(Q N : ℝ)| * (b * |α - a / b|) := by
    have h4 : (b : ℝ) * |(Q N : ℝ) * α - P N| ≤ 1 / 2 := by
      calc (b : ℝ) * |(Q N : ℝ) * α - P N| ≤ b * (1 / (2 * b)) :=
            mul_le_mul_of_nonneg_left (hEN.trans hE1) hb0.le
        _ = 1 / 2 := by field_simp
    linarith
  have h5 : |(Q N : ℝ)| * (b * |α - a / b|) ≤ K * (2 : ℝ) ^ θ * (b : ℝ) ^ (-(ε / 2)) := by
    have hpow : (b : ℝ) ^ θ * (b * (b : ℝ) ^ (-(1 + σ / τ + ε))) = (b : ℝ) ^ (-(ε / 2)) := by
      calc (b : ℝ) ^ θ * (b * (b : ℝ) ^ (-(1 + σ / τ + ε)))
          = (b : ℝ) ^ θ * ((b : ℝ) ^ (-(1 + σ / τ + ε)) * b) := by ring
        _ = (b : ℝ) ^ θ * (b : ℝ) ^ (-(1 + σ / τ + ε) + 1) := by rw [Real.rpow_add_one hb0.ne']
        _ = (b : ℝ) ^ (θ + (-(1 + σ / τ + ε) + 1)) := (Real.rpow_add hb0 _ _).symm
        _ = (b : ℝ) ^ (-(ε / 2)) := by
          congr 1
          rw [hθdef]
          ring
    calc |(Q N : ℝ)| * (b * |α - a / b|)
        ≤ (K * (2 * b) ^ θ) * (b * (b : ℝ) ^ (-(1 + σ / τ + ε))) :=
          mul_le_mul (hQN.trans hQ1) (mul_le_mul_of_nonneg_left happ.le hb0.le) (by positivity)
            (by positivity)
      _ = K * (2 : ℝ) ^ θ * ((b : ℝ) ^ θ * (b * (b : ℝ) ^ (-(1 + σ / τ + ε)))) := by
          rw [Real.mul_rpow (by norm_num) hb0.le]
          ring
      _ = K * (2 : ℝ) ^ θ * (b : ℝ) ^ (-(ε / 2)) := by rw [hpow]
  have h6 : (b : ℝ) ^ (ε / 2) * (b : ℝ) ^ (-(ε / 2)) = 1 := by
    rw [← Real.rpow_add hb0, add_neg_cancel, Real.rpow_zero]
  have h7 : (0 : ℝ) < (b : ℝ) ^ (-(ε / 2)) := Real.rpow_pos_of_pos hb0 _
  have h8 : (1 : ℝ) / 2 ≤ K * (2 : ℝ) ^ θ * (b : ℝ) ^ (-(ε / 2)) := h3.trans h5
  have h9 : (b : ℝ) ^ (ε / 2) * (1 / 2) ≤
      (b : ℝ) ^ (ε / 2) * (K * (2 : ℝ) ^ θ * (b : ℝ) ^ (-(ε / 2))) :=
    mul_le_mul_of_nonneg_left h8 (Real.rpow_nonneg hb0.le _)
  rw [show (b : ℝ) ^ (ε / 2) * (K * (2 : ℝ) ^ θ * (b : ℝ) ^ (-(ε / 2))) =
    K * (2 : ℝ) ^ θ * ((b : ℝ) ^ (ε / 2) * (b : ℝ) ^ (-(ε / 2))) by ring, h6, mul_one] at h9
  linarith

theorem irrMeasure_criterion (α σ τ : ℝ) (hσ : 0 ≤ σ) (hτ : 0 < τ) (P Q : ℕ → ℤ)
    (hQ : ∀ ε > 0, ∀ᶠ N : ℕ in atTop, |(Q N : ℝ)| ≤ exp ((σ + ε) * N))
    (hE : ∀ ε > 0, ∀ᶠ N : ℕ in atTop, |(Q N : ℝ) * α - P N| ≤ exp ((-τ + ε) * N))
    (hgap : ∀ᶠ N : ℕ in atTop, ∀ (a : ℤ) (b : ℕ), 0 < b →
      ∃ i : Fin 3, (b : ℤ) * P (N + i) - a * Q (N + i) ≠ 0) :
    IrrMeasureLE α (1 + σ / τ) := by
  intro ε hε
  obtain ⟨B, hB⟩ := key_bound α σ τ hσ hτ P Q hQ hE hgap ε hε
  have hT : {x : ℤ × ℕ | 0 < x.2 ∧ |α - x.1 / x.2| < (x.2 : ℝ) ^ (-(1 + σ / τ + ε))}.Finite := by
    refine finite_of_bounds α _ ⌈B ^ (2 / ε)⌉₊ fun q hq => ?_
    obtain ⟨hq0, hq1⟩ := hq
    have hb0 : (0 : ℝ) < q.2 := by exact_mod_cast hq0
    have hb1 : (1 : ℝ) ≤ q.2 := by exact_mod_cast hq0
    refine ⟨hq0, ?_, ?_⟩
    · have h1 := hB q.1 q.2 hq0 hq1
      have h2 : (q.2 : ℝ) ≤ B ^ (2 / ε) := by
        have h3 : ((q.2 : ℝ) ^ (ε / 2)) ^ (2 / ε) ≤ B ^ (2 / ε) :=
          Real.rpow_le_rpow (Real.rpow_nonneg hb0.le _) h1 (by positivity)
        rwa [← Real.rpow_mul hb0.le, show ε / 2 * (2 / ε) = 1 by field_simp, Real.rpow_one] at h3
      exact_mod_cast h2.trans (Nat.le_ceil _)
    · refine hq1.trans_le (Real.rpow_le_one_of_one_le_of_nonpos hb1 ?_)
      have : 0 ≤ 1 + σ / τ + ε := by positivity
      linarith
  refine (hT.image fun x : ℤ × ℕ => (x.1 : ℚ) / x.2).subset fun q hq =>
    ⟨(q.num, q.den), ⟨q.den_pos, ?_⟩, ?_⟩
  · rw [← Rat.cast_def]
    exact hq
  · exact Rat.num_div_den q

end Zeta2IrrCriterion
