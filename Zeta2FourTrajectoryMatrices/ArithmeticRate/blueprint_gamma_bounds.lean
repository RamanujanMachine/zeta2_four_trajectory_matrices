import Zeta2FourTrajectoryMatrices.ArithmeticRate.blueprint_gamma_int

open MeasureTheory Set Filter Topology Finset Zeta2Blueprint Zeta2GammaCore Zeta2GammaTable
  Zeta2GammaSum Zeta2GammaInt

noncomputable section

namespace Zeta2GammaBounds

theorem cross_lt : ∀ i, i < 94 → an i * ad (i + 1) < an (i + 1) * ad i := by decide +kernel

theorem an_pos : ∀ i, i < 94 → hv i ≠ 0 → 0 < an i := by decide +kernel

theorem an_succ_pos : ∀ i, i < 94 → hv i ≠ 0 → 0 < an (i + 1) := by decide +kernel

theorem count53 : ∑ i ∈ range 94, (if hv i = 0 then (0 : ℕ) else 1) = 53 := by decide +kernel

theorem nat_div_bounds (m n : ℕ) (hn : 0 < n) :
    ((m / n : ℕ) : ℝ) ≤ (m : ℝ) / n ∧ (m : ℝ) / n < ((m / n : ℕ) : ℝ) + 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨Nat.cast_div_le, ?_⟩
  rw [div_lt_iff₀ hn']
  have h1 : (m : ℝ) = n * ((m / n : ℕ) : ℝ) + ((m % n : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod m n).symm
  have h2 : ((m % n : ℕ) : ℝ) < n := by exact_mod_cast Nat.mod_lt m hn
  linarith

theorem realTerm_eq (k i : ℕ) (hi : i < 94) (h : hv i ≠ 0) :
    realTerm k i = ((hvN i * (an (i + 1) * ad i - an i * ad (i + 1)) : ℕ) : ℝ) /
      (((k * ad i + an i) * (k * ad (i + 1) + an (i + 1)) : ℕ) : ℝ) := by
  have hc1 : cutR i = (an i : ℝ) / ad i := by
    rw [cutR, cut_eq_div i (by omega)]
    push_cast
    rfl
  have hc2 : cutR (i + 1) = (an (i + 1) : ℝ) / ad (i + 1) := by
    rw [cutR, cut_eq_div (i + 1) (by omega)]
    push_cast
    rfl
  have hh : hvR i = (hvN i : ℝ) := by
    rw [hvR, hv_eq i hi]
    push_cast
    rfl
  have had1 : (0 : ℝ) < ad i := by exact_mod_cast ad_pos i (by omega)
  have had2 : (0 : ℝ) < ad (i + 1) := by exact_mod_cast ad_pos (i + 1) (by omega)
  have han : (0 : ℝ) < an i := by exact_mod_cast an_pos i hi h
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hcr : (an i * ad (i + 1) : ℝ) ≤ an (i + 1) * ad i := by
    exact_mod_cast (cross_lt i hi).le
  rw [realTerm, hc1, hc2, hh]
  push_cast [Nat.cast_sub (cross_lt i hi).le]
  have hd1 : (k : ℝ) * ad i + an i ≠ 0 := by positivity
  have hd2 : (k : ℝ) * ad (i + 1) + an (i + 1) ≠ 0 := by
    have : (0 : ℝ) < an (i + 1) := by exact_mod_cast an_succ_pos i hi h
    positivity
  field_simp
  ring

theorem idxTerm_bounds (k i : ℕ) (hi : i < 94) :
    ((idxTerm k i : ℕ) : ℝ) / 10 ^ 15 ≤ realTerm k i ∧
      realTerm k i ≤ (((idxTerm k i : ℕ) : ℝ) + (if hv i = 0 then 0 else 1)) / 10 ^ 15 := by
  by_cases h : hv i = 0
  · have hN : hvN i = 0 := by
      have := hv_eq i hi
      rw [h] at this
      exact_mod_cast this.symm
    simp [idxTerm, natTerm, numI, hN, realTerm, hvR, h]
  · simp only [h, ↓reduceIte]
    rw [realTerm_eq k i hi h]
    obtain ⟨N, hN⟩ : ∃ N : ℕ, N = hvN i * (an (i + 1) * ad i - an i * ad (i + 1)) := ⟨_, rfl⟩
    obtain ⟨D, hD⟩ : ∃ D : ℕ, D = (k * ad i + an i) * (k * ad (i + 1) + an (i + 1)) := ⟨_, rfl⟩
    have hDpos : 0 < D := by
      rw [hD]
      exact Nat.mul_pos (Nat.add_pos_right _ (an_pos i hi h))
        (Nat.add_pos_right _ (an_succ_pos i hi h))
    have hidx : idxTerm k i = (10 ^ 15 * N) / D := by
      rw [idxTerm, natTerm, numI, hN, hD]
    rw [← hN, ← hD, hidx]
    obtain ⟨h1, h2⟩ := nat_div_bounds (10 ^ 15 * N) D hDpos
    have hD' : (0 : ℝ) < D := by exact_mod_cast hDpos
    have e : (((10 ^ 15 * N : ℕ)) : ℝ) / D = 10 ^ 15 * ((N : ℝ) / D) := by
      push_cast
      ring
    rw [e] at h1 h2
    constructor
    · rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 15)]
      linarith
    · rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 15)]
      linarith

theorem sum_bridge :
    (12127998763267375 : ℝ) / 10 ^ 15 ≤ ∑ k ∈ range 2000, ∑ i ∈ range 94, realTerm k i ∧
      ∑ k ∈ range 2000, ∑ i ∈ range 94, realTerm k i ≤
        ((12127998763267375 : ℝ) + 2000 * 53) / 10 ^ 15 := by
  have hT : ((∑ k ∈ range 2000, periodNat k : ℕ) : ℝ) = 12127998763267375 := by
    rw [total_eq]
    push_cast
    rfl
  have hP : ∀ k, ((periodNat k : ℕ) : ℝ) = ∑ i ∈ range 94, ((idxTerm k i : ℕ) : ℝ) := fun k => by
    rw [periodNat_eq]
    push_cast
    rfl
  have hC : ∑ i ∈ range 94, (if hv i = 0 then (0 : ℝ) else 1) = 53 := by
    have := count53
    have h' : ((∑ i ∈ range 94, (if hv i = 0 then (0 : ℕ) else 1) : ℕ) : ℝ) = ((53 : ℕ) : ℝ) := by
      rw [this]
    push_cast at h'
    exact h'
  rw [← hT, Nat.cast_sum, Finset.sum_div]
  constructor
  · refine Finset.sum_le_sum fun k _ => ?_
    rw [hP, Finset.sum_div]
    exact Finset.sum_le_sum fun i hi => (idxTerm_bounds k i (mem_range.1 hi)).1
  · rw [show ((2000 : ℝ) * 53) = ∑ k ∈ range 2000, (53 : ℝ) by
      rw [Finset.sum_const, Finset.card_range]; simp, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [hP, ← hC, ← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_le_sum fun i hi => (idxTerm_bounds k i (mem_range.1 hi)).2

theorem gamma_bounds :
    (159010385641752609841 / 13110552000000000000 : ℝ) ≤ gammaRate ∧
      gammaRate ≤ 158851460347347083647 / 13097448000000000000 := by
  rw [gamma_eq]
  obtain ⟨hb1, hb2⟩ := sum_bridge
  constructor
  · calc (159010385641752609841 / 13110552000000000000 : ℝ) =
          (12127998763267375 : ℝ) / 10 ^ 15 + M / 2001 := by
            rw [M]
            norm_num
      _ ≤ _ := add_le_add hb1 tail_lower
  · calc _ ≤ ((12127998763267375 : ℝ) + 2000 * 53) / 10 ^ 15 + M / 1999 :=
          add_le_add hb2 tail_upper
      _ = 158851460347347083647 / 13097448000000000000 := by
            rw [M]
            norm_num

end Zeta2GammaBounds
