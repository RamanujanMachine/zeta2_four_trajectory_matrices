import Zeta2FourTrajectoryMatrices.ArithmeticNormalization.arithmetic_normalization_sprime

open Polynomial Finset Zeta2Blueprint Zeta2NextTwo

noncomputable section

namespace Zeta2ANSprime

theorem termRed (N r p : ℕ) [Fact p.Prime] (hp2 : 50 * N < p ^ 2) (Q : (ZMod p)[X])
    (κ : ZMod p) (A : ℕ → ZMod p)
    (hC : ∀ j ≤ 11 * N, ((cZ N j / (p : ℤ) ^ (phi ((N : ℝ) / p)).toNat : ℤ) : ZMod p) =
      κ * Q.eval ((j % p : ℕ) : ZMod p) * A (j / p))
    (k : ℕ) (hk : k < p) (V : ℤ) (hV1 : ((11 * N / p : ℕ) : ℤ) + 1 ≤ V)
    (hV2 : V + ((11 * N / p : ℕ) : ℤ) + 2 ≤ p) (j : ℕ) (hj : j ≤ 11 * N) :
    Rd p ((p : ℚ) ^ ((1 : ℤ) - ((phi ((N : ℝ) / p)).toNat : ℤ)) *
        (Zeta2FirstThree.om (11 * N) j * (X ^ r * Fpoly N).eval (j : ℚ) / ((k : ℚ) + p * V - j)))
      (if j % p = k then (k : ZMod p) ^ r * (κ * Q.eval (k : ZMod p) * A (j / p)) *
        ((V : ZMod p) - ((j / p : ℕ) : ZMod p))⁻¹ else 0) := by
  have pp : p.Prime := Fact.out
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 pp.ne_zero
  set h := (phi ((N : ℝ) / p)).toNat with hh
  obtain ⟨w, hw⟩ := cZ_dvd N p j pp hp2 hj
  have hwq : cZ N j / (p : ℤ) ^ h = w := by
    rw [hw, Int.mul_ediv_cancel_left _ (pow_ne_zero _ (by exact_mod_cast pp.ne_zero))]
  have hph : (p : ℚ) ^ ((1 : ℤ) - (h : ℤ)) * (p : ℚ) ^ h = p := by
    rw [← zpow_natCast, ← zpow_add₀ hp0, sub_add_cancel, zpow_one]
  have hom : Zeta2FirstThree.om (11 * N) j * (X ^ r * Fpoly N).eval (j : ℚ) =
      (j : ℚ) ^ r * ((p : ℚ) ^ h * w) := by
    have e1 : Zeta2FirstThree.om (11 * N) j * (Fpoly N).eval (j : ℚ) = cj N j := rfl
    rw [eval_mul, eval_pow, eval_X, mul_left_comm, e1, cj_eq, hw, Int.cast_mul, Int.cast_pow,
      Int.cast_natCast]
  have hM : j / p ≤ 11 * N / p := Nat.div_le_div_right hj
  have h1 : (p : ℤ) * (((11 * N / p : ℕ) : ℤ) + 1) ≤ p * V :=
    mul_le_mul_of_nonneg_left hV1 (Int.natCast_nonneg p)
  have h2 : ((11 * N : ℕ) : ℤ) < (p : ℤ) * (((11 * N / p : ℕ) : ℤ) + 1) := by
    exact_mod_cast Nat.lt_mul_div_succ (11 * N) pp.pos
  have hsq : (k : ℚ) + p * V - j ≠ 0 := fun he => by
    have h3 : (k : ℤ) + p * V - j = 0 := by exact_mod_cast he
    omega
  have hq : (p : ℚ) ^ ((1 : ℤ) - (h : ℤ)) * (Zeta2FirstThree.om (11 * N) j *
      (X ^ r * Fpoly N).eval (j : ℚ) / ((k : ℚ) + p * V - j)) * (((k : ℤ) + p * V - j : ℤ) : ℚ) =
      (((p : ℤ) * (j : ℤ) ^ r * w : ℤ) : ℚ) := by
    rw [hom, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_natCast,
      Int.cast_natCast, mul_assoc, div_mul_cancel₀ _ hsq, Int.cast_mul, Int.cast_mul, Int.cast_pow,
      Int.cast_natCast, Int.cast_natCast]
    linear_combination ((j : ℚ) ^ r * w) * hph
  by_cases hjk : j % p = k
  · rw [ite_eq_left hjk]
    have hjl : (j : ℤ) = k + p * ((j / p : ℕ) : ℤ) := by
      have := Nat.mod_add_div j p
      rw [hjk] at this
      exact_mod_cast this.symm
    have hf : (0 : ℤ) ≤ ((j / p : ℕ) : ℤ) := Int.natCast_nonneg _
    have hb : ¬ (p : ℤ) ∣ V - ((j / p : ℕ) : ℤ) := fun hd => by
      have := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega) (by omega) hd
      omega
    have e : (p : ℚ) ^ ((1 : ℤ) - (h : ℤ)) * (Zeta2FirstThree.om (11 * N) j *
        (X ^ r * Fpoly N).eval (j : ℚ) / ((k : ℚ) + p * V - j)) *
          ((V - ((j / p : ℕ) : ℤ) : ℤ) : ℚ) =
        (((j : ℤ) ^ r * w : ℤ) : ℚ) := by
      refine mul_left_cancel₀ hp0 ?_
      rw [show (((k : ℤ) + p * V - j : ℤ) : ℚ) = p * ((V - ((j / p : ℕ) : ℤ) : ℤ) : ℚ) by
        rw [hjl]; push_cast; ring] at hq
      rw [Int.cast_mul, Int.cast_mul, Int.cast_natCast] at hq
      rw [Int.cast_mul]
      linear_combination hq
    have hv : (((j : ℤ) ^ r * w : ℤ) : ZMod p) * (((V - ((j / p : ℕ) : ℤ) : ℤ) : ZMod p))⁻¹ =
        (k : ZMod p) ^ r * (κ * Q.eval (k : ZMod p) * A (j / p)) *
          ((V : ZMod p) - ((j / p : ℕ) : ZMod p))⁻¹ := by
      have hjz : (j : ZMod p) = (k : ZMod p) := by
        have := congrArg (fun z : ℤ => (z : ZMod p)) hjl
        rw [Int.cast_natCast, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_natCast,
          Int.cast_natCast, ZMod.natCast_self, zero_mul, add_zero] at this
        exact this
      rw [Int.cast_mul, Int.cast_pow, Int.cast_natCast, hjz, ← hwq, hC j hj, hjk, Int.cast_sub,
        Int.cast_natCast]
    rw [← hv]
    exact Rd_of_mul _ _ _ hb e
  · rw [ite_eq_right hjk]
    have hb : ¬ (p : ℤ) ∣ (k : ℤ) + p * V - j := fun hd => by
      have h4 : (p : ℤ) ∣ (k : ℤ) - j := by
        have := dvd_sub hd (dvd_mul_right (p : ℤ) V)
        rwa [show (k : ℤ) + p * V - j - p * V = k - j by ring] at this
      have h6 : (k : ℤ) % p = (j : ℤ) % p := Int.emod_eq_emod_iff_emod_sub_eq_zero.2
        (Int.emod_eq_zero_of_dvd h4)
      rw [Int.emod_eq_of_lt (by omega) (by omega), ← Int.natCast_mod] at h6
      omega
    have hv : (((p : ℤ) * (j : ℤ) ^ r * w : ℤ) : ZMod p) *
        ((((k : ℤ) + p * V - j : ℤ) : ZMod p))⁻¹ =
        0 := by
      rw [Int.cast_mul, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, zero_mul,
        zero_mul]
    rw [← hv]
    exact Rd_of_mul _ _ _ hb hq

theorem winRed (N r p : ℕ) [Fact p.Prime] (hp2 : 50 * N < p ^ 2) (Q : (ZMod p)[X])
    (κ : ZMod p) (A : ℕ → ZMod p)
    (hC : ∀ j ≤ 11 * N, ((cZ N j / (p : ℤ) ^ (phi ((N : ℝ) / p)).toNat : ℤ) : ZMod p) =
      κ * Q.eval ((j % p : ℕ) : ZMod p) * A (j / p))
    (U : ℤ → ZMod p) (k : ℕ) (hk : k < p) (V : ℤ) (hV1 : ((11 * N / p : ℕ) : ℤ) + 1 ≤ V)
    (hV2 : V + ((11 * N / p : ℕ) : ℤ) + 2 ≤ p)
    (hRk : Rd p ((p : ℚ) ^ ((1 : ℤ) - ((phi ((N : ℝ) / p)).toNat : ℤ)) *
      ((Fpoly N).eval ((k : ℚ) + p * V) * ((-1) ^ (11 * N) * ((11 * N).factorial : ℚ) /
        ∏ j ∈ range (11 * N + 1), ((k : ℚ) + p * V - j)))) (Q.eval (k : ZMod p) * U V)) :
    Rd p ((p : ℚ) ^ ((1 : ℤ) - ((phi ((N : ℝ) / p)).toNat : ℤ)) *
        (Spoly N r).eval ((k : ℚ) + p * V))
      ((k : ZMod p) ^ r * (Q.eval (k : ZMod p) * U V) - ∑ j ∈ range (11 * N + 1),
        (if j % p = k then (k : ZMod p) ^ r * (κ * Q.eval (k : ZMod p) * A (j / p)) *
          ((V : ZMod p) - ((j / p : ℕ) : ZMod p))⁻¹ else 0)) := by
  have pp : p.Prime := Fact.out
  have hs : ∀ j : ℕ, j ≤ 11 * N → (k : ℚ) + p * V ≠ j := fun j hj he => by
    have h1 : (p : ℤ) * (((11 * N / p : ℕ) : ℤ) + 1) ≤ p * V :=
      mul_le_mul_of_nonneg_left hV1 (Int.natCast_nonneg p)
    have h2 : ((11 * N : ℕ) : ℤ) < (p : ℤ) * (((11 * N / p : ℕ) : ℤ) + 1) := by
      exact_mod_cast Nat.lt_mul_div_succ (11 * N) pp.pos
    have h3 : (k : ℤ) + p * V = j := by exact_mod_cast he
    omega
  rw [Spoly_eq, Zeta2NextTwo.Sm_eval' _ _ _ hs, eval_mul, eval_pow, eval_X, mul_sub, mul_sum]
  refine Rd_sub pp ?_ (Rd_sum pp _ _ _ fun j hj => termRed N r p hp2 Q κ A hC k hk V hV1 hV2 j
    (by have := mem_range.1 hj; omega))
  have hsr : Rd p (((k : ℚ) + p * V) ^ r) ((k : ZMod p) ^ r) := by
    have := Rd_int pp (((k : ℤ) + p * V) ^ r)
    simp only [Int.cast_pow, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
      zero_mul, add_zero] at this
    exact this
  rw [mul_assoc (((k : ℚ) + p * V) ^ r), mul_left_comm]
  exact Rd_mul pp hsr hRk

theorem lcm_split12 (N p : ℕ) (pp : p.Prime) (h1 : p ≤ 12 * N) (h2 : 12 * N < p ^ 2) :
    ∃ U : ℕ, ¬ p ∣ U ∧ lcmUpTo (12 * N) = p * U := by
  have hf : (lcmUpTo (12 * N)).factorization p = 1 := by
    rw [show lcmUpTo (12 * N) = Nat.lcmUpto (12 * N) from rfl, Nat.factorization_lcmUpto _ pp]
    exact Nat.log_eq_one_iff'.2 ⟨h1, by rw [← pow_two]; exact h2⟩
  refine ⟨ordCompl[p] (lcmUpTo (12 * N)), Nat.not_dvd_ordCompl pp (lcmUpTo_pos _).ne', ?_⟩
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self (lcmUpTo (12 * N)) p]
  rw [hf, pow_one]

theorem T_val (N r p : ℕ) (pp : p.Prime) (Ud : ℕ) (hd : lcmUpTo (12 * N) = p * Ud) (wv : ℤ → ℤ)
    (hwv : ∀ z : ℤ, (C (lcmUpTo (12 * N) : ℚ) * Spoly N r).eval (z : ℚ) =
      (((p : ℤ) ^ (phi ((N : ℝ) / p)).toNat : ℤ) : ℚ) * wv z) (s : ℤ) :
    (p : ℚ) ^ ((1 : ℤ) - ((phi ((N : ℝ) / p)).toNat : ℤ)) * (Spoly N r).eval (s : ℚ) *
      ((Ud : ℤ) : ℚ) = wv s := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 pp.ne_zero
  set h := (phi ((N : ℝ) / p)).toNat with hh
  have hph : (p : ℚ) ^ ((1 : ℤ) - (h : ℤ)) * (p : ℚ) ^ h = p := by
    rw [← zpow_natCast, ← zpow_add₀ hp0, sub_add_cancel, zpow_one]
  have e := hwv s
  rw [eval_mul, eval_C, hd, Nat.cast_mul, Int.cast_pow, Int.cast_natCast] at e
  refine mul_left_cancel₀ (pow_ne_zero h hp0) ?_
  rw [Int.cast_natCast]
  linear_combination ((Spoly N r).eval (s : ℚ) * Ud) * hph + e

theorem winG (N r p : ℕ) [Fact p.Prime] (hp2 : 50 * N < p ^ 2) (Q : (ZMod p)[X])
    (κ : ZMod p) (A : ℕ → ZMod p)
    (hC : ∀ j ≤ 11 * N, ((cZ N j / (p : ℤ) ^ (phi ((N : ℝ) / p)).toNat : ℤ) : ZMod p) =
      κ * Q.eval ((j % p : ℕ) : ZMod p) * A (j / p))
    (U : ℤ → ZMod p) (Ud : ℕ) (wv : ℤ → ℤ)
    (hT : ∀ s : ℤ, (p : ℚ) ^ ((1 : ℤ) - ((phi ((N : ℝ) / p)).toNat : ℤ)) *
      (Spoly N r).eval (s : ℚ) * ((Ud : ℤ) : ℚ) = wv s)
    (G : (ZMod p)[X]) (k : ℕ) (hk : k < p)
    (hGv : ∀ V : ℤ, (wv (k + p * V) : ZMod p) = G.eval (V : ZMod p))
    (V : ℤ) (hV1 : ((11 * N / p : ℕ) : ℤ) + 1 ≤ V) (hV2 : V + ((11 * N / p : ℕ) : ℤ) + 2 ≤ p)
    (hRk : Rd p ((p : ℚ) ^ ((1 : ℤ) - ((phi ((N : ℝ) / p)).toNat : ℤ)) *
      ((Fpoly N).eval ((k : ℚ) + p * V) * ((-1) ^ (11 * N) * ((11 * N).factorial : ℚ) /
        ∏ j ∈ range (11 * N + 1), ((k : ℚ) + p * V - j)))) (Q.eval (k : ZMod p) * U V)) :
    G.eval (V : ZMod p) = (k : ZMod p) ^ r * Q.eval (k : ZMod p) *
      (U V - κ * ∑ l ∈ range (11 * N / p), A l * ((V : ZMod p) - l)⁻¹ -
        (if k ≤ 11 * N % p then 1 else 0) * κ * A (11 * N / p) *
          ((V : ZMod p) - ((11 * N / p : ℕ) : ZMod p))⁻¹) * Ud := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hv := Rd_val (winRed N r p hp2 Q κ A hC U k hk V hV1 hV2 hRk) Ud (wv (k + p * V))
    (by have := hT ((k : ℤ) + p * V); push_cast at this; exact this)
  have hdm := Nat.div_add_mod (11 * N) p
  rw [hGv, show 11 * N + 1 = p * (11 * N / p) + (11 * N % p + 1) by omega,
    reidx (11 * N / p) (11 * N % p) k (Nat.mod_lt _ hp0) hk, Int.cast_natCast] at hv
  exact hv

theorem alg1 {F : Type*} [Field F] (D ck c0 Ud u S κ AM ik i0 : F) (hD : D ≠ 0) (hc : c0 ≠ 0) :
    D * (ck * (u - κ * S - ik * κ * AM * D⁻¹) * Ud -
      ck * (c0⁻¹ * (c0 * (u - κ * S - i0 * κ * AM * D⁻¹) * Ud))) =
      ck * κ * AM * (i0 - ik) * Ud := by
  have h1 : D * D⁻¹ = 1 := mul_inv_cancel₀ hD
  have h2 : c0⁻¹ * c0 = 1 := inv_mul_cancel₀ hc
  linear_combination (ck * κ * AM * (i0 - ik) * Ud) * h1 -
    (D * ck * Ud * (u - κ * S - i0 * κ * AM * D⁻¹)) * h2

theorem yM_ne {p : ℕ} [Fact p.Prime] (M i : ℕ) (hi : i + 1 < p) :
    ((M + (i + 1) : ℕ) : ZMod p) - (M : ZMod p) ≠ 0 := by
  rw [Nat.cast_add, add_sub_cancel_left]
  intro h
  exact absurd (Nat.le_of_dvd (Nat.succ_pos i) ((ZMod.natCast_eq_zero_iff (i + 1) p).1 h))
    (by omega)

theorem kernel_divided_core (N r p : ℕ) [Fact p.Prime] (hN : 1 ≤ N) (hr : r < 3)
    (hs : p < 8 * N ∧ p.Prime ∧ 50 * N < p ^ 2 ∧ InShell N r p) (Q : (ZMod p)[X])
    (hC : ∃ (κ : ZMod p) (Acoef : ℕ → ZMod p), ∀ j ≤ 11 * N,
      ((cZ N j / (p : ℤ) ^ (phi ((N : ℝ) / p)).toNat : ℤ) : ZMod p) =
        κ * Q.eval ((j % p : ℕ) : ZMod p) * Acoef (j / p))
    (hR : ∃ U : ℤ → ZMod p, ∀ k : ℕ, k < p → ∀ V : ℤ, ((11 * N / p : ℕ) : ℤ) + 1 ≤ V →
      V + ((11 * N / p : ℕ) : ℤ) + 2 ≤ p →
      ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧
        (p : ℚ) ^ ((1 : ℤ) - ((phi ((N : ℝ) / p)).toNat : ℤ)) *
          ((Fpoly N).eval ((k : ℚ) + p * V) *
            ((-1) ^ (11 * N) * ((11 * N).factorial : ℚ) /
              ∏ j ∈ range (11 * N + 1), ((k : ℚ) + p * V - j))) * b = a ∧
        (a : ZMod p) = Q.eval (k : ZMod p) * U V * b) :
    ∃ (κ : ZMod p) (B : (ZMod p)[X]), ∀ s : ℤ,
      ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧
        (p : ℚ) ^ ((1 : ℤ) - ((phi ((N : ℝ) / p)).toNat : ℤ)) * (Spoly N r).eval (s : ℚ) * b = a ∧
        (a : ZMod p) =
          κ * (s : ZMod p) ^ r * Q.eval (s : ZMod p) * B.eval ((s / p : ℤ) : ZMod p) * b := by
  have pp : p.Prime := Fact.out
  have hp0 := pp.pos
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 pp.ne_zero
  obtain ⟨hp8, -, hp2, hsh⟩ := hs
  obtain ⟨K, hK2, hK1, hK3⟩ := shellK N r p hp2 hsh
  have hMK : 11 * N / p < K := (Nat.div_lt_iff_lt_mul hp0).2 (by rw [Nat.mul_comm K p]; omega)
  obtain ⟨κ, A, hA⟩ := hC
  obtain ⟨U, hU⟩ := hR
  obtain ⟨Ud, hUd, hd⟩ := lcm_split12 N p pp (by omega) (by omega)
  choose wv hwv using P_IntVal_p N r p pp hN hr hp2
  have hT := T_val N r p pp Ud hd wv hwv
  have hPw : ∀ z : ℤ, (C (((p : ℚ) ^ (phi ((N : ℝ) / p)).toNat)⁻¹) *
      (C (lcmUpTo (12 * N) : ℚ) * Spoly N r)).eval (z : ℚ) = wv z := fun z => by
    rw [eval_mul, eval_C, hwv z, Int.cast_pow, Int.cast_natCast,
      inv_mul_cancel_left₀ (pow_ne_zero _ hpq)]
  have hdeg : (C (((p : ℚ) ^ (phi ((N : ℝ) / p)).toNat)⁻¹) *
      (C (lcmUpTo (12 * N) : ℚ) * Spoly N r)).natDegree < p * K :=
    (natDegree_C_mul_le _ _).trans_lt ((P_deg N r hN).trans hK1)
  choose G hGd hGv using fun k : ℕ => redA _ wv hPw K (by omega) (by omega) hdeg (k : ℤ)
  have hW : ∀ k < p, ∀ i < K + 1, (G k).eval ((11 * N / p + (i + 1) : ℕ) : ZMod p) =
      (k : ZMod p) ^ r * Q.eval (k : ZMod p) *
        (U ((11 * N / p + (i + 1) : ℕ) : ℤ) - κ * ∑ l ∈ range (11 * N / p),
          A l * (((11 * N / p + (i + 1) : ℕ) : ZMod p) - l)⁻¹ -
          (if k ≤ 11 * N % p then 1 else 0) * κ * A (11 * N / p) *
            (((11 * N / p + (i + 1) : ℕ) : ZMod p) - ((11 * N / p : ℕ) : ZMod p))⁻¹) * Ud :=
    fun k hk i hi => by
      have h1 : ((11 * N / p : ℕ) : ℤ) + 1 ≤ ((11 * N / p + (i + 1) : ℕ) : ℤ) := by omega
      have h2 : ((11 * N / p + (i + 1) : ℕ) : ℤ) + ((11 * N / p : ℕ) : ℤ) + 2 ≤ p := by omega
      have := winG N r p hp2 Q κ A hA U Ud wv hT (G k) k hk (hGv k) _ h1 h2 (hU k hk _ h1 h2)
      rw [Int.cast_natCast] at this
      exact this
  obtain ⟨B0, hB0⟩ : ∃ B0 : (ZMod p)[X], ∀ k < p,
      G k = C ((k : ZMod p) ^ r * Q.eval (k : ZMod p)) * B0 := by
    by_cases hex : ∃ k0 < p, (k0 : ZMod p) ^ r * Q.eval (k0 : ZMod p) ≠ 0
    · obtain ⟨k0, hk0, hc0⟩ := hex
      refine ⟨C (((k0 : ZMod p) ^ r * Q.eval (k0 : ZMod p))⁻¹) * G k0, fun k hk => ?_⟩
      refine sub_eq_zero.1 (polyfrac _ K (11 * N / p) (by omega) ?_
        ((k : ZMod p) ^ r * Q.eval (k : ZMod p) * κ * A (11 * N / p) *
          ((if k0 ≤ 11 * N % p then 1 else 0) - (if k ≤ 11 * N % p then 1 else 0)) * Ud)
        fun i hi => ?_)
      · exact (natDegree_sub_le _ _).trans_lt (max_lt (hGd k) ((natDegree_C_mul_le _ _).trans_lt
          ((natDegree_C_mul_le _ _).trans_lt (hGd k0))))
      · rw [eval_sub, eval_mul, eval_C, eval_mul, eval_C, hW k hk i hi, hW k0 hk0 i hi]
        exact alg1 _ _ _ _ _ _ _ _ _ _ (yM_ne _ i (by omega)) hc0
    · refine ⟨0, fun k hk => ?_⟩
      have hck : (k : ZMod p) ^ r * Q.eval (k : ZMod p) = 0 := by
        by_contra hne
        exact hex ⟨k, hk, hne⟩
      rw [mul_zero]
      exact polyfrac (G k) K (11 * N / p) (by omega) (hGd k) 0 fun i hi => by
        rw [hW k hk i hi, hck, zero_mul, zero_mul, mul_zero]
  have hUz : ((Ud : ℤ) : ZMod p) ≠ 0 := zne_of_ndvd fun h => hUd (Int.natCast_dvd_natCast.1 h)
  refine ⟨((Ud : ℤ) : ZMod p)⁻¹, B0, fun s => ⟨wv s, Ud, fun h => hUd (Int.natCast_dvd_natCast.1 h),
    hT s, ?_⟩⟩
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast pp.ne_zero
  have hks : ((s % p).toNat : ℤ) = s % p := Int.toNat_of_nonneg (Int.emod_nonneg s hpz)
  have hk : (s % p).toNat < p := by
    have := Int.emod_lt_of_pos s (by exact_mod_cast hp0 : (0 : ℤ) < p)
    omega
  have hsd : s = ((s % p).toNat : ℤ) + p * (s / p) := by
    rw [hks]
    exact (Int.emod_add_mul_ediv s p).symm
  have hsz : (s : ZMod p) = (((s % p).toNat : ℕ) : ZMod p) := by
    rw [← Int.cast_natCast, hks, ZMod.intCast_mod]
  have hG := hGv (s % p).toNat (s / p)
  rw [← hsd, hB0 _ hk, eval_mul, eval_C] at hG
  rw [hG, hsz]
  have h1 : ((Ud : ℤ) : ZMod p)⁻¹ * ((Ud : ℤ) : ZMod p) = 1 := inv_mul_cancel₀ hUz
  linear_combination (-((((s % p).toNat : ℕ) : ZMod p) ^ r * Q.eval (((s % p).toNat : ℕ) : ZMod p) *
    B0.eval ((s / p : ℤ) : ZMod p))) * h1

end Zeta2ANSprime
