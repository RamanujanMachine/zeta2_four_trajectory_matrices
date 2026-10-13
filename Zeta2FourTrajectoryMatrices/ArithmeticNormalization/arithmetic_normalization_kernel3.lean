import Zeta2FourTrajectoryMatrices.ArithmeticNormalization.arithmetic_normalization_kernel2

open Polynomial Finset Zeta2Blueprint Zeta2NextTwo

noncomputable section

namespace Zeta2ANKernel

theorem Rbounds (N p k : ℕ) (hp0 : 0 < p) (hk : k < p) (V : ℤ)
    (hV1 : ((11 * N / p : ℕ) : ℤ) + 1 ≤ V) (hV2 : V + ((11 * N / p : ℕ) : ℤ) + 2 ≤ p) :
    0 ≤ V ∧ ((11 * N : ℕ) : ℤ) < k + p * V ∧ (k : ℤ) + p * V + ((11 * N : ℕ) : ℤ) < p ^ 2 := by
  have hdz : ((11 * N : ℕ) : ℤ) = p * ((11 * N / p : ℕ) : ℤ) + ((11 * N % p : ℕ) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod (11 * N) p).symm
  have hmz : ((11 * N % p : ℕ) : ℤ) < p := by exact_mod_cast Nat.mod_lt (11 * N) hp0
  have hp' : (0 : ℤ) ≤ p := by exact_mod_cast hp0.le
  have hkz : (k : ℤ) < p := by exact_mod_cast hk
  have hM0 : (0 : ℤ) ≤ ((11 * N / p : ℕ) : ℤ) := Nat.cast_nonneg _
  have hd0 : (0 : ℤ) ≤ ((11 * N % p : ℕ) : ℤ) := Nat.cast_nonneg _
  have hk0 : (0 : ℤ) ≤ (k : ℤ) := Nat.cast_nonneg _
  generalize ((11 * N / p : ℕ) : ℤ) = M at hdz hV1 hV2 hM0
  generalize ((11 * N % p : ℕ) : ℤ) = d at hdz hmz hd0
  generalize ((11 * N : ℕ) : ℤ) = A at hdz ⊢
  generalize (k : ℤ) = K at hkz hk0 ⊢
  generalize (p : ℤ) = P at hdz hmz hp' hV2 hkz ⊢
  have h1 : P * (M + 1) ≤ P * V := mul_le_mul_of_nonneg_left hV1 hp'
  have h2 : P * V ≤ P * (P - M - 2) := mul_le_mul_of_nonneg_left (by omega) hp'
  have e1 : P * (M + 1) = P * M + P := by ring
  have e2 : P * (P - M - 2) = P ^ 2 - P * M - 2 * P := by ring
  refine ⟨by omega, by omega, by omega⟩

theorem RPloc (N p : ℕ) [Fact p.Prime] (k : ℕ) (hk : k < p) (V : ℤ)
    (hV1 : ((11 * N / p : ℕ) : ℤ) + 1 ≤ V) (hV2 : V + ((11 * N / p : ℕ) : ℤ) + 2 ≤ p)
    (w0 w1 : ℤ) (e0 : ((8 * N).factorial : ℤ) = (p : ℤ) ^ (8 * N / p) * w0)
    (e1 : ((11 * N).factorial : ℤ) = (p : ℤ) ^ (11 * N / p) * w1) (hw0 : ¬ (p : ℤ) ∣ w0) :
    ∃ (t : ℕ) (a b : ℤ), chi N p k = ((phi ((N : ℝ) / p)).toNat : ℤ) + t ∧ ¬ (p : ℤ) ∣ b ∧
      (p : ℚ) ^ ((1 : ℤ) - ((phi ((N : ℝ) / p)).toNat : ℤ)) *
          ((Fpoly N).eval ((k : ℚ) + p * V) *
            ((-1) ^ (11 * N) * ((11 * N).factorial : ℚ) /
              ∏ j ∈ range (11 * N + 1), ((k : ℚ) + p * V - j))) * b = a ∧
      (b : ZMod p) = (w0 : ZMod p) ^ 3 *
        (Kd p N k * Wf p (k : ℤ) (11 * N + 1) (fun x => ((V + x : ℤ) : ZMod p))) ∧
      (a : ZMod p) = (p : ZMod p) ^ t * ((-1) ^ (11 * N) * (w1 : ZMod p) *
        (Kn p N k 9 * Wn p N k 9 V) * (Kn p N k 10 * Wn p N k 10 V) *
        (Kn p N k 11 * Wn p N k 11 V)) := by
  have pp : p.Prime := Fact.out
  have hp0 := pp.pos
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast pp.ne_zero
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast pp.ne_zero
  set h := (phi ((N : ℝ) / p)).toNat with hh
  obtain ⟨hV0, hb1, hb2⟩ := Rbounds N p k hp0 hk V hV1 hV2
  set s := k + p * V.toNat with hsdef
  have hs : (s : ℤ) = k + p * V := by
    rw [hsdef, Nat.cast_add, Nat.cast_mul, Int.toNat_of_nonneg hV0]
  have e2 := Nat.cast_pow (α := ℤ) p 2
  have hsb : s + 11 * N < p ^ 2 := by
    have : ((s + 11 * N : ℕ) : ℤ) < ((p ^ 2 : ℕ) : ℤ) := by push_cast; push_cast at hb2; omega
    exact_mod_cast this
  obtain ⟨α9, hα9, eA9, rA9⟩ := NUM1 pp s k (9 * N) (8 * N) V hs (by omega) (by omega)
  obtain ⟨α10, hα10, eA10, rA10⟩ := NUM1 pp s k (10 * N) (8 * N) V hs (by omega) (by omega)
  obtain ⟨α11, hα11, eA11, rA11⟩ := NUM1 pp s k (11 * N) (8 * N) V hs (by omega) (by omega)
  obtain ⟨β, hβ, eB, rB⟩ := DENr pp k (11 * N) V (by push_cast at hb1; exact hb1)
    (by push_cast at hb2; omega)
  have hEx := EXP N p k hp0 hk
  have hcl := hp_le_chi N p hp0 k
  obtain ⟨t, ht⟩ : ∃ t : ℕ, chi N p k = h + t := ⟨(chi N p k - h).toNat, by omega⟩
  have hpow : (p : ℤ) * (p : ℤ) ^ (11 * N / p) * (p : ℤ) ^ Ecnt p ((k + 9 * N : ℕ) : ℤ) (8 * N) *
      (p : ℤ) ^ Ecnt p ((k + 10 * N : ℕ) : ℤ) (8 * N) *
      (p : ℤ) ^ Ecnt p ((k + 11 * N : ℕ) : ℤ) (8 * N) =
      (p : ℤ) ^ t * ((p : ℤ) ^ (8 * N / p)) ^ 3 * (p : ℤ) ^ Ecnt p k (11 * N + 1) *
        (p : ℤ) ^ h := by
    rw [← pow_succ', ← pow_add, ← pow_add, ← pow_add, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]
    congr 1
    omega
  have keyZ : (p : ℤ) * ((-1) ^ (11 * N) * ((11 * N).factorial : ℤ) *
      ((∏ i ∈ range (8 * N), (((s + 9 * N : ℕ) : ℤ) - i)) *
        (∏ i ∈ range (8 * N), (((s + 10 * N : ℕ) : ℤ) - i)) *
        (∏ i ∈ range (8 * N), (((s + 11 * N : ℕ) : ℤ) - i)))) * (w0 ^ 3 * β) =
      ((-1) ^ (11 * N) * (p : ℤ) ^ t * w1 * (α9 * α10 * α11)) *
        (((8 * N).factorial : ℤ) ^ 3 * ∏ i ∈ range (11 * N + 1), ((k : ℤ) + p * V - i)) *
        (p : ℤ) ^ h := by
    rw [e0, e1, eA9, eA10, eA11, eB]
    linear_combination (-1) ^ (11 * N) * w1 * (α9 * α10 * α11) * w0 ^ 3 * β * hpow
  have hβ0 : β ≠ 0 := fun h0 => hβ (h0 ▸ dvd_zero _)
  have hD : (∏ i ∈ range (11 * N + 1), ((k : ℤ) + p * V - i)) ≠ 0 := by
    rw [eB]
    exact mul_ne_zero (pow_ne_zero _ hpz) hβ0
  have hDq : (∏ i ∈ range (11 * N + 1), ((k : ℚ) + p * V - i)) ≠ 0 := by
    have := (Int.cast_ne_zero (α := ℚ)).2 hD
    push_cast at this
    exact this
  have hF0 : ((8 * N).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  refine ⟨t, (-1) ^ (11 * N) * (p : ℤ) ^ t * w1 * (α9 * α10 * α11), w0 ^ 3 * β, ht,
    fun hd => ?_, ?_, ?_, ?_⟩
  · rcases (pz_prime pp).dvd_or_dvd hd with h1 | h1
    · exact hw0 ((pz_prime pp).dvd_of_dvd_pow h1)
    · exact hβ h1
  · have hsq : ((s : ℕ) : ℚ) = (k : ℚ) + p * V := by exact_mod_cast hs
    rw [← hsq, Fpoly, eval_mul, eval_mul, binom_eval_nat, binom_eval_nat, binom_eval_nat, hsq]
    have h9 := CI (s + 9 * N) (8 * N)
    have h10 := CI (s + 10 * N) (8 * N)
    have h11 := CI (s + 11 * N) (8 * N)
    have hFv : ((((s + 10 * N).choose (8 * N) : ℕ) : ℚ) * (((s + 9 * N).choose (8 * N) : ℕ) : ℚ) *
        (((s + 11 * N).choose (8 * N) : ℕ) : ℚ)) * ((8 * N).factorial : ℚ) ^ 3 =
        (((∏ i ∈ range (8 * N), (((s + 9 * N : ℕ) : ℤ) - i)) *
          (∏ i ∈ range (8 * N), (((s + 10 * N : ℕ) : ℤ) - i)) *
          (∏ i ∈ range (8 * N), (((s + 11 * N : ℕ) : ℤ) - i)) : ℤ) : ℚ) := by
      rw [← h9, ← h10, ← h11]
      push_cast
      ring
    have kq := congrArg (Int.cast : ℤ → ℚ) keyZ
    rw [zpow_sub₀ hpq, zpow_one, zpow_natCast, div_mul_eq_mul_div, div_mul_eq_mul_div,
      div_eq_iff (pow_ne_zero _ hpq), mul_div_assoc', mul_div_assoc', div_mul_eq_mul_div,
      div_eq_iff hDq]
    apply mul_right_cancel₀ (pow_ne_zero 3 hF0)
    push_cast at kq hFv ⊢
    linear_combination ((p : ℚ) * (-1) ^ (11 * N) * ((11 * N).factorial : ℚ) *
      ((w0 : ℚ) ^ 3 * β)) * hFv + kq
  · rw [Int.cast_mul, Int.cast_pow, rB]
    rfl
  · simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
    rw [rA9, rA10, rA11]
    unfold Kn Wn
    ring

theorem R_pt_core (N r p : ℕ) [Fact p.Prime] (hN : 1 ≤ N) (hr : r < 3)
    (hs : p < 8 * N ∧ p.Prime ∧ 50 * N < p ^ 2 ∧ InShell N r p) (Q : (ZMod p)[X])
    (hQ : binomPoly (ZMod p) ((9 * N : ℕ) : ZMod p) (8 * N % p) *
      binomPoly (ZMod p) ((10 * N : ℕ) : ZMod p) (8 * N % p) *
      binomPoly (ZMod p) ((11 * N : ℕ) : ZMod p) (8 * N % p) *
        (X ^ p - X) ^ (1 - (phi ((N : ℝ) / p)).toNat) =
      (X ^ p - X) ^ ((phi ((N : ℝ) / p)).toNat - 1) *
        (∏ j ∈ range (11 * N % p + 1), (X - C (j : ZMod p))) * Q) :
    ∃ U : ℤ → ZMod p, ∀ k : ℕ, k < p → ∀ V : ℤ, ((11 * N / p : ℕ) : ℤ) + 1 ≤ V →
      V + ((11 * N / p : ℕ) : ℤ) + 2 ≤ p →
      ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧
        (p : ℚ) ^ ((1 : ℤ) - ((phi ((N : ℝ) / p)).toNat : ℤ)) *
          ((Fpoly N).eval ((k : ℚ) + p * V) *
            ((-1) ^ (11 * N) * ((11 * N).factorial : ℚ) /
              ∏ j ∈ range (11 * N + 1), ((k : ℚ) + p * V - j))) * b = a ∧
        (a : ZMod p) = Q.eval (k : ZMod p) * U V * b := by
  have pp : p.Prime := Fact.out
  have hp0 := pp.pos
  obtain ⟨ε, hε⟩ := Kpart N p Q hQ
  obtain ⟨k0, hk0, hχ0⟩ := chi_min' N p hp0
  obtain ⟨w0, hw0, e0⟩ := fact_val pp (8 * N) (by omega)
  obtain ⟨w1, hw1, e1⟩ := fact_val pp (11 * N) (by omega)
  have hw0z : (w0 : ZMod p) ≠ 0 := fun h0 => hw0 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 h0)
  refine ⟨fun V => (-1) ^ (11 * N) * (w1 : ZMod p) * ε *
      (Wn p N k0 9 V * Wn p N k0 10 V * Wn p N k0 11 V) /
      ((w0 : ZMod p) ^ 3 * Wf p (k0 : ℤ) (11 * N + 1) (fun x => ((V + x : ℤ) : ZMod p))),
    fun k hk V hV1 hV2 => ?_⟩
  obtain ⟨t, a, b, ht, hb, hq, rb, ra⟩ := RPloc N p k hk V hV1 hV2 w0 w1 e0 e1 hw0
  refine ⟨a, b, hb, hq, ?_⟩
  have hbz : (b : ZMod p) ≠ 0 := fun h0 => hb ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 h0)
  rw [rb] at hbz
  have hW := right_ne_zero_of_mul (right_ne_zero_of_mul hbz)
  rcases Nat.eq_zero_or_pos t with rfl | htp
  · rw [Nat.cast_zero, add_zero] at ht
    have hK := (hε k hk).1 ht
    obtain ⟨he, hu⟩ := Zeta2ANChamber.chamber_table_core N r p hN hr hs k k0 hk hk0 ht hχ0
    have h9 := hu 9 (mem_insert_self 9 _)
    have h10 := hu 10 (mem_insert_of_mem (mem_insert_self 10 _))
    have h11 := hu 11 (mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self 11)))
    have w9 := WCnum N (8 * N) (9 * N) p k k0 hp0 (by omega) h9.1 h9.2
      (fun x => ((V + x : ℤ) : ZMod p))
    have w10 := WCnum (2 * N) (8 * N) (10 * N) p k k0 hp0 (by omega) h10.1 h10.2
      (fun x => ((V + x : ℤ) : ZMod p))
    have w11 := WCnum (3 * N) (8 * N) (11 * N) p k k0 hp0 (by omega) h11.1 h11.2
      (fun x => ((V + x : ℤ) : ZMod p))
    have wd := WCden N p k k0 hp0 hk hk0 (by omega) (by omega) he (fun x => ((V + x : ℤ) : ZMod p))
    rw [ra, rb, pow_zero, one_mul]
    unfold Wn Kn Kd at *
    beta_reduce
    rw [← w9, ← w10, ← w11, ← wd, mul_div_assoc', div_mul_eq_mul_div,
      eq_div_iff (mul_ne_zero (pow_ne_zero 3 hw0z) hW)]
    linear_combination (-1) ^ (11 * N) * (w1 : ZMod p) *
      (Wf p ((k + 9 * N : ℕ) : ℤ) (8 * N) (fun x => ((V + x : ℤ) : ZMod p)) *
        Wf p ((k + 10 * N : ℕ) : ℤ) (8 * N) (fun x => ((V + x : ℤ) : ZMod p)) *
        Wf p ((k + 11 * N : ℕ) : ℤ) (8 * N) (fun x => ((V + x : ℤ) : ZMod p))) *
      ((w0 : ZMod p) ^ 3 * Wf p (k : ℤ) (11 * N + 1) (fun x => ((V + x : ℤ) : ZMod p))) * hK
  · have hQ0 := (hε k hk).2 (by omega)
    rw [ra, ZMod.natCast_self, zero_pow htp.ne', zero_mul, hQ0, zero_mul, zero_mul]

end Zeta2ANKernel
