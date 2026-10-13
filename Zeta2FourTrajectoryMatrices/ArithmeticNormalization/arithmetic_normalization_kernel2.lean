import Zeta2FourTrajectoryMatrices.ArithmeticNormalization.arithmetic_normalization_kernel

open Polynomial Finset Zeta2Blueprint Zeta2NextTwo

noncomputable section

namespace Zeta2ANKernel

def Kn (p N k u : ℕ) : ZMod p := Lk (k : ZMod p) (Ms ((u * N : ℕ) : ZMod p) (8 * N))

def Wn (p N k u : ℕ) (V : ℤ) : ZMod p :=
  Wf p ((k + u * N : ℕ) : ℤ) (8 * N) (fun x => ((V + x : ℤ) : ZMod p))

def Kd (p N k : ℕ) : ZMod p := Lk (k : ZMod p) (Ms 0 (11 * N + 1))

theorem cZ_ident (N j : ℕ) (hj : j ≤ 11 * N) :
    cZ N j * ((8 * N).factorial : ℤ) ^ 3 * ∏ i ∈ (range (11 * N + 1)).erase j, ((j : ℤ) - i) =
      (-1) ^ (11 * N) * ((11 * N).factorial : ℤ) *
        (∏ i ∈ range (8 * N), (((j + 9 * N : ℕ) : ℤ) - i)) *
        (∏ i ∈ range (8 * N), (((j + 10 * N : ℕ) : ℤ) - i)) *
        (∏ i ∈ range (8 * N), (((j + 11 * N : ℕ) : ℤ) - i)) := by
  have h9 := CI (j + 9 * N) (8 * N)
  have h10 := CI (j + 10 * N) (8 * N)
  have h11 := CI (j + 11 * N) (8 * N)
  have hJ := CJ j (11 * N) hj
  rw [cZ, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]
  linear_combination
    ((((j + 10 * N).choose (8 * N) : ℕ) : ℤ) * (((j + 9 * N).choose (8 * N) : ℕ) : ℤ) *
      (((j + 11 * N).choose (8 * N) : ℕ) : ℤ) * ((8 * N).factorial : ℤ) ^ 3) * hJ +
    (-1) ^ (11 * N) * ((11 * N).factorial : ℤ) *
      (((((j + 10 * N).choose (8 * N) : ℕ) : ℤ) * ((8 * N).factorial : ℤ)) *
        ((((j + 11 * N).choose (8 * N) : ℕ) : ℤ) * ((8 * N).factorial : ℤ)) * h9 +
      (∏ i ∈ range (8 * N), (((j + 9 * N : ℕ) : ℤ) - i)) *
        ((((j + 11 * N).choose (8 * N) : ℕ) : ℤ) * ((8 * N).factorial : ℤ)) * h10 +
      (∏ i ∈ range (8 * N), (((j + 9 * N : ℕ) : ℤ) - i)) *
        (∏ i ∈ range (8 * N), (((j + 10 * N : ℕ) : ℤ) - i)) * h11)

theorem Ecnt_pos {p : ℕ} (k m : ℕ) (hk : k ≤ m) : 1 ≤ Ecnt p k (m + 1) := by
  have h := single_le_sum (f := fun i : ℕ => vb p ((k : ℤ) - i)) (fun _ _ => Nat.zero_le _)
    (mem_range.2 (Nat.lt_succ_of_le hk))
  rw [sub_self, vb, ite_eq_left (dvd_zero _)] at h
  exact h

theorem CJloc (N p : ℕ) [Fact p.Prime] (hp8 : p < 8 * N) (hp2 : 50 * N < p ^ 2) (j : ℕ)
    (hj : j ≤ 11 * N) (w0 w1 : ℤ)
    (e0 : ((8 * N).factorial : ℤ) = (p : ℤ) ^ (8 * N / p) * w0)
    (e1 : ((11 * N).factorial : ℤ) = (p : ℤ) ^ (11 * N / p) * w1) :
    ∃ t : ℕ, chi N p ((j % p : ℕ) : ℤ) = ((phi ((N : ℝ) / p)).toNat : ℤ) + t ∧
      Wf p ((j % p : ℕ) : ℤ) (11 * N + 1) (Gl p ((j / p : ℕ) : ℤ)) ≠ 0 ∧
      ((cZ N j / (p : ℤ) ^ (phi ((N : ℝ) / p)).toNat : ℤ) : ZMod p) * (w0 : ZMod p) ^ 3 *
        (Kd p N (j % p) * Wf p ((j % p : ℕ) : ℤ) (11 * N + 1) (Gl p ((j / p : ℕ) : ℤ))) =
      (p : ZMod p) ^ t * ((-1) ^ (11 * N) * (w1 : ZMod p) *
        (Kn p N (j % p) 9 * Wn p N (j % p) 9 ((j / p : ℕ) : ℤ)) *
        (Kn p N (j % p) 10 * Wn p N (j % p) 10 ((j / p : ℕ) : ℤ)) *
        (Kn p N (j % p) 11 * Wn p N (j % p) 11 ((j / p : ℕ) : ℤ))) := by
  have pp : p.Prime := Fact.out
  have hp0 := pp.pos
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast pp.ne_zero
  set h := (phi ((N : ℝ) / p)).toNat with hh
  set k := j % p with hkdef
  set l := j / p with hldef
  have hk : k < p := Nat.mod_lt _ hp0
  have hjkl : (j : ℤ) = k + p * (l : ℤ) := by exact_mod_cast (Nat.mod_add_div j p).symm
  obtain ⟨α9, hα9, eA9, rA9⟩ := NUM1 pp j k (9 * N) (8 * N) (l : ℤ) hjkl (by omega) (by omega)
  obtain ⟨α10, hα10, eA10, rA10⟩ := NUM1 pp j k (10 * N) (8 * N) (l : ℤ) hjkl (by omega)
    (by omega)
  obtain ⟨α11, hα11, eA11, rA11⟩ := NUM1 pp j k (11 * N) (8 * N) (l : ℤ) hjkl (by omega)
    (by omega)
  obtain ⟨β, hβ, eB, rB⟩ := LFe pp j k (11 * N) (l : ℤ) hjkl hj (by omega)
  have hI := cZ_ident N j hj
  obtain ⟨c', hc'⟩ := cZ_dvd N p j pp hp2 hj
  have hEx := EXP N p k hp0 hk
  have hcl := hp_le_chi N p hp0 k
  have hEL := Ecnt_pos (p := p) k (11 * N) (by omega)
  obtain ⟨t, ht⟩ : ∃ t : ℕ, chi N p k = h + t := ⟨(chi N p k - h).toNat, by omega⟩
  have hpow : (p : ℤ) ^ (11 * N / p) * (p : ℤ) ^ Ecnt p ((k + 9 * N : ℕ) : ℤ) (8 * N) *
      (p : ℤ) ^ Ecnt p ((k + 10 * N : ℕ) : ℤ) (8 * N) *
      (p : ℤ) ^ Ecnt p ((k + 11 * N : ℕ) : ℤ) (8 * N) =
      (p : ℤ) ^ h * ((p : ℤ) ^ (8 * N / p)) ^ 3 * (p : ℤ) ^ (Ecnt p k (11 * N + 1) - 1) *
        (p : ℤ) ^ t := by
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]
    congr 1
    omega
  rw [hc', e0, e1, eA9, eA10, eA11, eB] at hI
  have key : c' * w0 ^ 3 * β = (-1) ^ (11 * N) * (p : ℤ) ^ t * w1 * (α9 * α10 * α11) := by
    apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (pow_ne_zero h hpz)
      (pow_ne_zero 3 (pow_ne_zero (8 * N / p) hpz))) (pow_ne_zero (Ecnt p k (11 * N + 1) - 1) hpz))
    linear_combination hI + (-1) ^ (11 * N) * w1 * (α9 * α10 * α11) * hpow
  have hb0 : (β : ZMod p) ≠ 0 := fun h0 => hβ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 h0)
  rw [rB, Lk0] at hb0
  refine ⟨t, ht, right_ne_zero_of_mul hb0, ?_⟩
  have kz := congrArg (Int.cast : ℤ → ZMod p) key
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast] at kz
  rw [rA9, rA10, rA11, rB, Lk0] at kz
  rw [hc', Int.mul_ediv_cancel_left _ (pow_ne_zero h hpz), Kd, Kn, Kn, Kn, Wn, Wn, Wn]
  linear_combination kz

theorem kernel_residue_core (N r p : ℕ) [Fact p.Prime] (hN : 1 ≤ N) (hr : r < 3)
    (hs : p < 8 * N ∧ p.Prime ∧ 50 * N < p ^ 2 ∧ InShell N r p) (Q : (ZMod p)[X])
    (hQ : binomPoly (ZMod p) ((9 * N : ℕ) : ZMod p) (8 * N % p) *
      binomPoly (ZMod p) ((10 * N : ℕ) : ZMod p) (8 * N % p) *
      binomPoly (ZMod p) ((11 * N : ℕ) : ZMod p) (8 * N % p) *
        (X ^ p - X) ^ (1 - (phi ((N : ℝ) / p)).toNat) =
      (X ^ p - X) ^ ((phi ((N : ℝ) / p)).toNat - 1) *
        (∏ j ∈ range (11 * N % p + 1), (X - C (j : ZMod p))) * Q) :
    ∃ (κ : ZMod p) (Acoef : ℕ → ZMod p), ∀ j ≤ 11 * N,
      ((cZ N j / (p : ℤ) ^ (phi ((N : ℝ) / p)).toNat : ℤ) : ZMod p) =
        κ * Q.eval ((j % p : ℕ) : ZMod p) * Acoef (j / p) := by
  have pp : p.Prime := Fact.out
  have hp0 := pp.pos
  obtain ⟨ε, hε⟩ := Kpart N p Q hQ
  obtain ⟨k0, hk0, hχ0⟩ := chi_min' N p hp0
  obtain ⟨w0, hw0, e0⟩ := fact_val pp (8 * N) (by omega)
  obtain ⟨w1, hw1, e1⟩ := fact_val pp (11 * N) (by omega)
  have hw0z : (w0 : ZMod p) ≠ 0 := fun h0 => hw0 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 h0)
  refine ⟨(-1) ^ (11 * N) * (w1 : ZMod p) * ε / (w0 : ZMod p) ^ 3,
    fun l => Wn p N k0 9 (l : ℤ) * Wn p N k0 10 (l : ℤ) * Wn p N k0 11 (l : ℤ) /
      Wf p (k0 : ℤ) (11 * N + 1) (Gl p (l : ℤ)), fun j hj => ?_⟩
  obtain ⟨t, ht, hW, hm⟩ := CJloc N p hs.1 hs.2.2.1 j hj w0 w1 e0 e1
  obtain ⟨k, hkdef⟩ : ∃ k, k = j % p := ⟨_, rfl⟩
  rw [← hkdef] at ht hW hm ⊢
  have hk : k < p := hkdef ▸ Nat.mod_lt _ hp0
  have hKd : Kd p N k ≠ 0 := Lk_ne_zero _ _
  rcases Nat.eq_zero_or_pos t with rfl | htp
  · rw [Nat.cast_zero, add_zero] at ht
    have hK := (hε k hk).1 ht
    obtain ⟨he, hu⟩ := Zeta2ANChamber.chamber_table_core N r p hN hr hs k k0 hk hk0 ht hχ0
    have h9 := hu 9 (mem_insert_self 9 _)
    have h10 := hu 10 (mem_insert_of_mem (mem_insert_self 10 _))
    have h11 := hu 11 (mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self 11)))
    have w9 := WCnum N (8 * N) (9 * N) p k k0 hp0 (by omega) h9.1 h9.2
      (fun x => ((((j / p : ℕ) : ℤ) + x : ℤ) : ZMod p))
    have w10 := WCnum (2 * N) (8 * N) (10 * N) p k k0 hp0 (by omega) h10.1 h10.2
      (fun x => ((((j / p : ℕ) : ℤ) + x : ℤ) : ZMod p))
    have w11 := WCnum (3 * N) (8 * N) (11 * N) p k k0 hp0 (by omega) h11.1 h11.2
      (fun x => ((((j / p : ℕ) : ℤ) + x : ℤ) : ZMod p))
    have wd := WCden N p k k0 hp0 hk hk0 (by omega) (by omega) he (Gl p ((j / p : ℕ) : ℤ))
    rw [pow_zero, one_mul] at hm
    unfold Wn at hm ⊢
    beta_reduce
    rw [← w9, ← w10, ← w11, ← wd]
    have hz := (mul_eq_zero.1 (show Kd p N k *
        (((cZ N j / (p : ℤ) ^ (phi ((N : ℝ) / p)).toNat : ℤ) :
        ZMod p) * (w0 : ZMod p) ^ 3 * Wf p (k : ℤ) (11 * N + 1) (Gl p ((j / p : ℕ) : ℤ)) -
        (-1) ^ (11 * N) * (w1 : ZMod p) * ε * Q.eval (k : ZMod p) *
        (Wf p ((k + 9 * N : ℕ) : ℤ) (8 * N) (fun x => ((((j / p : ℕ) : ℤ) + x : ℤ) : ZMod p)) *
          Wf p ((k + 10 * N : ℕ) : ℤ) (8 * N) (fun x => ((((j / p : ℕ) : ℤ) + x : ℤ) : ZMod p)) *
          Wf p ((k + 11 * N : ℕ) : ℤ) (8 * N) (fun x => ((((j / p : ℕ) : ℤ) + x : ℤ) : ZMod p))))
        = 0 by
      unfold Kd
      unfold Kn Kd at hm
      linear_combination hm + (-1) ^ (11 * N) * (w1 : ZMod p) *
        (Wf p ((k + 9 * N : ℕ) : ℤ) (8 * N) (fun x => ((((j / p : ℕ) : ℤ) + x : ℤ) : ZMod p)) *
          Wf p ((k + 10 * N : ℕ) : ℤ) (8 * N) (fun x => ((((j / p : ℕ) : ℤ) + x : ℤ) : ZMod p)) *
          Wf p ((k + 11 * N : ℕ) : ℤ) (8 * N) (fun x => ((((j / p : ℕ) : ℤ) + x : ℤ) : ZMod p))) *
            hK)).resolve_left hKd
    rw [div_mul_eq_mul_div, div_mul_div_comm, eq_div_iff (mul_ne_zero (pow_ne_zero 3 hw0z) hW)]
    linear_combination hz
  · have hQ0 := (hε k hk).2 (by omega)
    rw [ZMod.natCast_self, zero_pow htp.ne', zero_mul] at hm
    have h1 := (mul_eq_zero.1 hm).resolve_right (mul_ne_zero hKd hW)
    rw [hQ0, mul_zero, zero_mul]
    exact (mul_eq_zero.1 h1).resolve_right (pow_ne_zero 3 hw0z)

end Zeta2ANKernel
