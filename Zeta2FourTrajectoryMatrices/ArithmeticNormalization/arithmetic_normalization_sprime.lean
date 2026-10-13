import Zeta2FourTrajectoryMatrices.ArithmeticNormalization.arithmetic_normalization_chamber

open Polynomial Finset Zeta2Blueprint Zeta2NextTwo

noncomputable section

namespace Zeta2ANSprime

def Rd (p : ℕ) (q : ℚ) (x : ZMod p) : Prop :=
  ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q * b = a ∧ (a : ZMod p) = x * b

theorem zne_of_ndvd {p : ℕ} {b : ℤ} (hb : ¬ (p : ℤ) ∣ b) : (b : ZMod p) ≠ 0 :=
  fun h => hb ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).1 h)

theorem Rd_of_mul {p : ℕ} [Fact p.Prime] (q : ℚ) (a b : ℤ) (hb : ¬ (p : ℤ) ∣ b) (e : q * b = a) :
    Rd p q ((a : ZMod p) * (b : ZMod p)⁻¹) :=
  ⟨a, b, hb, e, by rw [mul_assoc, inv_mul_cancel₀ (zne_of_ndvd hb), mul_one]⟩

theorem Rd_int {p : ℕ} (pp : p.Prime) (z : ℤ) : Rd p (z : ℚ) (z : ZMod p) :=
  ⟨z, 1, not_dvd_one' pp, by rw [Int.cast_one, mul_one], by rw [Int.cast_one, mul_one]⟩

theorem Rd_mul {p : ℕ} (pp : p.Prime) {q1 q2 : ℚ} {x1 x2 : ZMod p} (h1 : Rd p q1 x1)
    (h2 : Rd p q2 x2) : Rd p (q1 * q2) (x1 * x2) := by
  obtain ⟨a1, b1, hb1, e1, f1⟩ := h1
  obtain ⟨a2, b2, hb2, e2, f2⟩ := h2
  refine ⟨a1 * a2, b1 * b2, fun h => ((pz_prime pp).dvd_or_dvd h).elim hb1 hb2, ?_, ?_⟩
  · rw [Int.cast_mul, Int.cast_mul, ← e1, ← e2, mul_mul_mul_comm]
  · rw [Int.cast_mul, Int.cast_mul, f1, f2, mul_mul_mul_comm]

theorem Rd_add {p : ℕ} (pp : p.Prime) {q1 q2 : ℚ} {x1 x2 : ZMod p} (h1 : Rd p q1 x1)
    (h2 : Rd p q2 x2) : Rd p (q1 + q2) (x1 + x2) := by
  obtain ⟨a1, b1, hb1, e1, f1⟩ := h1
  obtain ⟨a2, b2, hb2, e2, f2⟩ := h2
  refine ⟨a1 * b2 + a2 * b1, b1 * b2, fun h => ((pz_prime pp).dvd_or_dvd h).elim hb1 hb2, ?_, ?_⟩
  · rw [Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_mul, ← e1, ← e2]
    ring
  · rw [Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_mul, f1, f2]
    ring

theorem Rd_neg {p : ℕ} {q : ℚ} {x : ZMod p} (h : Rd p q x) : Rd p (-q) (-x) := by
  obtain ⟨a, b, hb, e, f⟩ := h
  exact ⟨-a, b, hb, by rw [Int.cast_neg, ← e, neg_mul], by rw [Int.cast_neg, f, neg_mul]⟩

theorem Rd_sub {p : ℕ} (pp : p.Prime) {q1 q2 : ℚ} {x1 x2 : ZMod p} (h1 : Rd p q1 x1)
    (h2 : Rd p q2 x2) : Rd p (q1 - q2) (x1 - x2) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact Rd_add pp h1 (Rd_neg h2)

theorem Rd_sum {p : ℕ} (pp : p.Prime) {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (x : ι → ZMod p) (H : ∀ i ∈ s, Rd p (f i) (x i)) : Rd p (∑ i ∈ s, f i) (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 := Rd_int pp 0
    rw [Int.cast_zero, Int.cast_zero] at h0
    rw [sum_empty, sum_empty]
    exact h0
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact Rd_add pp (H a (mem_insert_self a s)) (ih fun i hi => H i (mem_insert_of_mem hi))

theorem Rd_val {p : ℕ} [Fact p.Prime] {q : ℚ} {x : ZMod p} (h : Rd p q x) (u w : ℤ)
    (e : q * u = w) :
    (w : ZMod p) = x * u := by
  obtain ⟨a, b, hb, e1, f⟩ := h
  have hz : w * b = a * u := by
    have : ((w * b : ℤ) : ℚ) = ((a * u : ℤ) : ℚ) := by
      rw [Int.cast_mul, Int.cast_mul, ← e, ← e1, mul_right_comm]
    exact_mod_cast this
  have hz' := congrArg (fun z : ℤ => (z : ZMod p)) hz
  simp only [Int.cast_mul] at hz'
  rw [f, mul_right_comm] at hz'
  exact mul_right_cancel₀ (zne_of_ndvd hb) hz'

theorem zmod_inj_lt {p i j : ℕ} (hi : i < p) (hj : j < p) (h : (i : ZMod p) = j) : i = j := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h

theorem zK {p : ℕ} [Fact p.Prime] (f : (ZMod p)[X]) (n : ℕ) (hf : f.natDegree < n)
    (v : ℕ → ZMod p) (hv : ∀ i < n, ∀ j < n, v i = v j → i = j)
    (h : ∀ i < n, f.eval (v i) = 0) : f = 0 :=
  eq_zero_of_degree_lt_of_eval_index_eq_zero (range n) (v := v)
    (fun i hi j hj e => hv i (mem_range.1 hi) j (mem_range.1 hj) e)
    (by rw [card_range]; exact degree_le_natDegree.trans_lt (by exact_mod_cast hf))
    (fun i hi => h i (mem_range.1 hi))

theorem polyfrac {p : ℕ} [Fact p.Prime] (f : (ZMod p)[X]) (K M : ℕ) (hK : K + 1 < p)
    (hf : f.natDegree < K) (e : ZMod p)
    (h : ∀ i < K + 1,
      (((M + (i + 1) : ℕ) : ZMod p) - M) * f.eval ((M + (i + 1) : ℕ) : ZMod p) = e) :
    f = 0 := by
  have hR : (X - C (M : ZMod p)) * f - C e = 0 := by
    refine zK _ (K + 1) ?_ (fun i => ((M + (i + 1) : ℕ) : ZMod p)) (fun i hi j hj hij => ?_)
      (fun i hi => ?_)
    · refine (natDegree_sub_le _ _).trans_lt (max_lt ((natDegree_mul_le).trans_lt ?_) ?_)
      · rw [natDegree_X_sub_C]; omega
      · rw [natDegree_C]; omega
    · have hij' : (M : ZMod p) + ((i + 1 : ℕ) : ZMod p) =
          (M : ZMod p) + ((j + 1 : ℕ) : ZMod p) := by
        rw [← Nat.cast_add, ← Nat.cast_add]
        exact hij
      have := zmod_inj_lt (p := p) (i := i + 1) (j := j + 1) (by omega) (by omega)
        (add_left_cancel hij')
      omega
    · rw [eval_sub, eval_mul, eval_sub, eval_X, eval_C, eval_C, h i hi, sub_self]
  have he : e = 0 := by
    have := congrArg (eval (M : ZMod p)) hR
    rwa [eval_sub, eval_mul, eval_sub, eval_X, eval_C, eval_C, sub_self, zero_mul, zero_sub,
      eval_zero, neg_eq_zero] at this
  rw [he, C_0, sub_zero] at hR
  exact (mul_eq_zero.1 hR).resolve_left (X_sub_C_ne_zero _)

theorem lucas0 {p : ℕ} [Fact p.Prime] (n t : ℕ) :
    (((p * n).choose t : ℕ) : ZMod p) =
      ((Nat.choose 0 (t % p) * n.choose (t / p) : ℕ) : ZMod p) := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := p * n) (k := t)
  rw [Nat.mul_mod_right, Nat.mul_div_cancel_left n (Fact.out : p.Prime).pos] at h
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 h

theorem blk1 {R : Type*} [CommRing R] (f : ℕ → R) (p n : ℕ) (hp : 0 < p) :
    ∀ K : ℕ, ∑ t ∈ range (p * K), f t * ((Nat.choose 0 (t % p) * n.choose (t / p) : ℕ) : R) =
      ∑ m ∈ range K, f (p * m) * (n.choose m : R)
  | 0 => by rw [mul_zero, sum_range_zero, sum_range_zero]
  | K + 1 => by
    rw [Nat.mul_succ, sum_range_add, blk1 f p n hp K, sum_range_succ]
    congr 1
    rw [sum_eq_single 0 (fun i hi hi0 => ?_) (fun h => absurd (mem_range.2 hp) h)]
    · rw [add_zero, Nat.mul_mod_right, Nat.mul_div_cancel_left K hp, Nat.choose_self, one_mul]
    · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (mem_range.1 hi),
        Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hi0), zero_mul, Nat.cast_zero, mul_zero]

theorem choose_zmod {p : ℕ} [Fact p.Prime] (n m : ℕ) (hm : m < p) :
    (n.choose m : ZMod p) =
      ((m.factorial : ZMod p))⁻¹ * (descPochhammer (ZMod p) m).eval (n : ZMod p) := by
  rw [descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul,
    inv_mul_cancel_left₀ (fact_ne_zero hm)]

theorem dl_int (P : ℚ[X]) (wf : ℤ → ℤ) (hw : ∀ z : ℤ, P.eval (z : ℚ) = wf z) (x0 : ℤ) :
    ∃ D : ℕ → ℤ, ∀ t, Zeta2FirstThree.dl t P x0 = (D t : ℚ) :=
  ⟨fun t => ∑ i ∈ range (t + 1), (-1) ^ (t - i) * (t.choose i : ℤ) * wf (i + x0), fun t => by
    rw [Zeta2FirstThree.dl, Int.cast_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [Int.cast_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast,
      ← hw,
      Int.cast_add, Int.cast_natCast]⟩

theorem redA0 {p : ℕ} [Fact p.Prime] (P : ℚ[X]) (wf : ℤ → ℤ)
    (hw : ∀ z : ℤ, P.eval (z : ℚ) = wf z) (K : ℕ) (hK1 : 1 ≤ K) (hK : K ≤ p)
    (hdeg : P.natDegree < p * K) (x0 : ℤ) :
    ∃ H : (ZMod p)[X], H.natDegree < K ∧
      ∀ n : ℕ, (wf (x0 + p * n) : ZMod p) = H.eval (n : ZMod p) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨D, hD⟩ := dl_int P wf hw x0
  refine ⟨∑ m ∈ range K, C ((D (p * m) : ZMod p) * ((m.factorial : ZMod p))⁻¹) *
    descPochhammer (ZMod p) m, ?_, fun n => ?_⟩
  · refine (natDegree_sum_le_of_forall_le _ _ (n := K - 1) fun m hm => ?_).trans_lt (by omega)
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [descPochhammer_natDegree]
    have := mem_range.1 hm
    omega
  · have hN := congrArg (eval ((p * n : ℕ) : ℚ)) (Zeta2FirstThree.newton P (x0 : ℚ) (p * K) hdeg)
    rw [eval_comp, eval_add, eval_X, eval_C, eval_finsetSum] at hN
    have hz : ((wf (x0 + p * n) : ℤ) : ℚ) =
        ((∑ t ∈ range (p * K), D t * ((p * n).choose t : ℤ) : ℤ) : ℚ) := by
      rw [← hw, Int.cast_sum,
        show ((x0 + p * n : ℤ) : ℚ) = ((p * n : ℕ) : ℚ) + x0 by push_cast; ring,
        hN]
      refine sum_congr rfl fun t _ => ?_
      rw [eval_mul, eval_C, Zeta2FirstThree.bin_eval_nat, hD, Int.cast_mul, Int.cast_natCast]
    rw [Int.cast_inj.1 hz, Int.cast_sum, eval_finsetSum]
    have e1 : ∀ t ∈ range (p * K), ((D t * ((p * n).choose t : ℤ) : ℤ) : ZMod p) =
        (D t : ZMod p) * ((Nat.choose 0 (t % p) * n.choose (t / p) : ℕ) : ZMod p) := fun t _ => by
      rw [Int.cast_mul, Int.cast_natCast, lucas0]
    rw [sum_congr rfl e1, blk1 (fun t => (D t : ZMod p)) p n hp0 K]
    refine sum_congr rfl fun m hm => ?_
    rw [eval_mul, eval_C, choose_zmod n m (by have := mem_range.1 hm; omega), mul_assoc]

theorem redA {p : ℕ} [Fact p.Prime] (P : ℚ[X]) (wf : ℤ → ℤ)
    (hw : ∀ z : ℤ, P.eval (z : ℚ) = wf z) (K : ℕ) (hK1 : 1 ≤ K) (hK : K ≤ p)
    (hdeg : P.natDegree < p * K) (c : ℤ) :
    ∃ G : (ZMod p)[X], G.natDegree < K ∧
      ∀ V : ℤ, (wf (c + p * V) : ZMod p) = G.eval (V : ZMod p) := by
  obtain ⟨G, hG, hGn⟩ := redA0 P wf hw K hK1 hK hdeg c
  refine ⟨G, hG, fun V => ?_⟩
  obtain ⟨H, hH, hHn⟩ := redA0 P wf hw K hK1 hK hdeg (c + p * V)
  have e : H - G.comp (X + C (V : ZMod p)) = 0 := by
    refine zK _ K ?_ (fun i => (((-V).toNat + i : ℕ) : ZMod p)) (fun i hi j hj hij => ?_)
      (fun i hi => ?_)
    · refine (natDegree_sub_le _ _).trans_lt (max_lt hH ?_)
      rw [natDegree_comp, natDegree_X_add_C, mul_one]
      exact hG
    · rw [Nat.cast_add, Nat.cast_add] at hij
      have := zmod_inj_lt (p := p) (i := i) (j := j) (by omega) (by omega) (add_left_cancel hij)
      exact this
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = (((-V).toNat + i : ℕ) : ℤ) + V :=
        ⟨((-V).toNat + i + V).toNat, by omega⟩
      have hmz : (((-V).toNat + i : ℕ) : ZMod p) + (V : ZMod p) = (m : ZMod p) := by
        have := congrArg (fun z : ℤ => (z : ZMod p)) hm
        rw [Int.cast_natCast, Int.cast_add, Int.cast_natCast] at this
        exact this.symm
      rw [eval_sub, eval_comp, eval_add, eval_X, eval_C, ← hHn, sub_eq_zero, hmz, ← hGn m, hm]
      congr 2
      ring
  have e0 := congrArg (eval 0) e
  rw [eval_sub, eval_comp, eval_add, eval_X, eval_C, zero_add, eval_zero, sub_eq_zero] at e0
  have h0 := hHn 0
  simp only [Nat.cast_zero, mul_zero, add_zero] at h0
  rw [h0, e0]

theorem blk2 {R : Type*} [AddCommMonoid R] (F : ℕ → R) (p k : ℕ) (hk : k < p) (M e : ℕ)
    (he : e ≤ p) : ∑ j ∈ range (p * M + e), (if j % p = k then F (j / p) else 0) =
      ∑ l ∈ range M, F l + (if k < e then F M else 0) := by
  have hp0 : 0 < p := by omega
  have key : ∀ m n, n ≤ p →
      ∑ i ∈ range n, (if (p * m + i) % p = k then F ((p * m + i) / p) else 0) =
      if k < n then F m else 0 := fun m n hn => by
    have e1 : ∀ i ∈ range n, (if (p * m + i) % p = k then F ((p * m + i) / p) else 0) =
        if i = k then F m else 0 := fun i hi => by
      have := mem_range.1 hi
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega), Nat.mul_add_div hp0,
        Nat.div_eq_of_lt (by omega), add_zero]
    rw [sum_congr rfl e1, sum_ite_eq' (range n) k (fun _ => F m)]
    by_cases hkn : k < n
    · rw [ite_eq_left (mem_range.2 hkn), ite_eq_left hkn]
    · rw [ite_eq_right (fun h => hkn (mem_range.1 h)), ite_eq_right hkn]
  have full : ∀ M, ∑ j ∈ range (p * M), (if j % p = k then F (j / p) else 0) = ∑ l ∈ range M, F l :=
    fun M => by
      induction M with
      | zero => rw [mul_zero, sum_range_zero, sum_range_zero]
      | succ M ih =>
        rw [Nat.mul_succ, sum_range_add, ih, key M p le_rfl, ite_eq_left hk, sum_range_succ]
  rw [sum_range_add, full M, key M e he]

theorem reidx {p : ℕ} [Fact p.Prime] (M d k : ℕ) (hd : d < p) (hk : k < p)
    (cr qk κ uV y : ZMod p) (A : ℕ → ZMod p) :
    cr * (qk * uV) - ∑ j ∈ range (p * M + (d + 1)), (if j % p = k then
        cr * (κ * qk * A (j / p)) * (y - ((j / p : ℕ) : ZMod p))⁻¹ else 0) =
      cr * qk * (uV - κ * ∑ l ∈ range M, A l * (y - l)⁻¹ -
        (if k ≤ d then 1 else 0) * κ * A M * (y - M)⁻¹) := by
  rw [blk2 (fun l => cr * (κ * qk * A l) * (y - (l : ZMod p))⁻¹) p k hk M (d + 1) (by omega)]
  have hs : ∑ l ∈ range M, cr * (κ * qk * A l) * (y - (l : ZMod p))⁻¹ =
      cr * qk * κ * ∑ l ∈ range M, A l * (y - l)⁻¹ := by
    rw [mul_sum]
    exact sum_congr rfl fun l _ => by ring
  rw [hs]
  by_cases hkd : k ≤ d
  · rw [ite_eq_left (by omega : k < d + 1), ite_eq_left hkd]
    ring
  · rw [ite_eq_right (by omega : ¬ k < d + 1), ite_eq_right hkd]
    ring

theorem psq (p c : ℕ) (h : p ≤ c) : p ^ 2 ≤ c * p := by
  rw [sq]
  exact Nat.mul_le_mul_right p h

theorem shellK (N r p : ℕ) (hp2 : 50 * N < p ^ 2) (hsh : InShell N r p) :
    ∃ K : ℕ, 2 ≤ K ∧ 13 * N + r < p * K ∧ 3 * K + 1 ≤ p := by
  rcases hsh with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨2, le_rfl, by omega, Nat.not_lt.1 fun hc => ?_⟩
    have := psq p 6 (by omega)
    omega
  · refine ⟨3, by omega, by omega, Nat.not_lt.1 fun hc => ?_⟩
    have := psq p 9 (by omega)
    omega
  · refine ⟨4, by omega, by omega, Nat.not_lt.1 fun hc => ?_⟩
    have := psq p 12 (by omega)
    omega
  · refine ⟨5, by omega, by omega, Nat.not_lt.1 fun hc => ?_⟩
    have := psq p 15 (by omega)
    omega
  · refine ⟨6, by omega, by omega, Nat.not_lt.1 fun hc => ?_⟩
    have := psq p 18 (by omega)
    omega
  · refine ⟨12, by omega, by omega, Nat.not_lt.1 fun hc => ?_⟩
    have := psq p 36 (by omega)
    omega

end Zeta2ANSprime
