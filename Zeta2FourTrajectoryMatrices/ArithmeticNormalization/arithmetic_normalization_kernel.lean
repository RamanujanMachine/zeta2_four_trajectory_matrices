import Zeta2FourTrajectoryMatrices.ArithmeticNormalization.arithmetic_normalization_chamber

open Polynomial Finset Zeta2Blueprint Zeta2NextTwo

noncomputable section

namespace Zeta2ANKernel

def Uf (p : ℕ) (x : ℤ) : ℤ := if (p : ℤ) ∣ x then x / p else x

def vb (p : ℕ) (x : ℤ) : ℕ := if (p : ℤ) ∣ x then 1 else 0

theorem Uf_spec (p : ℕ) (x : ℤ) : x = (p : ℤ) ^ vb p x * Uf p x := by
  unfold Uf vb
  by_cases h : (p : ℤ) ∣ x
  · rw [ite_eq_left h, ite_eq_left h, pow_one, Int.mul_ediv_cancel' h]
  · rw [ite_eq_right h, ite_eq_right h, pow_zero, one_mul]

theorem Uf_unit {p : ℕ} (pp : p.Prime) (x : ℤ) (h0 : x ≠ 0) (h1 : x.natAbs < p ^ 2) :
    ¬ (p : ℤ) ∣ Uf p x := by
  unfold Uf
  by_cases h : (p : ℤ) ∣ x
  · rw [ite_eq_left h]
    rintro ⟨z, hz⟩
    obtain ⟨y, rfl⟩ := h
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast pp.ne_zero
    rw [Int.mul_ediv_cancel_left _ hp0] at hz
    have h2 : ((p : ℤ) ^ 2) ∣ (p : ℤ) * y := ⟨z, by rw [hz, pow_two, mul_assoc]⟩
    have h3 := Int.natAbs_le_of_dvd_ne_zero h2 h0
    rw [Int.natAbs_pow, Int.natAbs_natCast] at h3
    omega
  · rw [ite_eq_right h]
    exact h

theorem Uf_res {p : ℕ} (hp : 0 < p) (y V : ℤ) : ((Uf p (y + p * V) : ℤ) : ZMod p) =
    if (p : ℤ) ∣ y then (((V + y / p) : ℤ) : ZMod p) else ((y : ℤ) : ZMod p) := by
  unfold Uf
  by_cases h : (p : ℤ) ∣ y
  · rw [ite_eq_left (dvd_add h (dvd_mul_right _ _)), ite_eq_left h,
      Int.add_mul_ediv_left y V (by exact_mod_cast hp.ne' : (p : ℤ) ≠ 0), add_comm]
  · rw [ite_eq_right (fun hh => h ((dvd_add_left (dvd_mul_right _ _)).1 hh)), ite_eq_right h,
      Int.cast_add,
      Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, add_zero]

theorem prod_Uf (p : ℕ) (I : Finset ℕ) (x : ℕ → ℤ) :
    ∏ i ∈ I, x i = (p : ℤ) ^ (∑ i ∈ I, vb p (x i)) * ∏ i ∈ I, Uf p (x i) := by
  rw [← prod_pow_eq_pow_sum, ← prod_mul_distrib]
  exact prod_congr rfl fun i _ => Uf_spec p (x i)

def Ecnt (p : ℕ) (y0 : ℤ) (n : ℕ) : ℕ := ∑ i ∈ range n, vb p (y0 - i)

def Wf (p : ℕ) (y0 : ℤ) (n : ℕ) (G : ℤ → ZMod p) : ZMod p :=
  ∏ t ∈ range (Ecnt p y0 n), G (y0 / p - t)

theorem floor_step {p : ℕ} (hp : 0 < p) (x : ℤ) :
    (x - 1) / p = if (p : ℤ) ∣ x then x / p - 1 else x / p := by
  have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  by_cases hd : (p : ℤ) ∣ x
  · rw [ite_eq_left hd]
    obtain ⟨q, rfl⟩ := hd
    rw [sub_eq_neg_add, Int.add_mul_ediv_left _ _ hp', Int.mul_ediv_cancel_left _ hp',
      neg_one_ediv _ (by exact_mod_cast hp), add_comm, ← sub_eq_add_neg]
  · rw [ite_eq_right hd]
    have hm := Int.emod_add_mul_ediv x p
    have hm1 : x % p ≠ 0 := fun h => hd (Int.dvd_of_emod_eq_zero h)
    have hm2 := Int.emod_nonneg x hp'
    have hm3 := Int.emod_lt_of_pos x (show (0 : ℤ) < p by exact_mod_cast hp)
    rw [show x - 1 = (x % p - 1) + p * (x / p) by omega, Int.add_mul_ediv_left _ _ hp',
      Int.ediv_eq_zero_of_lt (by omega) (by omega), zero_add]

theorem GLc {p : ℕ} (hp : 0 < p) (y0 : ℤ) (G : ℤ → ZMod p) : ∀ n : ℕ,
    (Ecnt p y0 n : ℤ) = y0 / p - (y0 - n) / p ∧
      ∏ i ∈ range n, (if (p : ℤ) ∣ y0 - i then G ((y0 - i) / p) else 1) = Wf p y0 n G
  | 0 => ⟨by rw [Ecnt, sum_range_zero, Nat.cast_zero, sub_zero, sub_self],
      by rw [prod_range_zero, Wf, Ecnt, sum_range_zero, prod_range_zero]⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := GLc hp y0 G n
    have hs := floor_step hp (y0 - n)
    rw [sub_sub, ← Nat.cast_succ] at hs
    rw [prod_range_succ, h2, Wf, Wf, Ecnt, sum_range_succ, ← Ecnt, vb]
    by_cases hd : (p : ℤ) ∣ y0 - n
    · rw [ite_eq_left hd] at hs
      rw [ite_eq_left hd, ite_eq_left hd, prod_range_succ, Nat.cast_add, Nat.cast_one, hs]
      refine ⟨by omega, ?_⟩
      rw [show y0 / p - (Ecnt p y0 n : ℕ) = (y0 - n) / p by omega]
    · rw [ite_eq_right hd] at hs
      rw [ite_eq_right hd, ite_eq_right hd, mul_one, add_zero, hs]
      exact ⟨h1, rfl⟩

def psi {p : ℕ} (y : ZMod p) : ZMod p := if y = 0 then 1 else y

theorem psi_ne_zero {p : ℕ} [Fact p.Prime] (y : ZMod p) : psi y ≠ 0 := by
  unfold psi
  by_cases h : y = 0
  · rw [ite_eq_left h]
    exact one_ne_zero
  · rw [ite_eq_right h]
    exact h

theorem res_split {p : ℕ} (y : ℤ) (A : ZMod p) :
    (if (p : ℤ) ∣ y then A else ((y : ℤ) : ZMod p)) =
      psi ((y : ℤ) : ZMod p) * (if (p : ℤ) ∣ y then A else 1) := by
  unfold psi
  by_cases h : (p : ℤ) ∣ y
  · rw [ite_eq_left h, ite_eq_left h, ite_eq_left ((ZMod.intCast_zmod_eq_zero_iff_dvd y p).2 h),
      one_mul]
  · rw [ite_eq_right h, ite_eq_right h,
      ite_eq_right (fun h' => h ((ZMod.intCast_zmod_eq_zero_iff_dvd y p).1 h')), mul_one]

theorem LFgen {p : ℕ} (pp : p.Prime) (I : Finset ℕ) (y0 V : ℤ) (G : ℤ → ZMod p)
    (hG : ∀ i ∈ I, (p : ℤ) ∣ y0 - i → G ((y0 - i) / p) = ((V + (y0 - i) / p : ℤ) : ZMod p))
    (hb : ∀ i ∈ I, y0 + p * V - i ≠ 0 ∧ -(p : ℤ) ^ 2 < y0 + p * V - i ∧ y0 + p * V - i < p ^ 2) :
    ∃ w : ℤ, ¬ (p : ℤ) ∣ w ∧ ∏ i ∈ I, (y0 + p * V - i) = (p : ℤ) ^ (∑ i ∈ I, vb p (y0 - i)) * w ∧
      (w : ZMod p) = (∏ i ∈ I, psi ((y0 - i : ℤ) : ZMod p)) *
        ∏ i ∈ I, (if (p : ℤ) ∣ y0 - i then G ((y0 - i) / p) else 1) := by
  refine ⟨∏ i ∈ I, Uf p (y0 + p * V - i), fun hd => ?_, ?_, ?_⟩
  · obtain ⟨i, hi, hdi⟩ := (Prime.dvd_finsetProd_iff (pz_prime pp) _).1 hd
    obtain ⟨h0, h1, h2⟩ := hb i hi
    have e := Nat.cast_pow (α := ℤ) p 2
    exact Uf_unit pp _ h0 (by omega) hdi
  · rw [prod_Uf p I (fun i => y0 + p * V - i)]
    congr 2
    refine sum_congr rfl fun i _ => ?_
    unfold vb
    rw [show y0 + p * V - i = (y0 - i) + p * V by ring]
    by_cases h : (p : ℤ) ∣ y0 - i
    · rw [ite_eq_left h, ite_eq_left (dvd_add h (dvd_mul_right _ _))]
    · rw [ite_eq_right h, ite_eq_right (fun hh => h ((dvd_add_left (dvd_mul_right _ _)).1 hh))]
  · rw [Int.cast_prod, ← prod_mul_distrib]
    refine prod_congr rfl fun i hi => ?_
    rw [show y0 + p * V - i = (y0 - i) + p * V by ring, Uf_res pp.pos, res_split]
    congr 1
    by_cases h : (p : ℤ) ∣ y0 - i
    · rw [ite_eq_left h, ite_eq_left h, hG i hi h]
    · rw [ite_eq_right h, ite_eq_right h]

theorem LF {p : ℕ} (pp : p.Prime) (y0 V : ℤ) (n : ℕ)
    (hb : ∀ i < n, 0 < y0 + p * V - i ∧ y0 + p * V - i < p ^ 2) :
    ∃ w : ℤ, ¬ (p : ℤ) ∣ w ∧ ∏ i ∈ range n, (y0 + p * V - i) = (p : ℤ) ^ Ecnt p y0 n * w ∧
      (w : ZMod p) = (∏ i ∈ range n, psi ((y0 - i : ℤ) : ZMod p)) *
        Wf p y0 n (fun x => ((V + x : ℤ) : ZMod p)) := by
  obtain ⟨w, hw, e1, e2⟩ := LFgen pp (range n) y0 V (fun x => ((V + x : ℤ) : ZMod p))
    (fun _ _ _ => rfl) (fun i hi => by
      obtain ⟨h1, h2⟩ := hb i (mem_range.1 hi)
      exact ⟨by omega, by omega, h2⟩)
  rw [(GLc pp.pos y0 (fun x => ((V + x : ℤ) : ZMod p)) n).2] at e2
  exact ⟨w, hw, e1, e2⟩

def Ms {p : ℕ} (c : ZMod p) (n : ℕ) : Multiset (ZMod p) :=
  (Multiset.range n).map fun i : ℕ => (i : ZMod p) - c

def Lk {p : ℕ} (k : ZMod p) (S : Multiset (ZMod p)) : ZMod p := (S.map fun a => psi (k - a)).prod

def Pm {p : ℕ} (S : Multiset (ZMod p)) : (ZMod p)[X] := (S.map fun a => X - C a).prod

theorem Lk_add {p : ℕ} (k : ZMod p) (S T : Multiset (ZMod p)) : Lk k (S + T) = Lk k S * Lk k T := by
  rw [Lk, Lk, Lk, Multiset.map_add, Multiset.prod_add]

theorem Lk_nsmul {p : ℕ} (k : ZMod p) (n : ℕ) (S : Multiset (ZMod p)) :
    Lk k (n • S) = Lk k S ^ n := by
  rw [Lk, Lk, Multiset.map_nsmul, Multiset.prod_nsmul]

theorem Pm_add {p : ℕ} (S T : Multiset (ZMod p)) : Pm (S + T) = Pm S * Pm T := by
  rw [Pm, Pm, Pm, Multiset.map_add, Multiset.prod_add]

theorem Pm_nsmul {p : ℕ} (n : ℕ) (S : Multiset (ZMod p)) : Pm (n • S) = Pm S ^ n := by
  rw [Pm, Pm, Multiset.map_nsmul, Multiset.prod_nsmul]

theorem Lk_ne_zero {p : ℕ} [Fact p.Prime] (k : ZMod p) (S : Multiset (ZMod p)) : Lk k S ≠ 0 :=
  Multiset.prod_ne_zero fun h => by
    obtain ⟨a, -, ha⟩ := Multiset.mem_map.1 h
    exact psi_ne_zero _ ha

theorem Lk_Ms {p : ℕ} (y0 c : ℤ) (n : ℕ) :
    ∏ i ∈ range n, psi ((y0 - i : ℤ) : ZMod p) =
      Lk ((y0 - c : ℤ) : ZMod p) (Ms ((c : ℤ) : ZMod p) n) := by
  rw [Lk, Ms, Multiset.map_map, prod_eq_multiset_prod]
  congr 1
  refine Multiset.map_congr rfl fun i _ => ?_
  rw [Function.comp_apply]
  congr 1
  push_cast
  ring

theorem eval_Pm_filter {p : ℕ} (k : ZMod p) (S : Multiset (ZMod p)) :
    (Pm (S.filter (· ≠ k))).eval k = Lk k S := by
  induction S using Multiset.induction_on with
  | empty => rw [Multiset.filter_zero, Pm, Lk, Multiset.map_zero, Multiset.map_zero,
      Multiset.prod_zero, Multiset.prod_zero, eval_one]
  | cons a S ih =>
    rw [Lk, Multiset.map_cons, Multiset.prod_cons, ← Lk, ← ih]
    by_cases h : a = k
    · rw [Multiset.filter_cons_of_neg (p := fun x => x ≠ k) S (fun h1 => h1 h), h, sub_self, psi,
        ite_eq_left rfl,
        one_mul]
    · rw [Multiset.filter_cons_of_pos (p := fun x => x ≠ k) S h, Pm, Multiset.map_cons,
        Multiset.prod_cons, ← Pm,
        eval_mul, eval_sub, eval_X, eval_C, psi,
        ite_eq_right (sub_ne_zero.2 (Ne.symm h))]

theorem Pm_split {p : ℕ} (k : ZMod p) (S : Multiset (ZMod p)) :
    Pm S = (X - C k) ^ S.count k * Pm (S.filter (· ≠ k)) := by
  conv_lhs => rw [← Multiset.filter_add_not (p := fun a => a = k) S]
  rw [Pm_add, Multiset.filter_eq', Pm, Multiset.map_replicate, Multiset.prod_replicate]

theorem PL {p : ℕ} [Fact p.Prime] (S T : Multiset (ZMod p)) (c : ZMod p) (Q : (ZMod p)[X])
    (h : C c * Pm S = Pm T * Q) (k : ZMod p) :
    (S.count k = T.count k → c * Lk k S = Lk k T * Q.eval k) ∧
      (T.count k < S.count k → Q.eval k = 0) := by
  rw [Pm_split k S, Pm_split k T] at h
  have hX : ∀ n : ℕ, (X - C k : (ZMod p)[X]) ^ n ≠ 0 := fun n => pow_ne_zero n (X_sub_C_ne_zero k)
  constructor
  · intro he
    rw [he, mul_left_comm, mul_assoc] at h
    have h2 := congrArg (eval k) (mul_left_cancel₀ (hX _) h)
    rw [eval_mul, eval_mul, eval_C, eval_Pm_filter, eval_Pm_filter] at h2
    exact h2
  · intro hlt
    obtain ⟨t, ht⟩ : ∃ t, S.count k = T.count k + (t + 1) := ⟨S.count k - T.count k - 1, by omega⟩
    rw [ht, pow_add, mul_left_comm, mul_assoc, mul_assoc] at h
    have h2 := congrArg (eval k) (mul_left_cancel₀ (hX _) h)
    rw [eval_mul, eval_mul, eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self,
      zero_pow (Nat.succ_ne_zero t), zero_mul, eval_Pm_filter] at h2
    exact (mul_eq_zero.1 h2.symm).resolve_left (Lk_ne_zero k T)

theorem Lk_univ {p : ℕ} [Fact p.Prime] (k : ZMod p) : Lk k (univ : Finset (ZMod p)).val = -1 := by
  have pp : p.Prime := Fact.out
  rw [Lk, ← prod_eq_multiset_prod,
    Fintype.prod_equiv (Equiv.subLeft k) (fun x => psi (k - x)) psi (fun x => rfl)]
  have e : ∏ b : ZMod p, psi b = ∏ x ∈ range p, psi ((x : ℕ) : ZMod p) :=
    prod_nbij' ZMod.val (fun x => (x : ZMod p)) (fun a _ => mem_range.2 (ZMod.val_lt a))
      (fun a _ => mem_univ _) (fun a _ => ZMod.natCast_zmod_val a)
      (fun a ha => ZMod.val_cast_of_lt (mem_range.1 ha)) (fun a _ => by rw [ZMod.natCast_zmod_val])
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := pp.one_lt; omega⟩
  have e2 : ∀ x ∈ range q, psi (((x + 1 : ℕ) : ℕ) : ZMod p) = ((x + 1 : ℕ) : ZMod p) :=
    fun x hx => by
      have := mem_range.1 hx
      rw [psi, ite_eq_right fun h0 => Nat.not_dvd_of_pos_of_lt (Nat.succ_pos x) (by omega)
        ((ZMod.natCast_eq_zero_iff (x + 1) p).1 h0)]
  rw [e, congrArg range hq, prod_range_succ', prod_congr rfl e2, Nat.cast_zero, psi,
    ite_eq_left rfl, mul_one, ← Nat.cast_prod, prod_range_add_one_eq_factorial,
    show q = p - 1 by omega, ZMod.wilsons_lemma]

theorem Ms_period {p : ℕ} [Fact p.Prime] (c : ZMod p) (n : ℕ) :
    Ms c (n + p) = Ms c n + (univ : Finset (ZMod p)).val := by
  rw [Ms, Multiset.range_add, Multiset.map_add, Multiset.map_map, ← Ms]
  congr 1
  apply Multiset.ext'
  intro a
  rw [Multiset.count_univ, show ((fun i : ℕ => (i : ZMod p) - c) ∘ (n + ·)) =
      fun i : ℕ => (i : ZMod p) - (c - n) by
    funext i
    rw [Function.comp_apply, Nat.cast_add]
    ring, count_S le_rfl a (c - n), ite_eq_left (ZMod.val_lt _)]

theorem Ms_split {p : ℕ} [Fact p.Prime] (c : ZMod p) (r : ℕ) :
    ∀ q : ℕ, Ms c (r + p * q) = q • (univ : Finset (ZMod p)).val + Ms c r
  | 0 => by rw [mul_zero, add_zero, zero_nsmul, zero_add]
  | q + 1 => by
    rw [Nat.mul_succ, ← add_assoc, Ms_period, Ms_split c r q, succ_nsmul, add_right_comm]

theorem Lk_split {p : ℕ} [Fact p.Prime] (k c : ZMod p) (n : ℕ) :
    Lk k (Ms c n) = (-1) ^ (n / p) * Lk k (Ms c (n % p)) := by
  conv_lhs => rw [← Nat.mod_add_div n p]
  rw [Ms_split, Lk_add, Lk_nsmul, Lk_univ]

theorem Lk_split' {p : ℕ} [Fact p.Prime] (k c : ZMod p) (r q : ℕ) :
    Lk k (Ms c (r + p * q)) = (-1) ^ q * Lk k (Ms c r) := by
  rw [Ms_split, Lk_add, Lk_nsmul, Lk_univ]

theorem binom_Pm {p : ℕ} [Fact p.Prime] (a : ZMod p) (b : ℕ) :
    binomPoly (ZMod p) a b = C ((b.factorial : ZMod p)⁻¹) * Pm (Ms a b) :=
  binom_prod a b

theorem Xp_Pm {p : ℕ} [Fact p.Prime] :
    (X ^ p - X : (ZMod p)[X]) = Pm (univ : Finset (ZMod p)).val :=
  Xp_prod

theorem Kpart (N p : ℕ) [Fact p.Prime] (Q : (ZMod p)[X])
    (hQ : binomPoly (ZMod p) ((9 * N : ℕ) : ZMod p) (8 * N % p) *
      binomPoly (ZMod p) ((10 * N : ℕ) : ZMod p) (8 * N % p) *
      binomPoly (ZMod p) ((11 * N : ℕ) : ZMod p) (8 * N % p) *
        (X ^ p - X) ^ (1 - (phi ((N : ℝ) / p)).toNat) =
      (X ^ p - X) ^ ((phi ((N : ℝ) / p)).toNat - 1) *
        (∏ j ∈ range (11 * N % p + 1), (X - C (j : ZMod p))) * Q) :
    ∃ ε : ZMod p, ∀ k : ℕ, k < p →
      (chi N p k = ((phi ((N : ℝ) / p)).toNat : ℤ) →
        Lk (k : ZMod p) (Ms ((9 * N : ℕ) : ZMod p) (8 * N)) *
          Lk (k : ZMod p) (Ms ((10 * N : ℕ) : ZMod p) (8 * N)) *
          Lk (k : ZMod p) (Ms ((11 * N : ℕ) : ZMod p) (8 * N)) =
        ε * Lk (k : ZMod p) (Ms 0 (11 * N + 1)) * Q.eval (k : ZMod p)) ∧
      (((phi ((N : ℝ) / p)).toNat : ℤ) < chi N p k → Q.eval (k : ZMod p) = 0) := by
  have pp : p.Prime := Fact.out
  have hp0 := pp.pos
  set h := (phi ((N : ℝ) / p)).toNat with hh
  have hb : 8 * N % p < p := Nat.mod_lt _ hp0
  have hd : 11 * N % p < p := Nat.mod_lt _ hp0
  set B : ZMod p := ((8 * N % p).factorial : ZMod p) with hB
  have hB0 : B ≠ 0 := fact_ne_zero hb
  have hg : (∏ j ∈ range (11 * N % p + 1), (X - C (j : ZMod p))) = Pm (Ms 0 (11 * N % p + 1)) := by
    rw [Pm, Ms, Multiset.map_map, prod_eq_multiset_prod]
    refine congrArg _ (Multiset.map_congr rfl fun i _ => ?_)
    rw [Function.comp_apply, sub_zero]
  have hP : C (B⁻¹ ^ 3) * Pm (Ms ((9 * N : ℕ) : ZMod p) (8 * N % p) +
      Ms ((10 * N : ℕ) : ZMod p) (8 * N % p) + Ms ((11 * N : ℕ) : ZMod p) (8 * N % p) +
      (1 - h) • (univ : Finset (ZMod p)).val) =
      Pm ((h - 1) • (univ : Finset (ZMod p)).val + Ms 0 (11 * N % p + 1)) * Q := by
    rw [binom_Pm, binom_Pm, binom_Pm, hg, Xp_Pm] at hQ
    rw [Pm_add, Pm_add, Pm_add, Pm_nsmul, Pm_add, Pm_nsmul, C_pow]
    linear_combination hQ
  refine ⟨(-1) ^ (8 * N / p) * (-1) ^ (8 * N / p) * (-1) ^ (8 * N / p) * (-1) ^ (1 - h) *
    (-1) ^ (h - 1) * (-1) ^ (11 * N / p) * B ^ 3, fun k hk => ?_⟩
  obtain ⟨E1, E2⟩ := PL _ _ _ Q hP (k : ZMod p)
  have hv : (k : ZMod p).val = k := ZMod.val_cast_of_lt hk
  have cL : Multiset.count (k : ZMod p) (Ms ((9 * N : ℕ) : ZMod p) (8 * N % p) +
      Ms ((10 * N : ℕ) : ZMod p) (8 * N % p) + Ms ((11 * N : ℕ) : ZMod p) (8 * N % p) +
      (1 - h) • (univ : Finset (ZMod p)).val) =
      (if (k + 9 * N) % p < 8 * N % p then 1 else 0) +
      (if (k + 10 * N) % p < 8 * N % p then 1 else 0) +
      (if (k + 11 * N) % p < 8 * N % p then 1 else 0) + (1 - h) := by
    rw [Multiset.count_add, Multiset.count_add, Multiset.count_add, Multiset.count_nsmul,
      Multiset.count_univ, mul_one, Ms, Ms, Ms, count_S hb.le, count_S hb.le, count_S hb.le,
      val_add_cast, val_add_cast, val_add_cast, hv]
  have cR : Multiset.count (k : ZMod p) ((h - 1) • (univ : Finset (ZMod p)).val +
      Ms 0 (11 * N % p + 1)) = (h - 1) + (if k < 11 * N % p + 1 then 1 else 0) := by
    rw [Multiset.count_add, Multiset.count_nsmul, Multiset.count_univ, mul_one, Ms,
      count_S (by omega : 11 * N % p + 1 ≤ p), add_zero, hv]
  have hc := chi_id N p k hp0 hk
  constructor
  · intro hch
    rw [hch] at hc
    have h1 := E1 (by rw [cL, cR]; split_ifs at hc ⊢ <;> omega)
    rw [Lk_add, Lk_add, Lk_add, Lk_nsmul, Lk_univ, Lk_add, Lk_nsmul, Lk_univ] at h1
    have e8 : 8 * N = 8 * N % p + p * (8 * N / p) := (Nat.mod_add_div _ _).symm
    have e11 : 11 * N + 1 = (11 * N % p + 1) + p * (11 * N / p) := by
      have := Nat.mod_add_div (11 * N) p
      omega
    rw [e8, Lk_split', Lk_split', Lk_split', e11, Lk_split', ← e8]
    have q1 : B * B⁻¹ = 1 := mul_inv_cancel₀ hB0
    have q2 : ((-1 : ZMod p) ^ (1 - h)) * (-1) ^ (1 - h) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    have q3 : ((-1 : ZMod p) ^ (11 * N / p)) * (-1) ^ (11 * N / p) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    linear_combination ((-1 : ZMod p) ^ (8 * N / p)) ^ 3 * (-1) ^ (1 - h) *
        ((-1 : ZMod p) ^ (11 * N / p)) ^ 2 * B ^ 3 * h1 -
      ((-1 : ZMod p) ^ (8 * N / p)) ^ 3 * (Lk (k : ZMod p) (Ms ((9 * N : ℕ) : ZMod p) (8 * N % p)) *
        Lk (k : ZMod p) (Ms ((10 * N : ℕ) : ZMod p) (8 * N % p)) *
        Lk (k : ZMod p) (Ms ((11 * N : ℕ) : ZMod p) (8 * N % p))) *
        (((B * B⁻¹) ^ 2 + B * B⁻¹ + 1) * q1 + (B * B⁻¹) ^ 3 * q3 +
          (B * B⁻¹) ^ 3 * ((-1 : ZMod p) ^ (11 * N / p)) ^ 2 * q2)
  · intro hlt
    exact E2 (by rw [cL, cR]; split_ifs at hc ⊢ <;> omega)

theorem CI (n t : ℕ) :
    ((n.choose t : ℕ) : ℤ) * (t.factorial : ℤ) = ∏ i ∈ range t, ((n : ℤ) - i) := by
  rw [← descPochhammer_eval_eq_prod_range, descPochhammer_eval_eq_descFactorial ℤ n t,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, mul_comm]

theorem PE (j : ℕ) : ∀ t : ℕ,
    ∏ i ∈ (range (j + t + 1)).erase j, ((j : ℤ) - i) = (-1) ^ t * j.factorial * t.factorial
  | 0 => by
    rw [add_zero, range_add_one, erase_insert notMem_range_self, pow_zero, one_mul,
      Nat.factorial_zero, Nat.cast_one, mul_one, ← IP_fact]
    rfl
  | t + 1 => by
    rw [show j + (t + 1) + 1 = (j + t + 1) + 1 by omega, range_add_one,
      erase_insert_of_ne (by omega), prod_insert (fun hm => by
        rw [mem_erase, mem_range] at hm
        omega), PE j t, Nat.factorial_succ, Nat.cast_mul]
    push_cast
    ring

theorem CJ (j m : ℕ) (h : j ≤ m) :
    (-1) ^ j * ((m.choose j : ℕ) : ℤ) * ∏ i ∈ (range (m + 1)).erase j, ((j : ℤ) - i) =
      (-1) ^ m * (m.factorial : ℤ) := by
  obtain ⟨t, rfl⟩ : ∃ t, m = j + t := ⟨m - j, by omega⟩
  have e := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right j t)
  rw [Nat.add_sub_cancel_left] at e
  rw [PE, ← e, pow_add]
  push_cast
  ring

def Gl (p : ℕ) (l : ℤ) (x : ℤ) : ZMod p := if l + x = 0 then 1 else ((l + x : ℤ) : ZMod p)

theorem LFe {p : ℕ} (pp : p.Prime) (j k m : ℕ) (l : ℤ) (hj : (j : ℤ) = k + p * l)
    (hjm : j ≤ m) (hm : m < p ^ 2) :
    ∃ w : ℤ, ¬ (p : ℤ) ∣ w ∧
      ∏ i ∈ (range (m + 1)).erase j, ((j : ℤ) - i) = (p : ℤ) ^ (Ecnt p k (m + 1) - 1) * w ∧
      (w : ZMod p) = (∏ i ∈ range (m + 1), psi (((k : ℤ) - i : ℤ) : ZMod p)) *
        Wf p k (m + 1) (Gl p l) := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast pp.ne_zero
  have hjr : j ∈ range (m + 1) := mem_range.2 (by omega)
  have hdj : (p : ℤ) ∣ (k : ℤ) - j := ⟨-l, by rw [hj]; ring⟩
  have hdiv : ((k : ℤ) - j) / p = -l := by
    rw [show (k : ℤ) - j = p * -l by rw [hj]; ring, Int.mul_ediv_cancel_left _ hp0]
  have e2 := Nat.cast_pow (α := ℤ) p 2
  obtain ⟨w, hw, e1, er⟩ := LFgen pp ((range (m + 1)).erase j) (k : ℤ) l (Gl p l)
    (fun i hi hd => by
      have hij := (mem_erase.1 hi).1
      unfold Gl
      rw [ite_eq_right fun h0 => hij ?_]
      obtain ⟨q, hq⟩ := hd
      rw [hq, Int.mul_ediv_cancel_left _ hp0] at h0
      have : (i : ℤ) = j := by rw [hj]; linear_combination (-p : ℤ) * h0 - hq
      exact_mod_cast this)
    (fun i hi => by
      have hij := (mem_erase.1 hi).1
      have him := mem_range.1 (mem_erase.1 hi).2
      have hne : (i : ℤ) ≠ j := fun h => hij (by exact_mod_cast h)
      refine ⟨by rw [← hj]; exact sub_ne_zero.2 hne.symm, ?_, ?_⟩ <;> rw [← hj] <;> omega)
  have hs := add_sum_erase (range (m + 1)) (fun i => vb p ((k : ℤ) - i)) hjr
  rw [vb, ite_eq_left hdj, ← Ecnt] at hs
  refine ⟨w, hw, ?_, ?_⟩
  · rw [← hs, Nat.add_sub_cancel_left, ← e1]
    exact prod_congr rfl fun i _ => by rw [hj]
  · rw [er, prod_erase _ (by rw [psi, ite_eq_left ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hdj)]),
      prod_erase _ (by rw [ite_eq_left hdj, hdiv, Gl, ite_eq_left (add_neg_cancel l)]),
      (GLc pp.pos (k : ℤ) (Gl p l) (m + 1)).2]

theorem Lk0 {p : ℕ} (k n : ℕ) :
    ∏ i ∈ range n, psi ((((k : ℤ) - i : ℤ)) : ZMod p) = Lk (k : ZMod p) (Ms 0 n) := by
  rw [Lk_Ms (k : ℤ) 0 n, sub_zero, Int.cast_zero, Int.cast_natCast]

theorem NUM1 {p : ℕ} (pp : p.Prime) (n k c B : ℕ) (V : ℤ) (hn : (n : ℤ) = k + p * V)
    (hBc : B ≤ c) (hb : n + c < p ^ 2) :
    ∃ α : ℤ, ¬ (p : ℤ) ∣ α ∧
      ∏ i ∈ range B, (((n + c : ℕ) : ℤ) - i) = (p : ℤ) ^ Ecnt p ((k + c : ℕ) : ℤ) B * α ∧
      (α : ZMod p) = Lk (k : ZMod p) (Ms ((c : ℕ) : ZMod p) B) *
        Wf p ((k + c : ℕ) : ℤ) B (fun x => ((V + x : ℤ) : ZMod p)) := by
  have e : ((k + c : ℕ) : ℤ) + p * V = ((n + c : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_add, hn]
    ring
  have e2 := Nat.cast_pow (α := ℤ) p 2
  have hb' : ((n + c : ℕ) : ℤ) < ((p ^ 2 : ℕ) : ℤ) := by exact_mod_cast hb
  obtain ⟨α, hα, h1, h2⟩ := LF pp ((k + c : ℕ) : ℤ) V B (fun i hi => by
    rw [e]
    have : ((i : ℕ) : ℤ) < ((B : ℕ) : ℤ) := by exact_mod_cast hi
    have : ((B : ℕ) : ℤ) ≤ ((c : ℕ) : ℤ) := by exact_mod_cast hBc
    push_cast at hb' ⊢
    omega)
  refine ⟨α, hα, by rw [← h1, e], ?_⟩
  rw [h2, Lk_Ms _ (c : ℤ), Nat.cast_add, add_sub_cancel_right, Int.cast_natCast, Int.cast_natCast]

theorem DENr {p : ℕ} (pp : p.Prime) (k m : ℕ) (V : ℤ) (h1 : (m : ℤ) < k + p * V)
    (h2 : (k : ℤ) + p * V < p ^ 2) :
    ∃ β : ℤ, ¬ (p : ℤ) ∣ β ∧
      ∏ i ∈ range (m + 1), ((k : ℤ) + p * V - i) = (p : ℤ) ^ Ecnt p k (m + 1) * β ∧
      (β : ZMod p) = Lk (k : ZMod p) (Ms 0 (m + 1)) *
        Wf p k (m + 1) (fun x => ((V + x : ℤ) : ZMod p)) := by
  obtain ⟨β, hβ, e1, e2⟩ := LF pp (k : ℤ) V (m + 1) (fun i hi => by
    have : ((i : ℕ) : ℤ) < ((m + 1 : ℕ) : ℤ) := by exact_mod_cast hi
    push_cast at this
    omega)
  exact ⟨β, hβ, e1, by rw [e2, Lk0]⟩

theorem chi_min' (N p : ℕ) (hp0 : 0 < p) :
    ∃ k : ℕ, k < p ∧ chi N p k = ((phi ((N : ℝ) / p)).toNat : ℤ) := by
  by_contra hne
  have H : ∀ k : ℤ, 0 ≤ k → k < p → ((phi ((N : ℝ) / p)).toNat : ℤ) + 1 ≤ chi N p k :=
    fun k hk0 hk => by
      obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
      have h1 := hp_le_chi N p hp0 m
      have h2 : chi N p m ≠ ((phi ((N : ℝ) / p)).toNat : ℤ) := fun he => hne ⟨m, by omega, he⟩
      omega
  have h3 := phi_ge N p hp0 _ H
  have h4 : ((phi ((N : ℝ) / p)).toNat : ℤ) = phi ((N : ℝ) / p) :=
    Int.toNat_of_nonneg (phi_nonneg N p hp0)
  omega

theorem Wf_congr (p : ℕ) (hp : 0 < p) (y0 y0' : ℤ) (n : ℕ) (G : ℤ → ZMod p)
    (h1 : y0 / p = y0' / p) (h2 : (y0 - n) / p = (y0' - n) / p) : Wf p y0 n G = Wf p y0' n G := by
  have e1 := (GLc hp y0 G n).1
  have e2 := (GLc hp y0' G n).1
  have hE : Ecnt p y0 n = Ecnt p y0' n := by
    have : (Ecnt p y0 n : ℤ) = Ecnt p y0' n := by rw [e1, e2, h1, h2]
    exact_mod_cast this
  unfold Wf
  rw [hE, h1]

theorem WCnum (A B c p k k' : ℕ) (hp : 0 < p) (hc : A + B = c) (hq : (k + c) / p = (k' + c) / p)
    (hd : ((k + c) % p < B % p ↔ (k' + c) % p < B % p)) (G : ℤ → ZMod p) :
    Wf p ((k + c : ℕ) : ℤ) B G = Wf p ((k' + c : ℕ) : ℤ) B G := by
  subst hc
  have c1 := carry_nat (k + A) B p hp
  have c2 := carry_nat (k' + A) B p hp
  rw [← add_assoc, ← add_assoc] at hq hd
  have hq2 : (k + A) / p = (k' + A) / p := by
    by_cases h : (k + A + B) % p < B % p
    · rw [ite_eq_left h] at c1
      rw [ite_eq_left (hd.1 h)] at c2
      omega
    · rw [ite_eq_right h] at c1
      rw [ite_eq_right (fun h' => h (hd.2 h'))] at c2
      omega
  apply Wf_congr p hp
  · rw [← Int.natCast_div, ← Int.natCast_div, ← add_assoc, ← add_assoc, hq]
  · rw [show ((k + (A + B) : ℕ) : ℤ) - ((B : ℕ) : ℤ) = ((k + A : ℕ) : ℤ) by push_cast; ring,
      show ((k' + (A + B) : ℕ) : ℤ) - ((B : ℕ) : ℤ) = ((k' + A : ℕ) : ℤ) by push_cast; ring,
      ← Int.natCast_div, ← Int.natCast_div, hq2]

theorem WCden (N p k k' : ℕ) (hp : 0 < p) (hk : k < p) (hk' : k' < p) (hkN : k ≤ 11 * N)
    (hk'N : k' ≤ 11 * N) (he : 11 * N % p < k ↔ 11 * N % p < k') (G : ℤ → ZMod p) :
    Wf p (k : ℤ) (11 * N + 1) G = Wf p (k' : ℤ) (11 * N + 1) G := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  apply Wf_congr p hp
  · rw [Int.ediv_eq_zero_of_lt (by omega) (by exact_mod_cast hk),
      Int.ediv_eq_zero_of_lt (by omega) (by exact_mod_cast hk')]
  · have c1 := carry_nat (11 * N - k) k p hp
    have c2 := carry_nat (11 * N - k') k' p hp
    rw [Nat.sub_add_cancel hkN, Nat.div_eq_of_lt hk, Nat.mod_eq_of_lt hk] at c1
    rw [Nat.sub_add_cancel hk'N, Nat.div_eq_of_lt hk', Nat.mod_eq_of_lt hk'] at c2
    have hq : (11 * N - k) / p = (11 * N - k') / p := by
      by_cases h : 11 * N % p < k
      · rw [ite_eq_left h] at c1
        rw [ite_eq_left (he.1 h)] at c2
        omega
      · rw [ite_eq_right h] at c1
        rw [ite_eq_right (fun h' => h (he.2 h'))] at c2
        omega
    rw [show (k : ℤ) - ((11 * N + 1 : ℕ) : ℤ) = -((11 * N - k : ℕ) : ℤ) - 1 by
        push_cast [Nat.cast_sub hkN]; ring,
      show (k' : ℤ) - ((11 * N + 1 : ℕ) : ℤ) = -((11 * N - k' : ℕ) : ℤ) - 1 by
        push_cast [Nat.cast_sub hk'N]; ring,
      neg_ediv' _ _ hp', neg_ediv' _ _ hp', ← Int.natCast_div, ← Int.natCast_div, hq]

theorem EXP (N p k : ℕ) (hp : 0 < p) (hk : k < p) :
    (Ecnt p ((k + 9 * N : ℕ) : ℤ) (8 * N) : ℤ) + Ecnt p ((k + 10 * N : ℕ) : ℤ) (8 * N) +
      Ecnt p ((k + 11 * N : ℕ) : ℤ) (8 * N) + ((11 * N / p : ℕ) : ℤ) + 1 =
      chi N p k + 3 * ((8 * N / p : ℕ) : ℤ) + Ecnt p k (11 * N + 1) := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  rw [(GLc hp _ (fun _ => (0 : ZMod p)) _).1, (GLc hp _ (fun _ => (0 : ZMod p)) _).1,
    (GLc hp _ (fun _ => (0 : ZMod p)) _).1, (GLc hp _ (fun _ => (0 : ZMod p)) _).1]
  unfold chi chi2
  have t0 : (k : ℤ) / p = 0 := Int.ediv_eq_zero_of_lt (by omega) (by exact_mod_cast hk)
  have f9 : ((k + 9 * N : ℕ) : ℤ) / p = (9 * N + k) / p := by push_cast; rw [add_comm]
  have f10 : ((k + 10 * N : ℕ) : ℤ) / p = (10 * N + k) / p := by push_cast; rw [add_comm]
  have f11 : ((k + 11 * N : ℕ) : ℤ) / p = (11 * N + k) / p := by push_cast; rw [add_comm]
  have g9 : (((k + 9 * N : ℕ) : ℤ) - ((8 * N : ℕ) : ℤ)) / p = (N + k) / p := by
    congr 1; push_cast; ring
  have g10 : (((k + 10 * N : ℕ) : ℤ) - ((8 * N : ℕ) : ℤ)) / p = (2 * N + k) / p := by
    congr 1; push_cast; ring
  have g11 : (((k + 11 * N : ℕ) : ℤ) - ((8 * N : ℕ) : ℤ)) / p = (3 * N + k) / p := by
    congr 1; push_cast; ring
  have gL : ((k : ℤ) - ((11 * N + 1 : ℕ) : ℤ)) / p = -((11 * N + -k) / p) - 1 := by
    rw [← neg_ediv' _ _ hp']
    congr 1
    push_cast
    ring
  have hM : ((11 * N / p : ℕ) : ℤ) = (11 * N : ℤ) / p := by rw [Int.natCast_div]; push_cast; rfl
  have ha : ((8 * N / p : ℕ) : ℤ) = (8 * N : ℤ) / p := by rw [Int.natCast_div]; push_cast; rfl
  rw [f9, f10, f11, g9, g10, g11, gL, hM, ha, t0]
  omega

end Zeta2ANKernel
