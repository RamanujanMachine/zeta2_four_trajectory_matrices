import Zeta2FourTrajectoryMatrices.FiniteReadout.blueprint_next_two

open Polynomial Finset Zeta2Blueprint Zeta2FirstThree Zeta2NextTwo

noncomputable section

namespace Zeta2ANJval

def Red (p : ℕ) (q : ℚ) (x : ZMod p) : Prop :=
  ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q * b = a ∧ (a : ZMod p) = x * b

theorem red_zero {p : ℕ} (pp : p.Prime) : Red p 0 0 :=
  ⟨0, 1, not_dvd_one' pp, by rw [zero_mul, Int.cast_zero], by rw [Int.cast_zero, zero_mul]⟩

theorem red_add {p : ℕ} (pp : p.Prime) {q1 q2 : ℚ} {x1 x2 : ZMod p} (h1 : Red p q1 x1)
    (h2 : Red p q2 x2) : Red p (q1 + q2) (x1 + x2) := by
  obtain ⟨a1, b1, hb1, e1, f1⟩ := h1
  obtain ⟨a2, b2, hb2, e2, f2⟩ := h2
  refine ⟨a1 * b2 + a2 * b1, b1 * b2, fun h => ((pz_prime pp).dvd_or_dvd h).elim hb1 hb2, ?_, ?_⟩
  · rw [Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_mul, ← e1, ← e2]
    ring
  · rw [Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_mul, f1, f2]
    ring

theorem red_sum {p : ℕ} (pp : p.Prime) {ι : Type*} (s : Finset ι) (f : ι → ℚ) (g : ι → ZMod p)
    (H : ∀ i ∈ s, Red p (f i) (g i)) : Red p (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [sum_empty, sum_empty]
    exact red_zero pp
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact red_add pp (H a (mem_insert_self a s)) (ih fun i hi => H i (mem_insert_of_mem hi))

theorem red_mul {p : ℕ} {q : ℚ} {x : ZMod p} (c : ℤ) (h : Red p q x) :
    Red p ((c : ℚ) * q) ((c : ZMod p) * x) := by
  obtain ⟨a, b, hb, e, f⟩ := h
  refine ⟨c * a, b, hb, ?_, ?_⟩
  · rw [Int.cast_mul, ← e, mul_assoc]
  · rw [Int.cast_mul, f, mul_assoc]

theorem red_pInt0 {p : ℕ} {q : ℚ} {x : ZMod p} (h : Red p q x) : pInt p 0 q := by
  obtain ⟨a, b, hb, e, -⟩ := h
  exact ⟨a, b, hb, by rw [e, pow_zero, one_mul]⟩

theorem red_pInt1 {p : ℕ} {q : ℚ} (h : Red p q 0) : pInt p 1 q := by
  obtain ⟨a, b, hb, e, f⟩ := h
  rw [zero_mul, ZMod.intCast_zmod_eq_zero_iff_dvd] at f
  obtain ⟨c, rfl⟩ := f
  exact ⟨c, b, hb, by rw [e, pow_one, Int.cast_mul, Int.cast_natCast]⟩

theorem pInt_div_unit {p : ℕ} (pp : p.Prime) {q : ℚ} (n : ℕ) (hn : ¬ p ∣ n) (h : pInt p 0 q) :
    pInt p 0 (q / n) := by
  obtain ⟨a, b, hb, e⟩ := h
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 fun h0 => hn (h0 ▸ dvd_zero p)
  refine ⟨a, b * n, fun h' => ((pz_prime pp).dvd_or_dvd h').elim hb
    fun h'' => hn (Int.natCast_dvd_natCast.1 h''), ?_⟩
  rw [Int.cast_mul, Int.cast_natCast, mul_comm (b : ℚ) (n : ℚ), ← mul_assoc,
    div_mul_cancel₀ q hn0, e]

theorem Jsum_C (B η : ℕ) (c : ℚ) (P : ℚ[X]) : Jsum B η (C c * P) = c * Jsum B η P := by
  rw [Jsum, Jsum, mul_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [dl_C_mul, mul_left_comm]

theorem choose_pred (p : ℕ) [hp : Fact p.Prime] :
    ∀ k, k < p → (((p - 1).choose k : ℕ) : ZMod p) = (-1) ^ k
  | 0, _ => by rw [Nat.choose_zero_right, Nat.cast_one, pow_zero]
  | k + 1, hk => by
    have ih := choose_pred p k (by omega)
    have h1 : p.choose (k + 1) = (p - 1).choose k + (p - 1).choose (k + 1) := by
      have := Nat.choose_succ_succ' (p - 1) k
      rwa [Nat.sub_add_cancel hp.out.one_le] at this
    have h2 : ((p.choose (k + 1) : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 (hp.out.dvd_choose_self (by omega) hk)
    rw [h1, Nat.cast_add, ih] at h2
    rw [pow_succ, mul_neg_one]
    exact eq_neg_of_add_eq_zero_right h2

theorem coef_eq (p : ℕ) [hp : Fact p.Prime] (n t u k : ℕ) (hn : n + 1 = t * p) (hu : u < t)
    (hk : k < p) :
    (((-1 : ℤ) ^ (n - (u * p + k)) * (n.choose (u * p + k) : ℤ) : ℤ) : ZMod p) =
      (-1) ^ (n - u * p) * ((t - 1).choose u : ZMod p) := by
  have hp0 : 0 < p := hp.out.pos
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have e1 : (t' + 1) * p = t' * p + p := Nat.succ_mul t' p
  have e2 : (u + 1) * p ≤ (t' + 1) * p := Nat.mul_le_mul_right p (by omega)
  have e3 : (u + 1) * p = u * p + p := Nat.succ_mul u p
  have hnm : n / p = t' ∧ n % p = p - 1 :=
    (Nat.div_mod_unique hp0).2 ⟨by rw [Nat.mul_comm p t']; omega, by omega⟩
  have him : (u * p + k) / p = u ∧ (u * p + k) % p = k :=
    (Nat.div_mod_unique hp0).2 ⟨by rw [Nat.mul_comm p u]; omega, hk⟩
  have hl := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := u * p + k) (p := p)
  rw [hnm.1, hnm.2, him.1, him.2] at hl
  have hz : ((n.choose (u * p + k) : ℕ) : ZMod p) =
      (((p - 1).choose k : ℕ) : ZMod p) * ((t'.choose u : ℕ) : ZMod p) := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 hl, Nat.cast_mul]
  rw [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast, hz,
    choose_pred p k hk, ← mul_assoc, ← pow_add, Nat.add_sub_cancel,
    show n - (u * p + k) + k = n - u * p by omega]

def Yf (p : ℕ) (κ : ZMod p) (Q B : (ZMod p)[X]) (r : ℕ) (s : ℤ) : ZMod p :=
  κ * (s : ZMod p) ^ r * Q.eval (s : ZMod p) * B.eval ((s / p : ℤ) : ZMod p)

theorem Yf_eq (p : ℕ) [hp : Fact p.Prime] (κ : ZMod p) (Q B : (ZMod p)[X]) (r A u k : ℕ)
    (hk : k < p) :
    Yf p κ Q B r (((u * p + k : ℕ) : ℤ) + -((A * p : ℕ) : ℤ)) =
      κ * (k : ZMod p) ^ r * Q.eval (k : ZMod p) * B.eval ((((u : ℤ) - A) : ℤ) : ZMod p) := by
  have hs : (((u * p + k : ℕ) : ℤ) + -((A * p : ℕ) : ℤ)) = (k : ℤ) + ((u : ℤ) - A) * p := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
    ring
  have hp0 : 0 < p := hp.out.pos
  have h1 : (((k : ℤ) + ((u : ℤ) - A) * p : ℤ) : ZMod p) = (k : ZMod p) := by
    rw [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_self,
      mul_zero, add_zero]
  have h2 : ((k : ℤ) + ((u : ℤ) - A) * p) / p = (u : ℤ) - A := by
    rw [Int.add_mul_ediv_right _ _ (by omega), Int.ediv_eq_zero_of_lt (by omega) (by omega),
      zero_add]
  rw [Yf, hs, h1, h2]

theorem sum_split {M : Type*} [AddCommMonoid M] (f : ℕ → M) (p : ℕ) :
    ∀ t, ∑ i ∈ range (t * p), f i = ∑ u ∈ range t, ∑ k ∈ range p, f (u * p + k)
  | 0 => by rw [Nat.zero_mul, range_zero, sum_empty, sum_empty]
  | t + 1 => by rw [Nat.succ_mul, sum_range_add, sum_split f p t, sum_range_succ]

theorem sum_range_zmod (p : ℕ) [hp : Fact p.Prime] (r : ℕ) (Q : (ZMod p)[X]) :
    ∑ k ∈ range p, (k : ZMod p) ^ r * Q.eval (k : ZMod p) = ∑ x : ZMod p, x ^ r * Q.eval x := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  refine Finset.sum_nbij (fun k : ℕ => (k : ZMod p)) (fun a _ => mem_univ _) ?_ ?_ fun a _ => rfl
  · intro a ha b hb hab
    have h := (ZMod.natCast_eq_natCast_iff' a b p).1 hab
    rwa [Nat.mod_eq_of_lt (mem_range.1 ha), Nat.mod_eq_of_lt (mem_range.1 hb)] at h
  · intro x _
    exact ⟨x.val, mem_range.2 (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩

theorem zsum_zero (p : ℕ) [Fact p.Prime] (κ : ZMod p) (Q B : (ZMod p)[X]) (r A t n : ℕ)
    (hQ : ∑ k : ZMod p, k ^ r * Q.eval k = 0) (hn : n + 1 = t * p) :
    ∑ i ∈ range (n + 1), (((-1 : ℤ) ^ (n - i) * (n.choose i : ℤ) : ℤ) : ZMod p) *
      Yf p κ Q B r ((i : ℤ) + -((A * p : ℕ) : ℤ)) = 0 := by
  rw [hn, sum_split _ p t]
  refine sum_eq_zero fun u hu => ?_
  have e : ∀ k ∈ range p, (((-1 : ℤ) ^ (n - (u * p + k)) * (n.choose (u * p + k) : ℤ) : ℤ) :
      ZMod p) * Yf p κ Q B r (((u * p + k : ℕ) : ℤ) + -((A * p : ℕ) : ℤ)) =
      ((-1) ^ (n - u * p) * ((t - 1).choose u : ZMod p) * κ *
        B.eval ((((u : ℤ) - A) : ℤ) : ZMod p)) * ((k : ZMod p) ^ r * Q.eval (k : ZMod p)) :=
    fun k hk => by
      rw [coef_eq p n t u k hn (mem_range.1 hu) (mem_range.1 hk), Yf_eq p κ Q B r A u k
        (mem_range.1 hk)]
      ring
  rw [sum_congr rfl e, ← mul_sum, sum_range_zmod p r Q, hQ, mul_zero]

theorem red_dl (p : ℕ) (pp : p.Prime) (P : ℚ[X]) (Y : ℤ → ZMod p) (c0 : ℤ)
    (hP : ∀ s : ℤ, Red p (P.eval (s : ℚ)) (Y s)) (n : ℕ) :
    Red p (dl n P (c0 : ℚ)) (∑ i ∈ range (n + 1),
      (((-1 : ℤ) ^ (n - i) * (n.choose i : ℤ) : ℤ) : ZMod p) * Y ((i : ℤ) + c0)) := by
  rw [dl]
  refine red_sum pp _ _ _ fun i _ => ?_
  have h := red_mul ((-1 : ℤ) ^ (n - i) * (n.choose i : ℤ)) (hP ((i : ℤ) + c0))
  rw [Int.cast_add, Int.cast_natCast, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast] at h
  exact h

theorem J_val_core (N r p : ℕ) [Fact p.Prime] (hN : 1 ≤ N) (hr : r < 3)
    (_hp8 : p < 8 * N) (hp2 : 50 * N < p ^ 2) (h A : ℕ) (_hA : A = 1 ∨ A = 2)
    (Q : (ZMod p)[X]) (hQ : ∑ k : ZMod p, k ^ r * Q.eval k = 0)
    (hS : ∃ (κ : ZMod p) (B : (ZMod p)[X]), ∀ s : ℤ,
      ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧
        (p : ℚ) ^ ((1 : ℤ) - (h : ℤ)) * (Spoly N r).eval (s : ℚ) * b = a ∧
        (a : ZMod p) =
          κ * (s : ZMod p) ^ r * Q.eval (s : ZMod p) * B.eval ((s / p : ℤ) : ZMod p) * b) :
    pInt p (h + 1) ((p : ℚ) ^ 2 * Jfun (A * p) (Spoly N r)) := by
  have pp : p.Prime := Fact.out
  obtain ⟨κ, B, hS⟩ := hS
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 pp.ne_zero
  have hdeg : (Spoly N r).natDegree < 13 * N + r := by
    have := P_deg N r hN
    rwa [natDegree_C_mul (Nat.cast_ne_zero.2 (lcmUpTo_pos (12 * N)).ne')] at this
  set T := C ((p : ℚ) ^ ((1 : ℤ) - (h : ℤ))) * Spoly N r with hT
  have key : (p : ℚ) ^ 2 * Jsum (13 * N + r) (A * p) (Spoly N r) =
      (p : ℚ) ^ (h + 1) * Jsum (13 * N + r) (A * p) T := by
    rw [hT, Jsum_C, ← mul_assoc, ← zpow_natCast (p : ℚ) (h + 1), ← zpow_add₀ hp0,
      show (((h + 1 : ℕ) : ℤ) + ((1 : ℤ) - (h : ℤ))) = ((2 : ℕ) : ℤ) by omega, zpow_natCast]
  have hTv : ∀ s : ℤ, Red p (T.eval (s : ℚ)) (Yf p κ Q B r s) := fun s => by
    obtain ⟨a, b, hb, e, f⟩ := hS s
    exact ⟨a, b, hb, by rw [hT, eval_mul, eval_C, e], f⟩
  have hpow : pInt p (h + 1) ((p : ℚ) ^ (h + 1)) := by
    have := pInt_of_dvd pp ((p : ℤ) ^ (h + 1)) dvd_rfl
    rwa [Int.cast_pow, Int.cast_natCast] at this
  rw [Jfun_eq _ _ _ hdeg, key]
  suffices hJ : pInt p 0 (Jsum (13 * N + r) (A * p) T) by
    have := pInt_mul pp hpow hJ
    rwa [Nat.add_zero] at this
  rw [Jsum]
  refine pInt_sum pp _ _ fun n hn => ?_
  have hn2 : n + 1 < p ^ 2 := by
    have := mem_range.1 hn
    omega
  have hR := red_dl p pp T (Yf p κ Q B r) (-((A * p : ℕ) : ℤ)) hTv n
  rw [Int.cast_neg, Int.cast_natCast] at hR
  have e : (-1 : ℚ) ^ n / ((n : ℚ) + 1) * dl n T (-((A * p : ℕ) : ℚ)) =
      (((-1 : ℤ) ^ n : ℤ) : ℚ) * (dl n T (-((A * p : ℕ) : ℚ)) / ((n + 1 : ℕ) : ℚ)) := by
    rw [Int.cast_pow, Int.cast_neg, Int.cast_one, Nat.cast_succ, div_mul_eq_mul_div, mul_div_assoc]
  rw [e]
  have hD : pInt p 0 (dl n T (-((A * p : ℕ) : ℚ)) / ((n + 1 : ℕ) : ℚ)) := by
    by_cases hpn : p ∣ n + 1
    · obtain ⟨t, ht⟩ := hpn
      rw [zsum_zero p κ Q B r A t n hQ (by rw [ht, Nat.mul_comm])] at hR
      exact pInt_div_nat pp _ (n + 1) (by omega) hn2 (red_pInt1 hR)
    · exact pInt_div_unit pp (n + 1) hpn (red_pInt0 hR)
  have := pInt_mul pp (pInt_int pp ((-1 : ℤ) ^ n)) hD
  rwa [Nat.zero_add] at this

end Zeta2ANJval
