import Zeta2FourTrajectoryMatrices.FiniteReadout.blueprint_first_three

open Polynomial Finset Zeta2Blueprint Zeta2FirstThree

noncomputable section

namespace Zeta2NextTwo

def chi2 (N p : ℕ) (k k' : ℤ) : ℤ :=
  (11 * N : ℤ) / p - k / p - (11 * N + k') / p + (10 * N + k) / p + (9 * N + k) / p +
    (11 * N + k) / p - 3 * ((8 * N : ℤ) / p) - (2 * N + k) / p - (N + k) / p - (3 * N + k) / p

def chi (N p : ℕ) (j : ℤ) : ℤ := chi2 N p j (-j)

theorem fl_add (c : ℤ) (N p : ℕ) (hp : 0 < p) (s : ℝ) :
    ⌊(c : ℝ) * ((N : ℝ) / p) + s⌋ = (c * N + ⌊(p : ℝ) * s⌋) / p := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne'
  rw [show (c : ℝ) * ((N : ℝ) / p) + s = (((c * N : ℤ) : ℝ) + (p : ℝ) * s) / p by
      rw [add_div, mul_div_cancel_left₀ _ hp0, Int.cast_mul, Int.cast_natCast, mul_div_assoc],
    Int.floor_div_natCast, Int.floor_intCast_add]

theorem rho_formula (N p : ℕ) (hp : 0 < p) (y : ℝ) :
    rho ((N : ℝ) / p) y = chi2 N p ⌊(p : ℝ) * y⌋ ⌊(p : ℝ) * -y⌋ := by
  have h11 := fl_add 11 N p hp 0
  have hy := fl_add 0 N p hp y
  have h11m := fl_add 11 N p hp (-y)
  have h10 := fl_add 10 N p hp y
  have h9 := fl_add 9 N p hp y
  have h11p := fl_add 11 N p hp y
  have h8 := fl_add 8 N p hp 0
  have h2 := fl_add 2 N p hp y
  have h1 := fl_add 1 N p hp y
  have h3 := fl_add 3 N p hp y
  simp only [Int.cast_ofNat, Int.cast_zero, Int.cast_one, zero_mul, zero_add, one_mul, add_zero,
    mul_zero, Int.floor_zero] at h11 hy h11m h10 h9 h11p h8 h2 h1 h3
  rw [← sub_eq_add_neg] at h11m
  rw [rho, h11, hy, h11m, h10, h9, h11p, h8, h2, h1, h3, chi2]

theorem rho_ge (N p : ℕ) (hp : 0 < p) (y : ℝ) : chi N p ⌊(p : ℝ) * y⌋ ≤ rho ((N : ℝ) / p) y := by
  have h1 : ⌊(p : ℝ) * -y⌋ ≤ -⌊(p : ℝ) * y⌋ := by
    rw [mul_neg, Int.floor_neg, neg_le_neg_iff]
    exact Int.floor_le_ceil _
  have h2 := Int.ediv_le_ediv (show (0 : ℤ) < p by exact_mod_cast hp)
    (add_le_add_right h1 (11 * (N : ℤ)))
  rw [rho_formula N p hp y, chi, chi2, chi2]
  omega

theorem rho_eq (N p : ℕ) (hp : 0 < p) (j : ℤ) : rho ((N : ℝ) / p) ((j : ℝ) / p) = chi N p j := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne'
  rw [rho_formula N p hp, mul_neg, mul_div_cancel₀ _ hp0, ← Int.cast_neg, Int.floor_intCast,
    Int.floor_intCast]
  rfl

theorem ediv_add_le (a b p : ℤ) (hp : 0 < p) : a / p + b / p ≤ (a + b) / p :=
  Int.le_ediv_of_mul_le hp (by
    rw [add_mul]; exact add_le_add (Int.ediv_mul_le a hp.ne') (Int.ediv_mul_le b hp.ne'))

theorem chi_nonneg (N p : ℕ) (hp : 0 < p) (j : ℤ) : 0 ≤ chi N p j := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have s1 := ediv_add_le j (11 * N + -j) p hp'
  have s2 := ediv_add_le (2 * N + j) (8 * N) p hp'
  have s3 := ediv_add_le (N + j) (8 * N) p hp'
  have s4 := ediv_add_le (3 * N + j) (8 * N) p hp'
  rw [show j + (11 * (N : ℤ) + -j) = 11 * N by omega] at s1
  rw [show 2 * (N : ℤ) + j + 8 * N = 10 * N + j by omega] at s2
  rw [show (N : ℤ) + j + 8 * N = 9 * N + j by omega] at s3
  rw [show 3 * (N : ℤ) + j + 8 * N = 11 * N + j by omega] at s4
  unfold chi chi2
  omega

theorem chi_mod (N p : ℕ) (hp : 0 < p) (j : ℤ) : chi N p j = chi N p (j % p) := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have key : ∀ A : ℤ, (A + j) / p = (A + j % p) / p + j / p := fun A => by
    conv_lhs => rw [← Int.emod_add_mul_ediv j p]
    rw [← add_assoc, Int.add_mul_ediv_left _ _ hp0]
  have key' : ∀ A : ℤ, (A + -j) / p = (A + -(j % p)) / p - j / p := fun A => by
    conv_lhs => rw [← Int.emod_add_mul_ediv j p]
    rw [neg_add, ← mul_neg, ← add_assoc, Int.add_mul_ediv_left _ _ hp0, ← sub_eq_add_neg]
  have k0 : j / p = (j % p) / p + j / p := by
    have := key 0
    rwa [zero_add, zero_add] at this
  have e1 := key (11 * N)
  have e2 := key (10 * N)
  have e3 := key (9 * N)
  have e4 := key (2 * N)
  have e5 := key N
  have e6 := key (3 * N)
  have e7 := key' (11 * N)
  unfold chi chi2
  omega

instance : Nonempty (Set.Ico (0 : ℝ) 1) := ⟨⟨0, le_rfl, one_pos⟩⟩

theorem rho_bdd (N p : ℕ) (hp : 0 < p) :
    BddBelow (Set.range fun y : Set.Ico (0 : ℝ) 1 => rho ((N : ℝ) / p) y) :=
  ⟨0, by rintro _ ⟨y, rfl⟩; exact (chi_nonneg N p hp _).trans (rho_ge N p hp y)⟩

theorem phi_le_chi (N p : ℕ) (hp : 0 < p) (j : ℤ) : phi ((N : ℝ) / p) ≤ chi N p j := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  rw [chi_mod N p hp j, ← rho_eq N p hp (j % p)]
  exact ciInf_le (rho_bdd N p hp) (⟨((j % p : ℤ) : ℝ) / p,
    div_nonneg (by exact_mod_cast Int.emod_nonneg j hp'.ne') hp0.le,
    (div_lt_one hp0).2 (by exact_mod_cast Int.emod_lt_of_pos j hp')⟩ : Set.Ico (0 : ℝ) 1)

theorem phi_ge (N p : ℕ) (hp : 0 < p) (h0 : ℤ)
    (H : ∀ k : ℤ, 0 ≤ k → k < p → h0 ≤ chi N p k) : h0 ≤ phi ((N : ℝ) / p) := by
  unfold phi
  refine le_ciInf fun y => (H _ (Int.floor_nonneg.2 (mul_nonneg (Nat.cast_nonneg p) y.2.1))
    ?_).trans (rho_ge N p hp y)
  rw [Int.floor_lt, Int.cast_natCast]
  exact mul_lt_of_lt_one_right (by exact_mod_cast hp) y.2.2

theorem phi_nonneg (N p : ℕ) (hp : 0 < p) : 0 ≤ phi ((N : ℝ) / p) :=
  phi_ge N p hp 0 fun k _ _ => chi_nonneg N p hp k

theorem qexact (A p q : ℤ) (hp : 0 < p) (h1 : q * p ≤ A) (h2 : A < q * p + p) : A / p = q := by
  have a := Int.le_ediv_of_mul_le hp h1
  have b := Int.ediv_lt_of_lt_mul hp (show A < (q + 1) * p by rw [add_mul, one_mul]; exact h2)
  omega

theorem qcase (A p q : ℤ) (hp : 0 < p) (h1 : q * p ≤ A) (h2 : A < q * p + 2 * p) :
    (A / p = q ∧ q * p ≤ A ∧ A < q * p + p) ∨
      (A / p = q + 1 ∧ q * p + p ≤ A ∧ A < q * p + 2 * p) := by
  rcases lt_or_ge A (q * p + p) with h | h
  · exact Or.inl ⟨qexact A p q hp h1 h, h1, h⟩
  · exact Or.inr ⟨qexact A p (q + 1) hp (by rw [add_mul, one_mul]; exact h)
      (by rw [add_mul, one_mul]; omega), h, h2⟩

theorem chi_S3 (N p : ℕ) (k : ℤ) (h1 : 13 * N < 3 * p) (h2 : 2 * p < 9 * N) (hk0 : 0 ≤ k)
    (hk : k < p) : 2 ≤ chi N p k := by
  have hp : (0 : ℤ) < p := by omega
  have e0 := qexact k p 0 hp (by omega) (by omega)
  have e1 := qexact (11 * N) p 2 hp (by omega) (by omega)
  have e2 := qexact (8 * N) p 1 hp (by omega) (by omega)
  have c1 := qcase (11 * N + -k) p 1 hp (by omega) (by omega)
  have c2 := qcase (10 * N + k) p 2 hp (by omega) (by omega)
  have c3 := qcase (9 * N + k) p 2 hp (by omega) (by omega)
  have c4 := qcase (11 * N + k) p 2 hp (by omega) (by omega)
  have c5 := qcase (2 * N + k) p 0 hp (by omega) (by omega)
  have c6 := qcase (N + k) p 0 hp (by omega) (by omega)
  have c7 := qcase (3 * N + k) p 0 hp (by omega) (by omega)
  unfold chi chi2
  omega

theorem chi_S4 (N p : ℕ) (k : ℤ) (h1 : 13 * N < 4 * p) (h2 : 3 * p < 10 * N) (hk0 : 0 ≤ k)
    (hk : k < p) : 1 ≤ chi N p k := by
  have hp : (0 : ℤ) < p := by omega
  have e0 := qexact k p 0 hp (by omega) (by omega)
  have e1 := qexact (11 * N) p 3 hp (by omega) (by omega)
  have e2 := qexact (8 * N) p 2 hp (by omega) (by omega)
  have c1 := qcase (11 * N + -k) p 2 hp (by omega) (by omega)
  have c2 := qcase (10 * N + k) p 3 hp (by omega) (by omega)
  have c3 := qcase (9 * N + k) p 2 hp (by omega) (by omega)
  have c4 := qcase (11 * N + k) p 3 hp (by omega) (by omega)
  have c5 := qcase (2 * N + k) p 0 hp (by omega) (by omega)
  have c6 := qcase (N + k) p 0 hp (by omega) (by omega)
  have c7 := qcase (3 * N + k) p 0 hp (by omega) (by omega)
  unfold chi chi2
  omega

theorem chi_S6a (N p : ℕ) (k : ℤ) (h1 : 13 * N < 6 * p) (h2 : 4 * p < 9 * N) (h3 : 11 * N < 5 * p)
    (hk0 : 0 ≤ k) (hk : k < p) : 1 ≤ chi N p k := by
  have hp : (0 : ℤ) < p := by omega
  have e0 := qexact k p 0 hp (by omega) (by omega)
  have e1 := qexact (11 * N) p 4 hp (by omega) (by omega)
  have e2 := qexact (8 * N) p 3 hp (by omega) (by omega)
  have c1 := qcase (11 * N + -k) p 3 hp (by omega) (by omega)
  have c2 := qcase (10 * N + k) p 4 hp (by omega) (by omega)
  have c3 := qcase (9 * N + k) p 4 hp (by omega) (by omega)
  have c4 := qcase (11 * N + k) p 4 hp (by omega) (by omega)
  have c5 := qcase (2 * N + k) p 0 hp (by omega) (by omega)
  have c6 := qcase (N + k) p 0 hp (by omega) (by omega)
  have c7 := qcase (3 * N + k) p 1 hp (by omega) (by omega)
  unfold chi chi2
  omega

theorem chi_S6b (N p : ℕ) (k : ℤ) (h1 : 13 * N < 6 * p) (h2 : 4 * p < 9 * N) (h3 : 5 * p < 11 * N)
    (hk0 : 0 ≤ k) (hk : k < p) : 2 ≤ chi N p k := by
  have hp : (0 : ℤ) < p := by omega
  have e0 := qexact k p 0 hp (by omega) (by omega)
  have e1 := qexact (11 * N) p 5 hp (by omega) (by omega)
  have e2 := qexact (8 * N) p 3 hp (by omega) (by omega)
  have c1 := qcase (11 * N + -k) p 4 hp (by omega) (by omega)
  have c2 := qcase (10 * N + k) p 4 hp (by omega) (by omega)
  have c3 := qcase (9 * N + k) p 4 hp (by omega) (by omega)
  have c4 := qcase (11 * N + k) p 5 hp (by omega) (by omega)
  have c5 := qcase (2 * N + k) p 0 hp (by omega) (by omega)
  have c6 := qcase (N + k) p 0 hp (by omega) (by omega)
  have c7 := qcase (3 * N + k) p 1 hp (by omega) (by omega)
  unfold chi chi2
  omega

theorem chi_S12 (N p : ℕ) (k : ℤ) (h1 : 13 * N < 12 * p) (h2 : 8 * p < 9 * N)
    (h3 : 10 * p < 11 * N) (hk0 : 0 ≤ k) (hk : k < p) : 1 ≤ chi N p k := by
  have hp : (0 : ℤ) < p := by omega
  have e0 := qexact k p 0 hp (by omega) (by omega)
  have e1 := qexact (11 * N) p 10 hp (by omega) (by omega)
  have e2 := qexact (8 * N) p 7 hp (by omega) (by omega)
  have c1 := qcase (11 * N + -k) p 9 hp (by omega) (by omega)
  have c2 := qcase (10 * N + k) p 9 hp (by omega) (by omega)
  have c3 := qcase (9 * N + k) p 8 hp (by omega) (by omega)
  have c4 := qcase (11 * N + k) p 10 hp (by omega) (by omega)
  have c5 := qcase (2 * N + k) p 1 hp (by omega) (by omega)
  have c6 := qcase (N + k) p 0 hp (by omega) (by omega)
  have c7 := qcase (3 * N + k) p 2 hp (by omega) (by omega)
  unfold chi chi2
  omega

theorem carry_nat (A B p : ℕ) (hp : 0 < p) :
    ((A + B) / p : ℕ) = A / p + B / p + (if (A + B) % p < B % p then 1 else 0) := by
  rw [Nat.add_div hp]
  have h1 := Nat.mod_lt A hp
  have h2 := Nat.mod_lt B hp
  rcases Nat.lt_or_ge (A % p + B % p) p with h | h
  · have h4 : (A + B) % p = A % p + B % p := by rw [Nat.add_mod, Nat.mod_eq_of_lt h]
    simp only [show ¬ (p ≤ A % p + B % p) by omega, show ¬ ((A + B) % p < B % p) by omega,
      ↓reduceIte]
  · have h4 : (A + B) % p = A % p + B % p - p := by
      rw [Nat.add_mod, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    simp only [h, show (A + B) % p < B % p by omega, ↓reduceIte]

theorem chi_id (N p k : ℕ) (hp : 0 < p) (hk : k < p) :
    chi N p k = (if 11 * N % p < k then 1 else 0) +
      ((if (k + 9 * N) % p < 8 * N % p then 1 else 0 : ℕ) : ℤ) +
      ((if (k + 10 * N) % p < 8 * N % p then 1 else 0 : ℕ) : ℤ) +
      ((if (k + 11 * N) % p < 8 * N % p then 1 else 0 : ℕ) : ℤ) := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have c9 := carry_nat (N + k) (8 * N) p hp
  have c10 := carry_nat (2 * N + k) (8 * N) p hp
  have c11 := carry_nat (3 * N + k) (8 * N) p hp
  rw [show N + k + 8 * N = k + 9 * N by omega] at c9
  rw [show 2 * N + k + 8 * N = k + 10 * N by omega] at c10
  rw [show 3 * N + k + 8 * N = k + 11 * N by omega] at c11
  have z9 := congrArg (fun n : ℕ => (n : ℤ)) c9
  have z10 := congrArg (fun n : ℕ => (n : ℤ)) c10
  have z11 := congrArg (fun n : ℕ => (n : ℤ)) c11
  simp only [Nat.cast_add, Int.natCast_div, Nat.cast_mul, Nat.cast_ofNat] at z9 z10 z11
  have t0 : (k : ℤ) / p = 0 := Int.ediv_eq_zero_of_lt (by omega) (by exact_mod_cast hk)
  have hM := Nat.div_add_mod (11 * N) p
  have hMz : (p : ℤ) * ((11 * N / p : ℕ) : ℤ) + ((11 * N % p : ℕ) : ℤ) = 11 * N := by
    exact_mod_cast hM
  have hd := Nat.mod_lt (11 * N) hp
  have t11 : (11 * N : ℤ) / p = ((11 * N / p : ℕ) : ℤ) := by
    rw [Int.natCast_div]; push_cast; rfl
  have te : (11 * N + -(k : ℤ)) / p = ((11 * N / p : ℕ) : ℤ) - (if 11 * N % p < k then 1 else 0) := by
    by_cases hdk : 11 * N % p < k
    · simp only [hdk, ↓reduceIte]
      refine ((Int.ediv_emod_unique (r := ((11 * N % p : ℕ) : ℤ) - k + p) hp').2 ⟨?_, ?_, ?_⟩).1
      · rw [mul_sub, mul_one]
        omega
      · omega
      · omega
    · simp only [hdk, ↓reduceIte, sub_zero]
      refine ((Int.ediv_emod_unique (r := ((11 * N % p : ℕ) : ℤ) - k) hp').2 ⟨?_, ?_, ?_⟩).1
      · omega
      · omega
      · omega
  rw [add_comm (k : ℤ)] at z9 z10 z11
  unfold chi chi2
  rw [t0, t11, te]
  omega

theorem fact_ne_zero {p : ℕ} [Fact p.Prime] {b : ℕ} (hb : b < p) : (b.factorial : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact fun h => absurd ((Nat.Prime.dvd_factorial Fact.out).1 h) (by omega)

theorem binom_desc {p : ℕ} [Fact p.Prime] (a : ZMod p) (b : ℕ) :
    (descPochhammer (ZMod p) b).comp (X + C a) =
      ((Multiset.range b).map fun i : ℕ => X - C ((i : ZMod p) - a)).prod := by
  induction b with
  | zero => rw [descPochhammer_zero, one_comp, Multiset.range_zero, Multiset.map_zero,
      Multiset.prod_zero]
  | succ n ih =>
    rw [descPochhammer_succ_right, mul_comp, ih, Multiset.range_succ, Multiset.map_cons,
      Multiset.prod_cons, sub_comp, X_comp, natCast_comp, mul_comm, C_sub, ← map_natCast C n]
    ring

theorem binom_prod {p : ℕ} [Fact p.Prime] (a : ZMod p) (b : ℕ) :
    binomPoly (ZMod p) a b = C ((b.factorial : ZMod p)⁻¹) *
      (((Multiset.range b).map fun i : ℕ => (i : ZMod p) - a).map fun c => X - C c).prod := by
  rw [binomPoly, binom_desc, Multiset.map_map]
  rfl

theorem binom_ne_zero {p : ℕ} [Fact p.Prime] (a : ZMod p) {b : ℕ} (hb : b < p) :
    binomPoly (ZMod p) a b ≠ 0 := by
  rw [binom_prod]
  exact mul_ne_zero (by rw [Ne, C_eq_zero]; exact inv_ne_zero (fact_ne_zero hb))
    (monic_multiset_prod_of_monic _ _ fun c _ => monic_X_sub_C c).ne_zero

theorem binom_roots {p : ℕ} [Fact p.Prime] (a : ZMod p) {b : ℕ} (hb : b < p) :
    (binomPoly (ZMod p) a b).roots = (Multiset.range b).map fun i : ℕ => (i : ZMod p) - a := by
  rw [binom_prod, roots_C_mul _ (inv_ne_zero (fact_ne_zero hb)), roots_multiset_prod_X_sub_C]

theorem binom_natDegree {p : ℕ} [Fact p.Prime] (a : ZMod p) {b : ℕ} (hb : b < p) :
    (binomPoly (ZMod p) a b).natDegree = b := by
  rw [binom_prod, natDegree_C_mul (inv_ne_zero (fact_ne_zero hb)),
    natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map, Multiset.card_range]

theorem count_S {p : ℕ} [Fact p.Prime] {b : ℕ} (hb : b ≤ p) (a c : ZMod p) :
    Multiset.count a ((Multiset.range b).map fun i : ℕ => (i : ZMod p) - c) =
      if (a + c).val < b then 1 else 0 := by
  have hnd : ((Multiset.range b).map fun i : ℕ => (i : ZMod p) - c).Nodup := by
    refine Multiset.Nodup.map_on (fun x hx y hy hxy => ?_) (Multiset.nodup_range b)
    have hx' := Multiset.mem_range.1 hx
    have hy' := Multiset.mem_range.1 hy
    have := congrArg ZMod.val (sub_left_injective hxy)
    rwa [ZMod.val_cast_of_lt (by omega), ZMod.val_cast_of_lt (by omega)] at this
  by_cases h : (a + c).val < b
  · rw [Multiset.count_eq_one_of_mem hnd (Multiset.mem_map.2 ⟨(a + c).val, Multiset.mem_range.2 h,
      by rw [ZMod.natCast_zmod_val, add_sub_cancel_right]⟩)]
    simp only [h, ↓reduceIte]
  · rw [Multiset.count_eq_zero.2 fun hm => h ?_]
    · simp only [h, ↓reduceIte]
    · obtain ⟨i, hi, hia⟩ := Multiset.mem_map.1 hm
      rw [← hia, sub_add_cancel, ZMod.val_cast_of_lt (by have := Multiset.mem_range.1 hi; omega)]
      exact Multiset.mem_range.1 hi

theorem count_G {p : ℕ} [Fact p.Prime] {d : ℕ} (hd : d < p) (a : ZMod p) :
    Multiset.count a ((Multiset.range (d + 1)).map fun j : ℕ => (j : ZMod p)) =
      if a.val ≤ d then 1 else 0 := by
  have h := count_S (b := d + 1) (by omega) a 0
  simp only [sub_zero, add_zero, Nat.lt_add_one_iff] at h
  exact h

theorem Xp_prod {p : ℕ} [Fact p.Prime] :
    (X ^ p - X : (ZMod p)[X]) = ((univ.val).map fun a : ZMod p => X - C a).prod := by
  have pp : p.Prime := Fact.out
  have hm : (X ^ p - X : (ZMod p)[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast pp.one_lt)
  have hr := FiniteField.roots_X_pow_card_sub_X (ZMod p)
  rw [ZMod.card] at hr
  have hc : (X ^ p - X : (ZMod p)[X]).roots.card = (X ^ p - X : (ZMod p)[X]).natDegree := by
    rw [hr, FiniteField.X_pow_card_sub_X_natDegree_eq _ pp.one_lt, Finset.card_val,
      Finset.card_univ, ZMod.card]
  rw [← hr]
  exact (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hc).symm

theorem val_add_cast {p : ℕ} [Fact p.Prime] (a : ZMod p) (n : ℕ) :
    (a + (n : ZMod p)).val = (a.val + n) % p := by
  rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod]

theorem polyQ_factor (N r p : ℕ) [Fact p.Prime] (hN : 1 ≤ N) (hr : r < 3)
    (hp : 50 * N < p ^ 2) (hshell : InShell N r p) :
    let b := 8 * N % p
    let d := 11 * N % p
    let h := (phi ((N : ℝ) / p)).toNat
    let f : (ZMod p)[X] := binomPoly (ZMod p) ((9 * N : ℕ) : ZMod p) b *
      binomPoly (ZMod p) ((10 * N : ℕ) : ZMod p) b * binomPoly (ZMod p) ((11 * N : ℕ) : ZMod p) b
    let g : (ZMod p)[X] := ∏ j ∈ range (d + 1), (X - C (j : ZMod p))
    ∃ 𝒬 : (ZMod p)[X], f * (X ^ p - X) ^ (1 - h) = (X ^ p - X) ^ (h - 1) * g * 𝒬 ∧
      (X ^ r * 𝒬).natDegree < p - 1 := by
  intro b d h f g
  have pp : p.Prime := Fact.out
  have hp0 : 0 < p := pp.pos
  have hp1 : 1 < p := pp.one_lt
  have hpN : p < 8 * N := by omega
  have hb : b < p := Nat.mod_lt _ hp0
  have hd : d < p := Nat.mod_lt _ hp0
  have hbdef : b = 8 * N % p := rfl
  have hddef : d = 11 * N % p := rfl
  have hphi0 := phi_nonneg N p hp0
  have hhdef : (h : ℤ) = phi ((N : ℝ) / p) := Int.toNat_of_nonneg hphi0
  have hXp0 : (X ^ p - X : (ZMod p)[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero _ hp1
  have hb9 := binom_ne_zero ((9 * N : ℕ) : ZMod p) hb
  have hb10 := binom_ne_zero ((10 * N : ℕ) : ZMod p) hb
  have hb11 := binom_ne_zero ((11 * N : ℕ) : ZMod p) hb
  have hf0 : f ≠ 0 := mul_ne_zero (mul_ne_zero hb9 hb10) hb11
  have hR0 : f * (X ^ p - X) ^ (1 - h) ≠ 0 := mul_ne_zero hf0 (pow_ne_zero _ hXp0)
  have hgp : g = (((Multiset.range (d + 1)).map fun j : ℕ => (j : ZMod p)).map
      fun c => X - C c).prod := by
    rw [Multiset.map_map]
    exact Finset.prod_eq_multiset_prod _ _
  have hg0 : g ≠ 0 := by
    rw [hgp]; exact (monic_multiset_prod_of_monic _ _ fun c _ => monic_X_sub_C c).ne_zero
  have hL : (X ^ p - X) ^ (h - 1) * g = ((((h - 1) • univ.val) +
      (Multiset.range (d + 1)).map fun j : ℕ => (j : ZMod p)).map fun c => X - C c).prod := by
    rw [Multiset.map_add, Multiset.prod_add, Multiset.map_nsmul, Multiset.prod_nsmul, ← Xp_prod,
      hgp]
  have hroots : (f * (X ^ p - X) ^ (1 - h)).roots =
      (Multiset.range b).map (fun i : ℕ => (i : ZMod p) - ((9 * N : ℕ) : ZMod p)) +
      (Multiset.range b).map (fun i : ℕ => (i : ZMod p) - ((10 * N : ℕ) : ZMod p)) +
      (Multiset.range b).map (fun i : ℕ => (i : ZMod p) - ((11 * N : ℕ) : ZMod p)) +
      (1 - h) • univ.val := by
    have hr := FiniteField.roots_X_pow_card_sub_X (ZMod p)
    rw [ZMod.card] at hr
    rw [roots_mul hR0, roots_pow, roots_mul hf0, roots_mul (mul_ne_zero hb9 hb10),
      binom_roots _ hb, binom_roots _ hb, binom_roots _ hb, hr]
  have hdvd : (X ^ p - X) ^ (h - 1) * g ∣ f * (X ^ p - X) ^ (1 - h) := by
    rw [hL, Multiset.prod_X_sub_C_dvd_iff_le_roots hR0, hroots, Multiset.le_iff_count]
    intro a
    rw [Multiset.count_add, Multiset.count_nsmul, Multiset.count_univ, count_G hd,
      Multiset.count_add, Multiset.count_add, Multiset.count_add, Multiset.count_nsmul,
      Multiset.count_univ, count_S hb.le, count_S hb.le, count_S hb.le, val_add_cast,
      val_add_cast, val_add_cast]
    have hk := phi_le_chi N p hp0 (a.val : ℤ)
    rw [chi_id N p a.val hp0 (ZMod.val_lt a)] at hk
    rw [← hhdef] at hk
    rw [← hbdef, ← hddef] at hk
    split_ifs at hk ⊢ <;> push_cast at hk <;> omega
  obtain ⟨Q, hQ⟩ := hdvd
  refine ⟨Q, hQ, ?_⟩
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hQ
    exact hR0 hQ
  have hdegR : (f * (X ^ p - X) ^ (1 - h)).natDegree = 3 * b + p * (1 - h) := by
    rw [natDegree_mul hf0 (pow_ne_zero _ hXp0), natDegree_pow,
      FiniteField.X_pow_card_sub_X_natDegree_eq _ hp1, natDegree_mul (mul_ne_zero hb9 hb10) hb11,
      natDegree_mul hb9 hb10, binom_natDegree _ hb, binom_natDegree _ hb, binom_natDegree _ hb]
    ring
  have hdegL : ((X ^ p - X) ^ (h - 1) * g).natDegree = p * (h - 1) + (d + 1) := by
    rw [natDegree_mul (pow_ne_zero _ hXp0) hg0, natDegree_pow,
      FiniteField.X_pow_card_sub_X_natDegree_eq _ hp1, hgp, natDegree_multiset_prod_X_sub_C_eq_card,
      Multiset.card_map, Multiset.card_range, mul_comm]
  have hsum := congrArg natDegree hQ
  rw [natDegree_mul (mul_ne_zero (pow_ne_zero _ hXp0) hg0) hQ0, hdegR, hdegL] at hsum
  rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hQ0, natDegree_X_pow]
  have e8 := Nat.div_add_mod (8 * N) p
  have e11 := Nat.div_add_mod (11 * N) p
  rw [← hbdef] at e8
  rw [← hddef] at e11
  have F1 : h = 0 → p * (1 - h) = p ∧ p * (h - 1) = 0 := fun h0 => by rw [h0]; simp
  have F2 : 1 ≤ h → p * (1 - h) = 0 := fun h1 => by rw [Nat.sub_eq_zero_of_le h1, mul_zero]
  have F3 : 2 ≤ h → p ≤ p * (h - 1) := fun h2 => Nat.le_mul_of_pos_right p (by omega)
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp0
  rcases hshell with ⟨s1, s2⟩ | ⟨s1, s2⟩ | ⟨s1, s2⟩ | ⟨s1, s2⟩ | ⟨s1, s2⟩ | ⟨s1, s2⟩
  · have ha : 8 * N / p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have hM : 11 * N / p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [ha] at e8
    rw [hM] at e11
    omega
  · have ha : 8 * N / p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have hM : 11 * N / p = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have hh : (2 : ℤ) ≤ phi ((N : ℝ) / p) :=
      phi_ge N p hp0 2 fun k hk0 hk => chi_S3 N p k (by omega) (by omega) hk0 hk
    rw [ha] at e8
    rw [hM] at e11
    omega
  · have ha : 8 * N / p = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have hM : 11 * N / p = 3 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have hh : (1 : ℤ) ≤ phi ((N : ℝ) / p) :=
      phi_ge N p hp0 1 fun k hk0 hk => chi_S4 N p k (by omega) (by omega) hk0 hk
    rw [ha] at e8
    rw [hM] at e11
    omega
  · have ha : 8 * N / p = 3 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have hM : 11 * N / p = 4 := Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [ha] at e8
    rw [hM] at e11
    omega
  · have ha : 8 * N / p = 3 := Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [ha] at e8
    rcases Nat.lt_trichotomy (11 * N) (5 * p) with h5 | h5 | h5
    · have hM : 11 * N / p = 4 := Nat.div_eq_of_lt_le (by omega) (by omega)
      have hh : (1 : ℤ) ≤ phi ((N : ℝ) / p) :=
        phi_ge N p hp0 1 fun k hk0 hk => chi_S6a N p k (by omega) (by omega) (by omega) hk0 hk
      rw [hM] at e11
      omega
    · exfalso
      have hdv : p ∣ 11 * N := ⟨5, by omega⟩
      rcases (Nat.Prime.dvd_mul pp).1 hdv with h11 | hNd
      · have := (Nat.prime_dvd_prime_iff_eq pp (by norm_num)).1 h11
        subst this
        omega
      · have := Nat.le_of_dvd (by omega) hNd
        omega
    · have hM : 11 * N / p = 5 := Nat.div_eq_of_lt_le (by omega) (by omega)
      have hh : (2 : ℤ) ≤ phi ((N : ℝ) / p) :=
        phi_ge N p hp0 2 fun k hk0 hk => chi_S6b N p k (by omega) (by omega) (by omega) hk0 hk
      rw [hM] at e11
      omega
  · have ha : 8 * N / p = 7 := Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [ha] at e8
    rcases Nat.lt_trichotomy (11 * N) (10 * p) with h5 | h5 | h5
    · have hM : 11 * N / p = 9 := Nat.div_eq_of_lt_le (by omega) (by omega)
      rw [hM] at e11
      omega
    · exfalso
      have hdv : p ∣ 11 * N := ⟨10, by omega⟩
      rcases (Nat.Prime.dvd_mul pp).1 hdv with h11 | hNd
      · have := (Nat.prime_dvd_prime_iff_eq pp (by norm_num)).1 h11
        subst this
        omega
      · have := Nat.le_of_dvd (by omega) hNd
        omega
    · have hM : 11 * N / p = 10 := Nat.div_eq_of_lt_le (by omega) (by omega)
      have hh : (1 : ℤ) ≤ phi ((N : ℝ) / p) :=
        phi_ge N p hp0 1 fun k hk0 hk => chi_S12 N p k (by omega) (by omega) (by omega) hk0 hk
      rw [hM] at e11
      omega

def pInt (p k : ℕ) (q : ℚ) : Prop := ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q * b = (p : ℚ) ^ k * a

theorem pz_prime {p : ℕ} (pp : p.Prime) : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp pp

theorem not_dvd_one' {p : ℕ} (pp : p.Prime) : ¬ (p : ℤ) ∣ 1 := (pz_prime pp).not_dvd_one

theorem pInt_of_dvd {p : ℕ} (pp : p.Prime) {k : ℕ} (z : ℤ) (h : (p : ℤ) ^ k ∣ z) : pInt p k z := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨c, 1, not_dvd_one' pp, by push_cast; ring⟩

theorem pInt_zero {p : ℕ} (pp : p.Prime) (k : ℕ) : pInt p k 0 :=
  ⟨0, 1, not_dvd_one' pp, by ring⟩

theorem pInt_int {p : ℕ} (pp : p.Prime) (z : ℤ) : pInt p 0 z :=
  pInt_of_dvd pp z (by rw [pow_zero]; exact one_dvd z)

theorem pInt_mono {p : ℕ} {k k' : ℕ} (hk : k' ≤ k) {q : ℚ} (h : pInt p k q) : pInt p k' q := by
  obtain ⟨a, b, hb, e⟩ := h
  refine ⟨(p : ℤ) ^ (k - k') * a, b, hb, ?_⟩
  rw [e, Int.cast_mul, Int.cast_pow, Int.cast_natCast, ← mul_assoc, ← pow_add,
    Nat.add_sub_cancel' hk]

theorem pInt_mul {p : ℕ} (pp : p.Prime) {k1 k2 : ℕ} {q1 q2 : ℚ} (h1 : pInt p k1 q1)
    (h2 : pInt p k2 q2) : pInt p (k1 + k2) (q1 * q2) := by
  obtain ⟨a1, b1, hb1, e1⟩ := h1
  obtain ⟨a2, b2, hb2, e2⟩ := h2
  refine ⟨a1 * a2, b1 * b2, fun h => ((pz_prime pp).dvd_or_dvd h).elim hb1 hb2, ?_⟩
  rw [Int.cast_mul, Int.cast_mul, pow_add]
  linear_combination (q2 * (b2 : ℚ)) * e1 + ((p : ℚ) ^ k1 * (a1 : ℚ)) * e2

theorem pInt_add {p : ℕ} (pp : p.Prime) {k : ℕ} {q1 q2 : ℚ} (h1 : pInt p k q1)
    (h2 : pInt p k q2) : pInt p k (q1 + q2) := by
  obtain ⟨a1, b1, hb1, e1⟩ := h1
  obtain ⟨a2, b2, hb2, e2⟩ := h2
  refine ⟨a1 * b2 + a2 * b1, b1 * b2, fun h => ((pz_prime pp).dvd_or_dvd h).elim hb1 hb2, ?_⟩
  push_cast
  linear_combination (b2 : ℚ) * e1 + (b1 : ℚ) * e2

theorem pInt_neg {p : ℕ} {k : ℕ} {q : ℚ} (h : pInt p k q) : pInt p k (-q) := by
  obtain ⟨a, b, hb, e⟩ := h
  exact ⟨-a, b, hb, by push_cast; linear_combination -e⟩

theorem pInt_sub {p : ℕ} (pp : p.Prime) {k : ℕ} {q1 q2 : ℚ} (h1 : pInt p k q1)
    (h2 : pInt p k q2) : pInt p k (q1 - q2) := by
  rw [sub_eq_add_neg]; exact pInt_add pp h1 (pInt_neg h2)

theorem pInt_sum {p : ℕ} (pp : p.Prime) {k : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (H : ∀ i ∈ s, pInt p k (f i)) : pInt p k (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [sum_empty]; exact pInt_zero pp k
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact pInt_add pp (H a (mem_insert_self a s)) (ih fun i hi => H i (mem_insert_of_mem hi))

theorem dvd_of_pInt {p : ℕ} (pp : p.Prime) {k : ℕ} (z : ℤ) (h : pInt p k z) :
    (p : ℤ) ^ k ∣ z := by
  obtain ⟨a, b, hb, e⟩ := h
  have e' : z * b = (p : ℤ) ^ k * a := by exact_mod_cast e
  exact (((pz_prime pp).coprime_iff_not_dvd.2 hb).pow_left).dvd_of_dvd_mul_right ⟨a, e'⟩

theorem pInt_frac {p : ℕ} (pp : p.Prime) (num den : ℤ) (a b k : ℕ) (wn wd : ℤ)
    (hn : num = (p : ℤ) ^ a * wn) (hd : den = (p : ℤ) ^ b * wd) (hwd : ¬ (p : ℤ) ∣ wd)
    (hk : k + b ≤ a) : pInt p k ((num : ℚ) / den) := by
  have hwd0 : (wd : ℚ) ≠ 0 := by
    rintro h; exact hwd (by rw [Int.cast_eq_zero.1 h]; exact dvd_zero _)
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 pp.ne_zero
  obtain ⟨c, rfl⟩ : ∃ c, a = b + (k + c) := ⟨a - b - k, by omega⟩
  refine ⟨(p : ℤ) ^ c * wn, wd, hwd, ?_⟩
  rw [hn, hd, pow_add, pow_add]
  push_cast
  rw [mul_assoc, mul_div_mul_left _ _ (pow_ne_zero _ hp0), div_mul_cancel₀ _ hwd0]
  ring

theorem small_val {p : ℕ} (pp : p.Prime) (n : ℕ) (h1 : 0 < n) (h2 : n < p ^ 2) :
    ∃ e : ℕ, ∃ w : ℤ, e ≤ 1 ∧ ¬ (p : ℤ) ∣ w ∧ (n : ℤ) = (p : ℤ) ^ e * w := by
  by_cases hd : p ∣ n
  · obtain ⟨c, rfl⟩ := hd
    have hc : c < p := by
      rw [pow_two] at h2
      exact Nat.lt_of_mul_lt_mul_left h2
    have hc0 : 0 < c := Nat.pos_of_mul_pos_left h1
    refine ⟨1, c, le_rfl, fun h => Nat.not_dvd_of_pos_of_lt hc0 hc (Int.natCast_dvd_natCast.1 h), ?_⟩
    push_cast; ring
  · exact ⟨0, n, Nat.zero_le _, fun h => hd (Int.natCast_dvd_natCast.1 h), by ring⟩

theorem pInt_div_nat {p : ℕ} (pp : p.Prime) {k : ℕ} (q : ℚ) (n : ℕ) (h1 : 0 < n) (h2 : n < p ^ 2)
    (hq : pInt p (k + 1) q) : pInt p k (q / n) := by
  obtain ⟨e, w, he, hw, hn⟩ := small_val pp n h1 h2
  obtain ⟨a, b, hb, eq⟩ := hq
  have hw0 : (w : ℚ) ≠ 0 := by
    rintro h; exact hw (by rw [Int.cast_eq_zero.1 h]; exact dvd_zero _)
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 pp.ne_zero
  refine ⟨(p : ℤ) ^ (1 - e) * a, b * w, fun h => ((pz_prime pp).dvd_or_dvd h).elim hb hw, ?_⟩
  have hn' : (n : ℚ) = (p : ℚ) ^ e * w := by exact_mod_cast hn
  rw [show k + 1 = e + (k + (1 - e)) by omega, pow_add, pow_add] at eq
  rw [hn']
  push_cast
  rw [div_mul_eq_mul_div, ← mul_assoc, mul_div_mul_right _ _ hw0, eq, mul_assoc,
    mul_div_cancel_left₀ _ (pow_ne_zero _ hp0), mul_assoc]

def IP (c : ℤ) (n : ℕ) : ℤ := ∏ i ∈ range n, (c - i)

theorem neg_one_ediv (p : ℤ) (hp : 1 ≤ p) : (-1 : ℤ) / p = -1 :=
  qexact (-1) p (-1) (by omega) (by omega) (by omega)

theorem IP_val {p : ℕ} (pp : p.Prime) (c : ℤ) (M : ℕ) (hM : M ≤ p ^ 2) :
    ∀ n : ℕ, IP c n ≠ 0 → (∀ i < n, -(M : ℤ) < c - i ∧ c - i < M) →
      ∃ e : ℕ, ∃ w : ℤ, ¬ (p : ℤ) ∣ w ∧ IP c n = (p : ℤ) ^ e * w ∧ (e : ℤ) = c / p - (c - n) / p
  | 0, _, _ => ⟨0, 1, not_dvd_one' pp, by rw [IP, prod_range_zero]; ring, by
      rw [Nat.cast_zero, sub_zero, sub_self]⟩
  | n + 1, hne, hbd => by
    have hp1 : (1 : ℤ) ≤ p := by exact_mod_cast pp.one_lt.le
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast pp.ne_zero
    rw [IP, prod_range_succ] at hne
    obtain ⟨e, w, hw, he, hee⟩ := IP_val pp c M hM n (mul_ne_zero_iff.1 hne).1
      (fun i hi => hbd i (by omega))
    have hx0 : c - n ≠ 0 := (mul_ne_zero_iff.1 hne).2
    have hxb := hbd n (by omega)
    have hIP : IP c (n + 1) = IP c n * (c - n) := by rw [IP, IP, prod_range_succ]
    by_cases hx : (p : ℤ) ∣ c - n
    · obtain ⟨y, hy⟩ := hx
      have hy' : ¬ (p : ℤ) ∣ y := by
        rintro ⟨z, rfl⟩
        have h2 : ((p : ℤ) ^ 2) ∣ c - n := ⟨z, by rw [hy]; ring⟩
        have h3 := Int.natAbs_le_of_dvd_ne_zero h2 hx0
        rw [Int.natAbs_pow, Int.natAbs_natCast] at h3
        omega
      refine ⟨e + 1, w * y, fun h => ((pz_prime pp).dvd_or_dvd h).elim hw hy', ?_, ?_⟩
      · rw [hIP, he, hy]; ring
      · have q1 : (c - (n : ℤ)) / p = y := by rw [hy, Int.mul_ediv_cancel_left _ hp0]
        have q2 : (c - ((n + 1 : ℕ) : ℤ)) / p = y - 1 := by
          rw [show c - ((n + 1 : ℕ) : ℤ) = -1 + p * y by push_cast; omega,
            Int.add_mul_ediv_left _ _ hp0, neg_one_ediv _ hp1]
          ring
        push_cast at hee q2 ⊢
        omega
    · refine ⟨e, w * (c - n), fun h => ((pz_prime pp).dvd_or_dvd h).elim hw hx, ?_, ?_⟩
      · rw [hIP, he]; ring
      · have hm := Int.emod_add_mul_ediv (c - n) p
        have hm1 : (c - n) % p ≠ 0 := fun h => hx (Int.dvd_of_emod_eq_zero h)
        have hm2 := Int.emod_nonneg (c - n) hp0
        have hm3 := Int.emod_lt_of_pos (c - n) (show (0 : ℤ) < p by omega)
        have q2 : (c - ((n + 1 : ℕ) : ℤ)) / p = (c - n) / p := by
          rw [show c - ((n + 1 : ℕ) : ℤ) = ((c - n) % p - 1) + p * ((c - n) / p) by push_cast; omega,
            Int.add_mul_ediv_left _ _ hp0, Int.ediv_eq_zero_of_lt (by omega) (by omega), zero_add]
        push_cast at hee q2 ⊢
        omega

theorem IP_fact (n : ℕ) : IP n n = (n.factorial : ℤ) := by
  induction n with
  | zero => rw [IP, prod_range_zero, Nat.factorial_zero, Nat.cast_one]
  | succ n ih =>
    rw [IP, prod_range_succ', Nat.factorial_succ, Nat.cast_mul, ← ih, IP]
    push_cast
    rw [mul_comm]
    congr 1
    exact prod_congr rfl fun i _ => by ring

theorem desc_eval_int (c : ℤ) (b : ℕ) : (descPochhammer ℚ b).eval (c : ℚ) = (IP c b : ℚ) := by
  induction b with
  | zero => rw [descPochhammer_zero, eval_one, IP, prod_range_zero, Int.cast_one]
  | succ n ih =>
    rw [descPochhammer_succ_right, eval_mul, ih, eval_sub, eval_X, eval_natCast, IP, IP,
      prod_range_succ]
    push_cast
    rfl

theorem fact_val {p : ℕ} (pp : p.Prime) (n : ℕ) (hn : n < p ^ 2) :
    ∃ w : ℤ, ¬ (p : ℤ) ∣ w ∧ (n.factorial : ℤ) = (p : ℤ) ^ (n / p) * w := by
  have hne : IP n n ≠ 0 := by rw [IP_fact]; exact_mod_cast Nat.factorial_ne_zero n
  obtain ⟨e, w, hw, he, hee⟩ := IP_val pp n (p ^ 2) le_rfl n hne (fun i hi => by
    constructor <;> omega)
  refine ⟨w, hw, ?_⟩
  rw [← IP_fact, he]
  congr 2
  rw [sub_self, Int.zero_ediv, sub_zero, ← Int.natCast_div] at hee
  exact_mod_cast hee

theorem choose_pInt {p : ℕ} (pp : p.Prime) (n k : ℕ) (hk : k ≤ n) (hn : n < p ^ 2) :
    pInt p (n / p - k / p - (n - k) / p) (n.choose k : ℚ) := by
  obtain ⟨wn, hwn, en⟩ := fact_val pp n hn
  obtain ⟨wk, hwk, ek⟩ := fact_val pp k (by omega)
  obtain ⟨wm, hwm, em⟩ := fact_val pp (n - k) (by omega)
  have hle : k / p + (n - k) / p ≤ (k + (n - k)) / p := Nat.div_add_div_le_add_div
  rw [Nat.add_sub_cancel' hk] at hle
  have hc : (n.choose k : ℚ) = ((n.factorial : ℤ) : ℚ) / (((k.factorial * (n - k).factorial : ℕ) : ℤ) : ℚ) := by
    rw [eq_div_iff (by positivity), Int.cast_natCast, Int.cast_natCast, ← Nat.cast_mul, ← mul_assoc, Nat.choose_mul_factorial_mul_factorial hk]
  rw [hc]
  refine pInt_frac pp _ _ (n / p) (k / p + (n - k) / p) _ wn (wk * wm) en ?_
    (fun h => ((pz_prime pp).dvd_or_dvd h).elim hwk hwm) (by omega)
  push_cast
  rw [ek, em, pow_add]
  ring

def IntVal (M : ℤ) (P : ℚ[X]) : Prop := ∀ z : ℤ, ∃ w : ℤ, P.eval (z : ℚ) = M * w

theorem iv_forward (P : ℚ[X]) (n : ℕ) (hn : P.natDegree < n) (M a : ℤ)
    (h : ∀ t < n, ∃ w : ℤ, P.eval ((a : ℚ) + t) = M * w) :
    ∀ t : ℕ, ∃ w : ℤ, P.eval ((a : ℚ) + t) = M * w := by
  choose! W hW using h
  intro t
  have hN := congrArg (eval (t : ℚ)) (newton P (a : ℚ) n hn)
  rw [eval_comp, eval_add, eval_X, eval_C, eval_finsetSum] at hN
  refine ⟨∑ k ∈ range n, (∑ i ∈ range (k + 1), (-1) ^ (k - i) * (k.choose i : ℤ) * W i) *
    (t.choose k : ℤ), ?_⟩
  rw [add_comm, hN]
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun k hk => ?_
  rw [eval_mul, eval_C, bin_eval_nat, dl]
  have hd : ∑ i ∈ range (k + 1), (-1 : ℚ) ^ (k - i) * (k.choose i : ℚ) * P.eval ((i : ℚ) + a) =
      M * ∑ i ∈ range (k + 1), (-1 : ℚ) ^ (k - i) * (k.choose i : ℚ) * (W i : ℚ) := by
    rw [mul_sum]
    refine sum_congr rfl fun i hi => ?_
    rw [add_comm, hW i (by have := mem_range.1 hi; have := mem_range.1 hk; omega)]
    ring
  rw [hd]
  ring

theorem iv (P : ℚ[X]) (n : ℕ) (hn : P.natDegree < n) (M a : ℤ)
    (h : ∀ t < n, ∃ w : ℤ, P.eval ((a : ℚ) + t) = M * w) : IntVal M P := by
  have hn1 : 1 ≤ n := by omega
  intro z
  rcases le_or_gt a z with hz | hz
  · obtain ⟨w, hw⟩ := iv_forward P n hn M a h (z - a).toNat
    refine ⟨w, ?_⟩
    rw [← hw]
    congr 1
    have e : (((z - a).toNat : ℕ) : ℤ) = z - a := Int.toNat_of_nonneg (by omega)
    have e' : (((z - a).toNat : ℕ) : ℚ) = (z : ℚ) - a := by exact_mod_cast e
    rw [e']
    ring
  · have hQd : (P.comp (-X)).natDegree < n := by
      rw [natDegree_comp, natDegree_neg, natDegree_X, mul_one]; exact hn
    have hQ : ∀ t < n, ∃ w : ℤ, (P.comp (-X)).eval (((-(a + n - 1) : ℤ) : ℚ) + t) = M * w := by
      intro t ht
      obtain ⟨w, hw⟩ := h (n - 1 - t) (by omega)
      refine ⟨w, ?_⟩
      rw [eval_comp, eval_neg, eval_X, ← hw]
      congr 1
      have e : ((n - 1 - t : ℕ) : ℤ) = (n : ℤ) - 1 - t := by omega
      have e' : ((n - 1 - t : ℕ) : ℚ) = (n : ℚ) - 1 - t := by exact_mod_cast e
      rw [e']
      push_cast
      ring
    obtain ⟨w, hw⟩ := iv_forward (P.comp (-X)) n hQd M _ hQ (-z + a + n - 1).toNat
    refine ⟨w, ?_⟩
    rw [← hw, eval_comp, eval_neg, eval_X]
    congr 1
    have e : (((-z + a + n - 1).toNat : ℕ) : ℤ) = -z + a + n - 1 := Int.toNat_of_nonneg (by omega)
    have e' : (((-z + a + n - 1).toNat : ℕ) : ℚ) = -(z : ℚ) + a + n - 1 := by exact_mod_cast e
    rw [e']
    push_cast
    ring

theorem IntVal_add {M : ℤ} {P Q : ℚ[X]} (hP : IntVal M P) (hQ : IntVal M Q) : IntVal M (P + Q) :=
  fun z => by
    obtain ⟨a, ha⟩ := hP z
    obtain ⟨b, hb⟩ := hQ z
    exact ⟨a + b, by rw [eval_add, ha, hb]; push_cast; ring⟩

theorem IntVal_mul {M : ℤ} {P Q : ℚ[X]} (hP : IntVal M P) (hQ : IntVal 1 Q) : IntVal M (P * Q) :=
  fun z => by
    obtain ⟨a, ha⟩ := hP z
    obtain ⟨b, hb⟩ := hQ z
    exact ⟨a * b, by rw [eval_mul, ha, hb]; push_cast; ring⟩

theorem IntVal_C (c : ℤ) : IntVal 1 (C (c : ℚ)) := fun _ => ⟨c, by rw [eval_C]; ring⟩

theorem IntVal_X : IntVal 1 (X : ℚ[X]) := fun z => ⟨z, by rw [eval_X]; ring⟩

theorem IntVal_zero (M : ℤ) : IntVal M 0 := fun _ => ⟨0, by rw [eval_zero]; ring⟩

theorem IntVal_C_mul {M : ℤ} (c : ℤ) {P : ℚ[X]} (hP : IntVal M P) : IntVal M (C (c : ℚ) * P) := by
  rw [mul_comm]; exact IntVal_mul hP (IntVal_C c)

theorem IntVal_sum {M : ℤ} {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) (H : ∀ i ∈ s, IntVal M (f i)) :
    IntVal M (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [sum_empty]; exact IntVal_zero M
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact IntVal_add (H a (mem_insert_self a s)) (ih fun i hi => H i (mem_insert_of_mem hi))

theorem IntVal_pow (P : ℚ[X]) (hP : IntVal 1 P) (r : ℕ) : IntVal 1 (P ^ r) := by
  induction r with
  | zero => rw [pow_zero, ← C_1, ← Int.cast_one]; exact IntVal_C 1
  | succ r ih => rw [pow_succ]; exact IntVal_mul ih hP

theorem binom_eval_nat (u b s : ℕ) : (binomPoly ℚ (u : ℚ) b).eval (s : ℚ) = (((s + u).choose b : ℕ) : ℚ) := by
  rw [binomPoly, eval_mul, eval_C, eval_comp, eval_add, eval_X, eval_C,
    show (s : ℚ) + u = ((s + u : ℕ) : ℚ) by push_cast; ring, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  exact inv_mul_cancel_left₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero b)) _

theorem binom_natDegree_Q (a : ℚ) (b : ℕ) : (binomPoly ℚ a b).natDegree = b := by
  rw [binomPoly, natDegree_C_mul (inv_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero b))),
    natDegree_comp, descPochhammer_natDegree, natDegree_X_add_C, mul_one]

theorem binom_IntVal (u b : ℕ) : IntVal 1 (binomPoly ℚ (u : ℚ) b) :=
  iv _ (b + 1) (by rw [binom_natDegree_Q]; omega) 1 0 fun t _ =>
    ⟨((t + u).choose b : ℕ), by rw [Int.cast_zero, zero_add, binom_eval_nat]; push_cast; ring⟩

theorem DD_mul (f g : ℚ[X]) (a : ℚ) : DD (f * g) a = f * DD g a + C (g.eval a) * DD f a :=
  DD_unique _ _ _ (by
    rw [mul_add, mul_left_comm, DD_spec, mul_left_comm (X - C a) (C _), DD_spec, eval_mul, C_mul]
    ring)

theorem DD_Xpow_IntVal (r j : ℕ) : IntVal 1 (DD (X ^ r) (j : ℚ)) := by
  have h : DD (X ^ r) (j : ℚ) = ∑ i ∈ range r, X ^ i * C ((j : ℚ) ^ (r - 1 - i)) := by
    refine DD_unique _ _ _ ?_
    rw [eval_pow, eval_X, C_pow, mul_comm, ← geom_sum₂_mul]
    congr 1
    exact sum_congr rfl fun i _ => by rw [C_pow]
  rw [h]
  exact IntVal_sum _ _ fun i _ => IntVal_mul (IntVal_pow X IntVal_X i)
    (by rw [show ((j : ℚ) ^ (r - 1 - i)) = (((j : ℤ) ^ (r - 1 - i) : ℤ) : ℚ) by push_cast; ring];
        exact IntVal_C _)

theorem DD_binom_IntVal (u b j : ℕ) :
    IntVal 1 (C (lcmUpTo b : ℚ) * DD (binomPoly ℚ (u : ℚ) b) (j : ℚ)) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · have h1 : binomPoly ℚ (u : ℚ) 0 = 1 := by
      rw [binomPoly, descPochhammer_zero, one_comp, Nat.factorial_zero, Nat.cast_one, inv_one, C_1,
        mul_one]
    rw [h1, show DD 1 (j : ℚ) = 0 from DD_unique _ _ _ (by rw [mul_zero, eval_one, C_1, sub_self]),
      mul_zero]
    exact IntVal_zero 1
  · refine iv _ b ?_ 1 (j + 1) fun t ht => ?_
    · refine (natDegree_C_mul_le _ _).trans_lt ?_
      rw [DD, natDegree_divByMonic _ (monic_X_sub_C _), natDegree_X_sub_C, natDegree_sub_C,
        binom_natDegree_Q]
      omega
    · have hdv : t + 1 ∣ lcmUpTo b := Finset.dvd_lcm (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
      refine ⟨((lcmUpTo b / (t + 1) : ℕ) : ℤ) *
        (((j + 1 + t + u).choose b : ℕ) - ((j + u).choose b : ℕ) : ℤ), ?_⟩
      have hs : ((((j : ℤ) + 1 : ℤ) : ℚ) + (t : ℚ)) = ((j + 1 + t : ℕ) : ℚ) := by push_cast; ring
      have hden : ((j + 1 + t : ℕ) : ℚ) - (j : ℚ) = (t : ℚ) + 1 := by push_cast; ring
      obtain ⟨c, hc⟩ := hdv
      rw [eval_mul, eval_C, hs, DD_eval _ _ _ (by push_cast; linarith), binom_eval_nat,
        binom_eval_nat, hden, hc, Nat.mul_div_cancel_left c (Nat.succ_pos t)]
      push_cast
      field_simp

theorem L_closed (m : ℕ) : ∀ s : ℚ, (∀ j : ℕ, j ≤ m → s ≠ j) →
    ∑ j ∈ range (m + 1), om m j / (s - j) =
      (-1) ^ m * (m.factorial : ℚ) / ∏ j ∈ range (m + 1), (s - j) := by
  induction m with
  | zero =>
    intro s _
    simp only [zero_add, sum_range_one, prod_range_one, om, pow_zero, Nat.choose_self,
      Nat.cast_one, Nat.cast_zero, one_mul, Nat.factorial_zero]
  | succ m ih =>
    intro s hs
    have hsm : ∀ j : ℕ, j ≤ m → s ≠ j := fun j hj => hs j (by omega)
    have hs1 : ∀ j : ℕ, j ≤ m → s - 1 ≠ j := fun j hj h => hs (j + 1) (by omega)
      (by push_cast; linarith)
    have hrec : ∑ j ∈ range (m + 1 + 1), om (m + 1) j / (s - j) =
        ∑ j ∈ range (m + 1), om m j / (s - j) - ∑ j ∈ range (m + 1), om m j / (s - 1 - j) := by
      rw [sum_range_succ', sum_range_succ' (fun j => om m j / (s - j))]
      have e1 : ∀ j : ℕ, om (m + 1) (j + 1) = om m (j + 1) - om m j := fun j => by
        unfold om; rw [Nat.choose_succ_succ]; push_cast; ring
      simp only [e1, sub_div, sum_sub_distrib]
      rw [sum_range_succ (fun j => om m (j + 1) / (s - ((j + 1 : ℕ) : ℚ))),
        show om m (m + 1) = 0 by rw [om, Nat.choose_succ_self, Nat.cast_zero, mul_zero]]
      have e2 : ∀ j : ℕ, s - ((j + 1 : ℕ) : ℚ) = s - 1 - j := fun j => by push_cast; ring
      simp only [e2, om, pow_zero, Nat.choose_zero_right, Nat.cast_one, Nat.cast_zero, sub_zero,
        zero_div, add_zero]
      ring
    rw [hrec, ih s hsm, ih (s - 1) hs1]
    have hA : ∏ j ∈ range (m + 1), (s - j) ≠ 0 :=
      prod_ne_zero_iff.2 fun j hj => sub_ne_zero.2 (hsm j (by have := mem_range.1 hj; omega))
    have hB : ∏ j ∈ range (m + 1), (s - 1 - j) ≠ 0 :=
      prod_ne_zero_iff.2 fun j hj => sub_ne_zero.2 (hs1 j (by have := mem_range.1 hj; omega))
    have e1 : (∏ j ∈ range (m + 1), (s - j)) * (s - ((m + 1 : ℕ) : ℚ)) =
        ∏ j ∈ range (m + 1 + 1), (s - j) := (prod_range_succ _ _).symm
    have e2 : s * ∏ j ∈ range (m + 1), (s - 1 - j) = ∏ j ∈ range (m + 1 + 1), (s - j) := by
      rw [prod_range_succ' (fun j : ℕ => s - (j : ℚ)) (m + 1), Nat.cast_zero, sub_zero, mul_comm]
      exact congrArg (· * s) (prod_congr rfl fun j _ => by push_cast; ring)
    have hP : ∏ j ∈ range (m + 1 + 1), (s - j) ≠ 0 := by
      rw [← e1]; exact mul_ne_zero hA (sub_ne_zero.2 (hs (m + 1) le_rfl))
    rw [div_sub_div _ _ hA hB, div_eq_div_iff (mul_ne_zero hA hB) hP, Nat.factorial_succ,
      Nat.cast_mul, pow_succ]
    push_cast at e1 ⊢
    linear_combination (-((-1 : ℚ) ^ m * (m.factorial : ℚ) * ∏ j ∈ range (m + 1), (s - 1 - j))) * e1 +
      ((-1 : ℚ) ^ m * (m.factorial : ℚ) * ∏ j ∈ range (m + 1), (s - j)) * e2

theorem Sm_eval' (m : ℕ) (g : ℚ[X]) (s : ℚ) (hs : ∀ j : ℕ, j ≤ m → s ≠ j) :
    (Sm m g).eval s = g.eval s * ((-1) ^ m * (m.factorial : ℚ) / ∏ j ∈ range (m + 1), (s - j)) -
      ∑ j ∈ range (m + 1), om m j * g.eval (j : ℚ) / (s - j) := by
  rw [← L_closed m s hs, Sm, eval_finsetSum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun j hj => ?_
  rw [eval_smul, DD_eval _ _ _ (hs j (by have := mem_range.1 hj; omega)), smul_eq_mul]
  ring

def Pij (m j : ℕ) : ℚ[X] := ∏ i ∈ (range (m + 1)).erase j, (X - C (i : ℚ))

theorem Pi_identity (m : ℕ) (g : ℚ[X]) :
    (∏ j ∈ range (m + 1), (X - C (j : ℚ))) * Sm m g =
      C ((-1) ^ m * (m.factorial : ℚ)) * g - ∑ j ∈ range (m + 1), C (om m j * g.eval (j : ℚ)) * Pij m j := by
  apply eq_of_infinite_eval_eq
  refine (Set.Ioi_infinite (m : ℚ)).mono fun s hs => ?_
  have hs' : (m : ℚ) < s := hs
  have hsj : ∀ j : ℕ, j ≤ m → s ≠ j := fun j hj h => by
    have : (j : ℚ) ≤ m := by exact_mod_cast hj
    linarith
  show eval s _ = eval s _
  have hP : ∏ j ∈ range (m + 1), (s - j) ≠ 0 :=
    prod_ne_zero_iff.2 fun j hj => sub_ne_zero.2 (hsj j (by have := mem_range.1 hj; omega))
  rw [eval_mul, Sm_eval' m g s hsj, eval_sub, eval_mul, eval_C, eval_finsetSum, eval_prod]
  simp only [eval_sub, eval_X, eval_C, eval_mul]
  rw [mul_sub, mul_sum]
  congr 1
  · field_simp
  · refine sum_congr rfl fun j hj => ?_
    have hj' : j ∈ range (m + 1) := hj
    rw [Pij, eval_prod, ← mul_prod_erase _ _ hj']
    simp only [eval_sub, eval_X, eval_C]
    have hne : s - j ≠ 0 := sub_ne_zero.2 (hsj j (by have := mem_range.1 hj; omega))
    field_simp

theorem Sm_natDegree (m : ℕ) (g : ℚ[X]) (hg : m < g.natDegree) :
    (Sm m g).natDegree + (m + 1) ≤ g.natDegree := by
  rcases eq_or_ne (Sm m g) 0 with h0 | h0
  · rw [h0, natDegree_zero]
    omega
  · have hmon : (∏ j ∈ range (m + 1), (X - C (j : ℚ))).Monic :=
      monic_prod_of_monic _ _ fun j _ => monic_X_sub_C _
    have hdeg := congrArg natDegree (Pi_identity m g)
    rw [natDegree_mul hmon.ne_zero h0, natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C _] at hdeg
    simp only [natDegree_X_sub_C, sum_const, card_range, smul_eq_mul, mul_one] at hdeg
    have hb : (C ((-1) ^ m * (m.factorial : ℚ)) * g -
        ∑ j ∈ range (m + 1), C (om m j * g.eval (j : ℚ)) * Pij m j).natDegree ≤ g.natDegree := by
      refine (natDegree_sub_le _ _).trans (max_le (natDegree_C_mul_le _ _) ?_)
      refine (natDegree_sum_le_of_forall_le _ _ fun j hj => ?_).trans hg.le
      refine (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans ?_)
      simp only [natDegree_X_sub_C, sum_const, smul_eq_mul, mul_one]
      rw [card_erase_of_mem hj, card_range]
      omega
    omega

theorem dvd_lcmUpTo {k n : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ n) : k ∣ lcmUpTo n :=
  Finset.dvd_lcm (Finset.mem_Icc.2 ⟨h1, h2⟩)

theorem lcmUpTo_mono {a b : ℕ} (h : a ≤ b) : lcmUpTo a ∣ lcmUpTo b :=
  Finset.lcm_mono (Finset.Icc_subset_Icc le_rfl h)

theorem lcmUpTo_pos (n : ℕ) : 0 < lcmUpTo n := Nat.pos_of_ne_zero fun h => by
  obtain ⟨x, hx, h0⟩ := Finset.lcm_eq_zero_iff.1 h
  rw [Finset.mem_Icc] at hx
  rw [id_eq] at h0
  omega

def cZ (N j : ℕ) : ℤ :=
  (-1) ^ j * (((11 * N).choose j * ((j + 10 * N).choose (8 * N) * (j + 9 * N).choose (8 * N) *
    (j + 11 * N).choose (8 * N)) : ℕ) : ℤ)

theorem cj_eq (N j : ℕ) : cj N j = (cZ N j : ℚ) := by
  rw [cj, cZ, Fpoly, eval_mul, eval_mul, binom_eval_nat, binom_eval_nat, binom_eval_nat]
  push_cast
  ring

def Sset (N : ℕ) : Finset ℕ := (Icc 1 (13 * N)).filter (fun p => p.Prime ∧ 50 * N < p ^ 2)

theorem mem_Sset {N p : ℕ} (h : p ∈ Sset N) : p.Prime ∧ 50 * N < p ^ 2 ∧ 1 ≤ p ∧ p ≤ 13 * N := by
  obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.1 h
  exact ⟨h2, h3, (Finset.mem_Icc.1 h1).1, (Finset.mem_Icc.1 h1).2⟩

theorem G_dvd (N : ℕ) (z : ℤ) (H : ∀ p ∈ Sset N, (p : ℤ) ^ (phi ((N : ℝ) / p)).toNat ∣ z) :
    (GN N : ℤ) ∣ z := by
  rw [show GN N = ∏ p ∈ Sset N, p ^ (phi ((N : ℝ) / p)).toNat from rfl, Nat.cast_prod]
  simp only [Nat.cast_pow]
  refine Finset.prod_dvd_of_coprime (fun p hp q hq hpq => ?_) H
  exact ((Nat.coprime_primes (mem_Sset hp).1 (mem_Sset hq).1).2 hpq).isCoprime.pow

theorem hp_zero (N p : ℕ) (hp0 : 0 < p) (h : 11 * N < p) : (phi ((N : ℝ) / p)).toNat = 0 := by
  have h1 := phi_le_chi N p hp0 0
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp0
  have h2 : chi N p 0 = 0 := by
    have e1 := qexact (11 * N) p 0 hp' (by omega) (by omega)
    have e2 := qexact (11 * N + -0) p 0 hp' (by omega) (by omega)
    have e3 := qexact (10 * N + 0) p 0 hp' (by omega) (by omega)
    have e4 := qexact (9 * N + 0) p 0 hp' (by omega) (by omega)
    have e5 := qexact (11 * N + 0) p 0 hp' (by omega) (by omega)
    have e6 := qexact (8 * N) p 0 hp' (by omega) (by omega)
    have e7 := qexact (2 * N + 0) p 0 hp' (by omega) (by omega)
    have e8 := qexact (N + 0) p 0 hp' (by omega) (by omega)
    have e9 := qexact (3 * N + 0) p 0 hp' (by omega) (by omega)
    have e0 := qexact 0 p 0 hp' (by omega) (by omega)
    unfold chi chi2
    omega
  exact Int.toNat_eq_zero.2 (by omega)

theorem hp_le_chi (N p : ℕ) (hp0 : 0 < p) (j : ℤ) :
    ((phi ((N : ℝ) / p)).toNat : ℤ) ≤ chi N p j := by
  rw [Int.toNat_of_nonneg (phi_nonneg N p hp0)]
  exact phi_le_chi N p hp0 j

theorem chi_nat (N p j : ℕ) (hp : 0 < p) (hj : j ≤ 11 * N) :
    chi N p j = ((11 * N / p : ℕ) : ℤ) - ((j / p : ℕ) : ℤ) - (((11 * N - j) / p : ℕ) : ℤ) +
      (((j + 10 * N) / p : ℕ) : ℤ) + (((j + 9 * N) / p : ℕ) : ℤ) + (((j + 11 * N) / p : ℕ) : ℤ) -
      3 * ((8 * N / p : ℕ) : ℤ) - (((2 * N + j) / p : ℕ) : ℤ) - (((N + j) / p : ℕ) : ℤ) -
      (((3 * N + j) / p : ℕ) : ℤ) := by
  unfold chi chi2
  simp only [Int.natCast_div]
  push_cast [Nat.cast_sub hj]
  ring_nf

theorem cZ_dvd (N p j : ℕ) (pp : p.Prime) (hp2 : 50 * N < p ^ 2) (hj : j ≤ 11 * N) :
    (p : ℤ) ^ (phi ((N : ℝ) / p)).toNat ∣ cZ N j := by
  have hp0 := pp.pos
  apply dvd_of_pInt pp
  have c1 := choose_pInt pp (11 * N) j hj (by omega)
  have c2 := choose_pInt pp (j + 10 * N) (8 * N) (by omega) (by omega)
  have c3 := choose_pInt pp (j + 9 * N) (8 * N) (by omega) (by omega)
  have c4 := choose_pInt pp (j + 11 * N) (8 * N) (by omega) (by omega)
  rw [show j + 10 * N - 8 * N = 2 * N + j by omega] at c2
  rw [show j + 9 * N - 8 * N = N + j by omega] at c3
  rw [show j + 11 * N - 8 * N = 3 * N + j by omega] at c4
  have hs : pInt p 0 (((-1 : ℤ) ^ j : ℤ) : ℚ) := pInt_int pp _
  have hall := pInt_mul pp hs (pInt_mul pp c1 (pInt_mul pp (pInt_mul pp c2 c3) c4))
  have hc : ((cZ N j : ℤ) : ℚ) = (((-1 : ℤ) ^ j : ℤ) : ℚ) * ((((11 * N).choose j : ℕ) : ℚ) *
      (((((j + 10 * N).choose (8 * N) : ℕ) : ℚ) * (((j + 9 * N).choose (8 * N) : ℕ) : ℚ)) *
        (((j + 11 * N).choose (8 * N) : ℕ) : ℚ))) := by
    rw [cZ]; push_cast; ring
  rw [hc]
  refine pInt_mono ?_ hall
  have h1 := hp_le_chi N p hp0 j
  rw [chi_nat N p j hp0 hj] at h1
  have s1 : j / p + (11 * N - j) / p ≤ 11 * N / p := by
    have : j / p + (11 * N - j) / p ≤ (j + (11 * N - j)) / p := Nat.div_add_div_le_add_div
    rwa [show j + (11 * N - j) = 11 * N by omega] at this
  have s2 : 8 * N / p + (2 * N + j) / p ≤ (j + 10 * N) / p := by
    have : 8 * N / p + (2 * N + j) / p ≤ (8 * N + (2 * N + j)) / p := Nat.div_add_div_le_add_div
    rwa [show 8 * N + (2 * N + j) = j + 10 * N by omega] at this
  have s3 : 8 * N / p + (N + j) / p ≤ (j + 9 * N) / p := by
    have : 8 * N / p + (N + j) / p ≤ (8 * N + (N + j)) / p := Nat.div_add_div_le_add_div
    rwa [show 8 * N + (N + j) = j + 9 * N by omega] at this
  have s4 : 8 * N / p + (3 * N + j) / p ≤ (j + 11 * N) / p := by
    have : 8 * N / p + (3 * N + j) / p ≤ (8 * N + (3 * N + j)) / p := Nat.div_add_div_le_add_div
    rwa [show 8 * N + (3 * N + j) = j + 11 * N by omega] at this
  omega

theorem kummer_dvd (N j q : ℕ) (hq : q.Prime) (v : ℕ) (hQ1 : 12 * N < q ^ v) (hQ2 : q ^ v ≤ j + 2 * N)
    (hj : j ≤ 11 * N) (hN : 1 ≤ N) : q ∣ (j + 9 * N).choose (8 * N) := by
  have := Fact.mk hq
  have hv : 1 ≤ v := by
    rcases Nat.eq_zero_or_pos v with rfl | h
    · rw [pow_zero] at hQ1; omega
    · exact h
  have h8 : 8 * N < q ^ v := by omega
  have hjN : j + N < q ^ v := by omega
  refine dvd_of_one_le_padicValNat ?_
  rw [padicValNat_choose (show 8 * N ≤ j + 9 * N by omega) (Nat.lt_succ_self (Nat.log q (j + 9 * N)))]
  refine Finset.card_pos.2 ⟨v, Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨hv, ?_⟩, ?_⟩⟩
  · have := Nat.le_log_of_pow_le hq.one_lt (show q ^ v ≤ j + 9 * N by omega)
    omega
  · rw [Nat.mod_eq_of_lt h8, show j + 9 * N - 8 * N = j + N by omega, Nat.mod_eq_of_lt hjN]
    omega

theorem k_dvd (N j k : ℕ) (hN : 1 ≤ N) (hj : j ≤ 11 * N) (hk12 : 12 * N < k) (hk : k ≤ j + 2 * N) :
    k ∣ lcmUpTo (12 * N) * (j + 9 * N).choose (8 * N) := by
  have hk0 : k ≠ 0 := by omega
  have hX0 : lcmUpTo (12 * N) * (j + 9 * N).choose (8 * N) ≠ 0 :=
    mul_ne_zero (lcmUpTo_pos _).ne' (Nat.choose_pos (by omega)).ne'
  rw [← Nat.factorization_le_iff_dvd hk0 hX0, Finsupp.le_def]
  intro q
  by_cases hq : q.Prime
  · rw [← hq.pow_dvd_iff_le_factorization hX0]
    have hQk : q ^ k.factorization q ∣ k := Nat.ordProj_dvd k q
    have hQle : q ^ k.factorization q ≤ k := Nat.le_of_dvd (by omega) hQk
    by_cases hsmall : q ^ k.factorization q ≤ 12 * N
    · exact (dvd_lcmUpTo (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hq.ne_zero)) hsmall).mul_right _
    · have hv : 1 ≤ k.factorization q := by
        rcases Nat.eq_zero_or_pos (k.factorization q) with h0 | h0
        · rw [h0, pow_zero] at hsmall; omega
        · exact h0
      have hpow : q ^ k.factorization q = q ^ (k.factorization q - 1) * q := by
        rw [← pow_succ, Nat.sub_add_cancel hv]
      have h2 : q ^ (k.factorization q - 1) * 2 ≤ q ^ (k.factorization q - 1) * q :=
        Nat.mul_le_mul_left _ hq.two_le
      rw [hpow]
      refine mul_dvd_mul (dvd_lcmUpTo (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hq.ne_zero))
        (by omega)) (kummer_dvd N j q hq (k.factorization q) (by omega) (by omega) hj hN)
  · rw [Nat.factorization_eq_zero_of_not_prime k hq]
    exact Nat.zero_le _

theorem choose_dvd_cZ (N j : ℕ) : (((j + 9 * N).choose (8 * N) : ℕ) : ℤ) ∣ cZ N j := by
  rw [cZ]
  exact Dvd.dvd.mul_left (Int.natCast_dvd_natCast.2 (((dvd_mul_left _ _).mul_right _).mul_left _)) _

theorem harm_term (N j k : ℕ) (r : ℕ) (hN : 1 ≤ N) (hr : r < 3) (hj : j ≤ 11 * N) (hk1 : 1 ≤ k)
    (hk : k ≤ j + 2 * N) :
    ∃ w : ℤ, ((lcmUpTo (12 * N) * lcmUpTo (13 * N + r) : ℕ) : ℚ) * (cZ N j : ℚ) / (k : ℚ) ^ 2 = w ∧
      (GN N : ℤ) ∣ w := by
  set D := lcmUpTo (12 * N) * lcmUpTo (13 * N + r)
  have hkk : ((k * k : ℕ) : ℤ) ∣ (D : ℤ) * cZ N j := by
    by_cases hk12 : k ≤ 12 * N
    · have : k * k ∣ D := mul_dvd_mul (dvd_lcmUpTo hk1 hk12) (dvd_lcmUpTo hk1 (by omega))
      exact (Int.natCast_dvd_natCast.2 this).mul_right _
    · have h1 : (k : ℤ) ∣ (lcmUpTo (12 * N) : ℤ) * cZ N j :=
        (Int.natCast_dvd_natCast.2 (k_dvd N j k hN hj (by omega) hk)).trans
          (by push_cast; exact mul_dvd_mul_left _ (choose_dvd_cZ N j))
      have h2 : (k : ℤ) ∣ (lcmUpTo (13 * N + r) : ℤ) :=
        Int.natCast_dvd_natCast.2 (dvd_lcmUpTo hk1 (by omega))
      have := mul_dvd_mul h2 h1
      rw [show (D : ℤ) * cZ N j = (lcmUpTo (13 * N + r) : ℤ) * ((lcmUpTo (12 * N) : ℤ) * cZ N j) by
        simp only [D]; push_cast; ring]
      push_cast
      exact this
  obtain ⟨w, hw⟩ := hkk
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hwq : ((D : ℕ) : ℚ) * (cZ N j : ℚ) / (k : ℚ) ^ 2 = w := by
    have : ((D : ℤ) : ℚ) * (cZ N j : ℚ) = ((k : ℚ) * k) * w := by exact_mod_cast hw
    rw [Int.cast_natCast] at this
    rw [this, pow_two]
    field_simp
  refine ⟨w, hwq, G_dvd N w fun p hp => ?_⟩
  obtain ⟨pp, hp2, hp1, hp13⟩ := mem_Sset hp
  by_cases hp12 : 12 * N < p
  · rw [hp_zero N p pp.pos (by omega), pow_zero]
    exact one_dvd _
  · apply dvd_of_pInt pp
    rw [← hwq]
    have hD : pInt p 2 ((D : ℕ) : ℚ) := by
      have hd1 : (p : ℤ) ∣ lcmUpTo (12 * N) := Int.natCast_dvd_natCast.2 (dvd_lcmUpTo hp1 (by omega))
      have hd2 : (p : ℤ) ∣ lcmUpTo (13 * N + r) := Int.natCast_dvd_natCast.2 (dvd_lcmUpTo hp1 (by omega))
      have := pInt_of_dvd pp ((D : ℕ) : ℤ) (by rw [pow_two]; simp only [D]; push_cast; exact mul_dvd_mul hd1 hd2)
      rwa [Int.cast_natCast] at this
    have hc := pInt_of_dvd pp _ (cZ_dvd N p j pp hp2 hj)
    have hm := pInt_mul pp hD hc
    rw [show 2 + (phi ((N : ℝ) / p)).toNat = ((phi ((N : ℝ) / p)).toNat + 1) + 1 by ring] at hm
    have h1 := pInt_div_nat pp _ k (by omega) (by omega) hm
    have h2 := pInt_div_nat pp _ k (by omega) (by omega) h1
    rwa [div_div, ← pow_two] at h2

theorem Spoly_eq (N r : ℕ) : Spoly N r = Sm (11 * N) (X ^ r * Fpoly N) := rfl

theorem DD_mul_IntVal (d j : ℕ) (f g : ℚ[X]) (hf : IntVal 1 f) (hg : IntVal 1 g)
    (hdf : IntVal 1 (C (d : ℚ) * DD f j)) (hdg : IntVal 1 (C (d : ℚ) * DD g j)) :
    IntVal 1 (C (d : ℚ) * DD (f * g) j) := by
  obtain ⟨w, hw⟩ := hg j
  rw [Int.cast_natCast, Int.cast_one, one_mul] at hw
  rw [DD_mul, mul_add, mul_left_comm (C (d : ℚ)) f, mul_comm f,
    mul_left_comm (C (d : ℚ)) (C _), hw]
  exact IntVal_add (IntVal_mul hdg hf) (IntVal_C_mul w hdf)

theorem F_IntVal (N : ℕ) : IntVal 1 (Fpoly N) :=
  IntVal_mul (IntVal_mul (binom_IntVal _ _) (binom_IntVal _ _)) (binom_IntVal _ _)

theorem DD_g_IntVal (N r j : ℕ) : IntVal 1 (C (lcmUpTo (8 * N) : ℚ) * DD (X ^ r * Fpoly N) j) :=
  DD_mul_IntVal _ _ _ _ (IntVal_pow X IntVal_X r) (F_IntVal N)
    (by have := IntVal_C_mul (lcmUpTo (8 * N) : ℤ) (DD_Xpow_IntVal r j)
        rwa [Int.cast_natCast] at this)
    (DD_mul_IntVal _ _ _ _ (IntVal_mul (binom_IntVal _ _) (binom_IntVal _ _)) (binom_IntVal _ _)
      (DD_mul_IntVal _ _ _ _ (binom_IntVal _ _) (binom_IntVal _ _) (DD_binom_IntVal _ _ _)
        (DD_binom_IntVal _ _ _)) (DD_binom_IntVal _ _ _))

theorem Sm_IntVal (m d : ℕ) (g : ℚ[X]) (H : ∀ j : ℕ, IntVal 1 (C (d : ℚ) * DD g j)) :
    IntVal 1 (C (d : ℚ) * Sm m g) := by
  rw [Sm, mul_sum]
  refine IntVal_sum _ _ fun j _ => ?_
  rw [smul_eq_C_mul, mul_left_comm (C (d : ℚ)), show om m j = (((-1) ^ j * (m.choose j : ℤ) : ℤ) : ℚ) by
    rw [om, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]]
  exact IntVal_C_mul _ (H j)

theorem P_IntVal1 (N r : ℕ) : IntVal 1 (C (lcmUpTo (12 * N) : ℚ) * Spoly N r) := by
  obtain ⟨k, hk⟩ := lcmUpTo_mono (show 8 * N ≤ 12 * N by omega)
  have := IntVal_C_mul (k : ℤ) (Sm_IntVal (11 * N) _ _ (DD_g_IntVal N r))
  rw [Int.cast_natCast, ← mul_assoc, ← C_mul, mul_comm (k : ℚ), ← Nat.cast_mul, ← hk] at this
  rwa [Spoly_eq]

theorem P_deg (N r : ℕ) (hN : 1 ≤ N) : (C (lcmUpTo (12 * N) : ℚ) * Spoly N r).natDegree < 13 * N + r := by
  have hb : ∀ u : ℕ, binomPoly ℚ (u : ℚ) (8 * N) ≠ 0 := fun u h => by
    have := binom_natDegree_Q (u : ℚ) (8 * N)
    rw [h, natDegree_zero] at this
    omega
  have hF0 : Fpoly N ≠ 0 := mul_ne_zero (mul_ne_zero (hb _) (hb _)) (hb _)
  have hF : (Fpoly N).natDegree = 24 * N := by
    rw [Fpoly, natDegree_mul (mul_ne_zero (hb _) (hb _)) (hb _), natDegree_mul (hb _) (hb _),
      binom_natDegree_Q, binom_natDegree_Q, binom_natDegree_Q]
    omega
  have hg : (X ^ r * Fpoly N).natDegree = r + 24 * N := by
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hF0, natDegree_X_pow, hF]
  have := Sm_natDegree (11 * N) _ (show 11 * N < (X ^ r * Fpoly N).natDegree by omega)
  rw [hg] at this
  exact (natDegree_C_mul_le _ _).trans_lt (by rw [Spoly_eq]; omega)

theorem neg_ediv' (A p : ℤ) (hp : 0 < p) : (-A - 1) / p = -(A / p) - 1 := by
  have e := Int.emod_def A p
  have h1 := Int.emod_nonneg A hp.ne'
  have h2 := Int.emod_lt_of_pos A hp
  apply qexact _ _ _ hp <;> rw [sub_mul, neg_mul, one_mul, mul_comm] <;> omega

theorem binom_eval_neg (u N b t : ℕ) :
    (binomPoly ℚ ((u * N : ℕ) : ℚ) b).eval (-(t : ℚ)) =
      (IP ((u : ℤ) * N + -(t : ℤ)) b : ℚ) / (b.factorial : ℚ) := by
  rw [binomPoly, eval_mul, eval_C, eval_comp, eval_add, eval_X, eval_C,
    show -(t : ℚ) + ((u * N : ℕ) : ℚ) = (((u : ℤ) * N + -(t : ℤ) : ℤ) : ℚ) by push_cast; ring,
    desc_eval_int, inv_mul_eq_div]

theorem pInt_of_eq {p k : ℕ} {q1 q2 : ℚ} (e : q1 = q2) (h : pInt p k q2) : pInt p k q1 := e ▸ h

theorem pieceA (N r p t : ℕ) (pp : p.Prime) (hN : 1 ≤ N) (hp2 : 50 * N < p ^ 2) (hp : p ≤ 11 * N)
    (ht1 : 1 ≤ t) (ht : t ≤ 13 * N + 2) :
    pInt p (phi ((N : ℝ) / p)).toNat ((lcmUpTo (12 * N) : ℚ) * ((X ^ r * Fpoly N).eval (-(t : ℚ)) *
      ((-1) ^ (11 * N) * ((11 * N).factorial : ℚ) / ∏ j ∈ range (11 * N + 1), (-(t : ℚ) - j)))) := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast pp.pos
  have hpz := pz_prime pp
  have hP0 : IP (-(t : ℤ)) (11 * N + 1) ≠ 0 := prod_ne_zero_iff.2 fun i _ => by omega
  have hfQ : ((8 * N).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hPQ : (IP (-(t : ℤ)) (11 * N + 1) : ℚ) ≠ 0 := Int.cast_ne_zero.2 hP0
  refine pInt_of_eq (q2 := (((lcmUpTo (12 * N) : ℤ) * (-(t : ℤ)) ^ r * (-1) ^ (11 * N) *
      ((11 * N).factorial : ℤ) * (IP (10 * (N : ℤ) + -(t : ℤ)) (8 * N) *
        IP (9 * (N : ℤ) + -(t : ℤ)) (8 * N) * IP (11 * (N : ℤ) + -(t : ℤ)) (8 * N)) : ℤ) : ℚ) /
      ((((8 * N).factorial : ℤ) ^ 3 * IP (-(t : ℤ)) (11 * N + 1) : ℤ) : ℚ)) ?_ ?_
  · have hprod : ∏ j ∈ range (11 * N + 1), (-(t : ℚ) - j) = (IP (-(t : ℤ)) (11 * N + 1) : ℚ) := by
      rw [IP, Int.cast_prod]
      push_cast
      rfl
    rw [eval_mul, eval_pow, eval_X, Fpoly, eval_mul, eval_mul, binom_eval_neg, binom_eval_neg,
      binom_eval_neg, hprod]
    simp only [Nat.cast_ofNat]
    push_cast
    field_simp
  by_cases hz : IP (10 * (N : ℤ) + -(t : ℤ)) (8 * N) * IP (9 * (N : ℤ) + -(t : ℤ)) (8 * N) *
      IP (11 * (N : ℤ) + -(t : ℤ)) (8 * N) = 0
  · rw [hz, mul_zero, Int.cast_zero, zero_div]
    exact pInt_zero pp _
  have h10 : IP (10 * (N : ℤ) + -(t : ℤ)) (8 * N) ≠ 0 := fun h => hz (by rw [h, zero_mul, zero_mul])
  have h9 : IP (9 * (N : ℤ) + -(t : ℤ)) (8 * N) ≠ 0 := fun h => hz (by rw [h, mul_zero, zero_mul])
  have h11 : IP (11 * (N : ℤ) + -(t : ℤ)) (8 * N) ≠ 0 := fun h => hz (by rw [h, mul_zero])
  obtain ⟨wd, hwd⟩ := dvd_lcmUpTo pp.one_lt.le (show p ≤ 12 * N by omega)
  obtain ⟨wm, -, hm⟩ := fact_val pp (11 * N) (by omega)
  obtain ⟨wf, hwf, hf⟩ := fact_val pp (8 * N) (by omega)
  obtain ⟨e0, w0, hw0, he0, ee0⟩ := IP_val pp _ (p ^ 2) le_rfl _ hP0 fun i hi => by
    constructor <;> omega
  obtain ⟨e1, w1, -, he1, ee1⟩ := IP_val pp _ (p ^ 2) le_rfl _ h10 fun i hi => by
    constructor <;> omega
  obtain ⟨e2, w2, -, he2, ee2⟩ := IP_val pp _ (p ^ 2) le_rfl _ h9 fun i hi => by
    constructor <;> omega
  obtain ⟨e3, w3, -, he3, ee3⟩ := IP_val pp _ (p ^ 2) le_rfl _ h11 fun i hi => by
    constructor <;> omega
  refine pInt_frac pp _ _ (1 + 11 * N / p + (e1 + e2 + e3)) (3 * (8 * N / p) + e0) _
    (wd * (-(t : ℤ)) ^ r * (-1) ^ (11 * N) * wm * (w1 * w2 * w3)) (wf ^ 3 * w0)
    (by rw [hwd, hm, he1, he2, he3]; push_cast; ring) (by rw [hf, he0]; ring)
    (fun h => (hpz.dvd_or_dvd h).elim (fun h' => hwf (hpz.dvd_of_dvd_pow h')) hw0) ?_
  have hchi := hp_le_chi N p pp.pos (-(t : ℤ))
  unfold chi chi2 at hchi
  rw [show -(t : ℤ) - ((11 * N + 1 : ℕ) : ℤ) = -(11 * (N : ℤ) + -(-(t : ℤ))) - 1 by push_cast; ring,
    neg_ediv' _ _ hp'] at ee0
  rw [show 10 * (N : ℤ) + -(t : ℤ) - ((8 * N : ℕ) : ℤ) = 2 * N + -(t : ℤ) by push_cast; ring] at ee1
  rw [show 9 * (N : ℤ) + -(t : ℤ) - ((8 * N : ℕ) : ℤ) = N + -(t : ℤ) by push_cast; ring] at ee2
  rw [show 11 * (N : ℤ) + -(t : ℤ) - ((8 * N : ℕ) : ℤ) = 3 * N + -(t : ℤ) by push_cast; ring] at ee3
  have : ((((phi ((N : ℝ) / p)).toNat + (3 * (8 * N / p) + e0) : ℕ)) : ℤ) ≤
      ((1 + 11 * N / p + (e1 + e2 + e3) : ℕ) : ℤ) := by
    push_cast
    omega
  exact_mod_cast this

theorem pieceB (N r p t j : ℕ) (pp : p.Prime) (hN : 1 ≤ N) (hp2 : 50 * N < p ^ 2) (hp : p ≤ 11 * N)
    (ht : t ≤ 13 * N + 2) (hj : j ≤ 11 * N) (htj : 1 ≤ t + j) :
    pInt p (phi ((N : ℝ) / p)).toNat
      ((lcmUpTo (12 * N) : ℚ) * (om (11 * N) j * (X ^ r * Fpoly N).eval (j : ℚ) / (-(t : ℚ) - j))) := by
  have hd : -(t : ℚ) - j = -((t + j : ℕ) : ℚ) := by push_cast; ring
  have e : (lcmUpTo (12 * N) : ℚ) * (om (11 * N) j * (X ^ r * Fpoly N).eval (j : ℚ) / (-(t : ℚ) - j)) =
      -((((lcmUpTo (12 * N) : ℤ) * (j : ℤ) ^ r * cZ N j : ℤ) : ℚ) / ((t + j : ℕ) : ℚ)) := by
    rw [hd, eval_mul, eval_pow, eval_X, div_neg, mul_neg, Int.cast_mul, Int.cast_mul, ← cj_eq, cj, om]
    push_cast
    ring
  rw [e]
  refine pInt_neg (pInt_div_nat pp _ _ (by omega) (by omega) (pInt_of_dvd pp _ ?_))
  rw [pow_succ']
  exact mul_dvd_mul (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.2
    (dvd_lcmUpTo pp.one_lt.le (by omega))) _) (cZ_dvd N p j pp hp2 hj)

theorem P_pInt (N r p t : ℕ) (pp : p.Prime) (hN : 1 ≤ N) (hr : r < 3) (hp2 : 50 * N < p ^ 2)
    (hp : p ≤ 11 * N) (ht1 : 1 ≤ t) (ht : t ≤ 13 * N + r) :
    pInt p (phi ((N : ℝ) / p)).toNat ((C (lcmUpTo (12 * N) : ℚ) * Spoly N r).eval (-(t : ℚ))) := by
  have hs : ∀ j : ℕ, j ≤ 11 * N → -(t : ℚ) ≠ j := fun j _ h => by
    have h0 : ((t + j : ℕ) : ℚ) = 0 := by rw [Nat.cast_add, ← h, add_neg_cancel]
    have := Nat.cast_eq_zero.1 h0
    omega
  rw [eval_mul, eval_C, Spoly_eq, Sm_eval' _ _ _ hs, mul_sub, mul_sum]
  exact pInt_sub pp (pieceA N r p t pp hN hp2 hp ht1 (by omega))
    (pInt_sum pp _ _ fun j hj => pieceB N r p t j pp hN hp2 hp (by omega)
      (by have := mem_range.1 hj; omega) (by omega))

theorem P_IntVal_p (N r p : ℕ) (pp : p.Prime) (hN : 1 ≤ N) (hr : r < 3) (hp2 : 50 * N < p ^ 2) :
    IntVal ((p : ℤ) ^ (phi ((N : ℝ) / p)).toNat) (C (lcmUpTo (12 * N) : ℚ) * Spoly N r) := by
  by_cases hp : 11 * N < p
  · rw [hp_zero N p pp.pos hp, pow_zero]
    exact P_IntVal1 N r
  refine iv _ (13 * N + r) (P_deg N r hN) _ (-((13 * N + r : ℕ) : ℤ)) fun t ht => ?_
  obtain ⟨w, hw⟩ := P_IntVal1 N r (-((13 * N + r - t : ℕ) : ℤ))
  rw [Int.cast_neg, Int.cast_natCast, Int.cast_one, one_mul] at hw
  have := P_pInt N r p (13 * N + r - t) pp hN hr hp2 (by omega) (by omega) (by omega)
  rw [hw] at this
  obtain ⟨c, hc⟩ := dvd_of_pInt pp w this
  refine ⟨c, ?_⟩
  rw [show ((-((13 * N + r : ℕ) : ℤ) : ℤ) : ℚ) + (t : ℚ) = -((13 * N + r - t : ℕ) : ℚ) by
    rw [Nat.cast_sub ht.le]; push_cast; ring, hw, hc, Int.cast_mul]

theorem P_IntVal_G (N r : ℕ) (hN : 1 ≤ N) (hr : r < 3) :
    IntVal (GN N : ℤ) (C (lcmUpTo (12 * N) : ℚ) * Spoly N r) := by
  intro z
  obtain ⟨w, hw⟩ := P_IntVal1 N r z
  rw [Int.cast_one, one_mul] at hw
  obtain ⟨c, hc⟩ := G_dvd N w fun p hp => by
    obtain ⟨pp, hp2, -, -⟩ := mem_Sset hp
    obtain ⟨c, hc⟩ := P_IntVal_p N r p pp hN hr hp2 z
    rw [hw, ← Int.cast_mul, Int.cast_inj] at hc
    exact ⟨c, hc⟩
  exact ⟨c, by rw [hw, hc, Int.cast_mul]⟩

theorem ex_sum {M : ℤ} {ι : Type*} (s : Finset ι) (f : ι → ℚ) (H : ∀ i ∈ s, ∃ w : ℤ, f i = M * w) :
    ∃ w : ℤ, ∑ i ∈ s, f i = M * w := by
  choose! W hW using H
  exact ⟨∑ i ∈ s, W i, by rw [Int.cast_sum, mul_sum]; exact sum_congr rfl hW⟩

theorem J_int (N r : ℕ) (hN : 1 ≤ N) (hr : r < 3) :
    ∃ w : ℤ, (lcmUpTo (13 * N + r) : ℚ) * Jfun (2 * N) (C (lcmUpTo (12 * N) : ℚ) * Spoly N r) =
      (GN N : ℤ) * w := by
  have hG := P_IntVal_G N r hN hr
  rw [Jfun_eq _ _ _ (P_deg N r hN), Jsum, mul_sum]
  refine ex_sum _ _ fun h hh => ?_
  obtain ⟨q, hq⟩ := dvd_lcmUpTo (n := 13 * N + r) (show 1 ≤ h + 1 by omega)
    (by have := mem_range.1 hh; omega)
  rw [dl, mul_sum, mul_sum]
  refine ex_sum _ _ fun i _ => ?_
  obtain ⟨w, hw⟩ := hG ((i : ℤ) - (2 * N : ℕ))
  refine ⟨(-1) ^ h * q * ((-1) ^ (h - i) * (h.choose i : ℤ) * w), ?_⟩
  have hinv : ((h : ℚ) + 1) * ((h : ℚ) + 1)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  rw [show (i : ℚ) + -((2 * N : ℕ) : ℚ) = (((i : ℤ) - (2 * N : ℕ) : ℤ) : ℚ) by push_cast; ring, hw, hq]
  push_cast
  linear_combination ((q : ℚ) * (-1) ^ h * ((-1) ^ (h - i) * (h.choose i : ℚ) * ((GN N : ℚ) * w))) * hinv

theorem X2_int (N r : ℕ) : ∃ w : ℤ, ((lcmUpTo (12 * N) * lcmUpTo (13 * N + r) : ℕ) : ℚ) *
    ∑ j ∈ range (11 * N + 1), (j : ℚ) ^ r * cj N j = (GN N : ℤ) * w := by
  rw [mul_sum]
  refine ex_sum _ _ fun j hj => ?_
  obtain ⟨c, hc⟩ := G_dvd N (cZ N j) fun p hp =>
    cZ_dvd N p j (mem_Sset hp).1 (mem_Sset hp).2.1 (by have := mem_range.1 hj; omega)
  exact ⟨(lcmUpTo (12 * N) * lcmUpTo (13 * N + r) : ℕ) * (j : ℤ) ^ r * c, by
    rw [cj_eq, hc]; push_cast; ring⟩

theorem X1h_int (N r : ℕ) (hN : 1 ≤ N) (hr : r < 3) :
    ∃ w : ℤ, ((lcmUpTo (12 * N) * lcmUpTo (13 * N + r) : ℕ) : ℚ) *
      ∑ j ∈ range (11 * N + 1), (j : ℚ) ^ r * cj N j * harm2 (j + 2 * N) = (GN N : ℤ) * w := by
  rw [mul_sum]
  refine ex_sum _ _ fun j hj => ?_
  rw [harm2, mul_sum, mul_sum]
  refine ex_sum _ _ fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := mem_Icc.1 hk
  obtain ⟨w, hw, c, hc⟩ := harm_term N j k r hN hr (by have := mem_range.1 hj; omega) hk1 hk2
  refine ⟨(j : ℤ) ^ r * c, ?_⟩
  rw [cj_eq, show ((lcmUpTo (12 * N) * lcmUpTo (13 * N + r) : ℕ) : ℚ) *
      ((j : ℚ) ^ r * (cZ N j : ℚ) * (1 / (k : ℚ) ^ 2)) =
      (j : ℚ) ^ r * (((lcmUpTo (12 * N) * lcmUpTo (13 * N + r) : ℕ) : ℚ) * (cZ N j : ℚ) / (k : ℚ) ^ 2) by
    ring, hw, hc]
  push_cast
  ring

theorem baseline_integrality (N : ℕ) (hN : 1 ≤ N) (r : Fin 3) :
    ∃ z : Fin 2 → ℤ, ∀ i,
      ((CN N * lcmUpTo (12 * N) * lcmUpTo (13 * N + r) : ℕ) / (GN N : ℚ)) * readout N i r = z i := by
  have hR := Zeta2FirstThree.readout_formula N r (2 * N) le_rfl (by omega)
  have h0 : (CN N : ℚ) * readout N 0 r = 2 * (∑ j ∈ range (11 * N + 1), (j : ℚ) ^ (r : ℕ) * cj N j *
      harm2 (j + 2 * N) + Jfun (2 * N) (Spoly N r)) := congrFun hR 0
  have h1 : (CN N : ℚ) * readout N 1 r = 2 * ∑ j ∈ range (11 * N + 1), (j : ℚ) ^ (r : ℕ) * cj N j :=
    congrFun hR 1
  have hG : (GN N : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.2 (prod_ne_zero_iff.2 fun p hp => pow_ne_zero _ (mem_Sset hp).1.ne_zero)
  obtain ⟨a, ha⟩ := X1h_int N r hN r.2
  obtain ⟨b, hb⟩ := J_int N r hN r.2
  obtain ⟨c, hc⟩ := X2_int N r
  rw [Jfun_C_mul] at hb
  push_cast at ha hb hc
  refine ⟨![2 * (a + b), 2 * c], Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
  · rw [div_mul_eq_mul_div, div_eq_iff hG]
    show _ = ((2 * (a + b) : ℤ) : ℚ) * _
    push_cast
    linear_combination ((lcmUpTo (12 * N) : ℚ) * lcmUpTo (13 * N + r)) * h0 + 2 * ha + 2 * hb
  · rw [div_mul_eq_mul_div, div_eq_iff hG]
    show _ = ((2 * c : ℤ) : ℚ) * _
    push_cast
    linear_combination ((lcmUpTo (12 * N) : ℚ) * lcmUpTo (13 * N + r)) * h1 + 2 * hc

end Zeta2NextTwo
