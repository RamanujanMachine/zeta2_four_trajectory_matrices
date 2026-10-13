import Zeta2FourTrajectoryMatrices.FiniteReadout.blueprint_next_two

open Zeta2Blueprint Zeta2NextTwo

namespace Zeta2ANChamber

attribute [local instance 2000] List.decidableBAll

def Pat (N p k : ℕ) (E : Prop) (l9 l10 l11 : ℕ) (D9 D10 D11 : Prop) : Prop :=
  (11 * N % p < k ↔ E) ∧ (k + 9 * N) / p = l9 ∧ (k + 10 * N) / p = l10 ∧ (k + 11 * N) / p = l11 ∧
    ((k + 9 * N) % p < 8 * N % p ↔ D9) ∧ ((k + 10 * N) % p < 8 * N % p ↔ D10) ∧
    ((k + 11 * N) % p < 8 * N % p ↔ D11)

def Ind (x k P Q : ℕ) : Prop := (x = 0 ∧ k + Q < P) ∨ (x = 1 ∧ P ≤ k + Q)

theorem nq (X p c : ℕ) (h1 : c * p ≤ X) (h2 : X < c * p + p) : X / p = c ∧ X % p + c * p = X := by
  have hq : X / p = c := Nat.div_eq_of_lt_le h1 (by rw [Nat.succ_mul]; exact h2)
  have e := Nat.div_add_mod X p
  rw [hq, Nat.mul_comm] at e
  exact ⟨hq, by omega⟩

theorem ind_div (A p k : ℕ) (hp : 0 < p) (hk : k < p) :
    ∃ t, (k + A) / p = A / p + t ∧ Ind t k (A / p * p + p) A := by
  have e := Nat.div_add_mod A p
  have hm := Nat.mod_lt A hp
  rw [Nat.mul_comm] at e
  rcases Nat.lt_or_ge (k + A) (A / p * p + p) with h | h
  · exact ⟨0, (nq (k + A) p (A / p) (by omega) h).1, Or.inl ⟨rfl, h⟩⟩
  · have q := (nq (k + A) p (A / p + 1) (by rw [Nat.succ_mul]; exact h)
      (by rw [Nat.succ_mul]; omega)).1
    exact ⟨1, q, Or.inr ⟨rfl, h⟩⟩

theorem ind_le {x y k P Q P' Q' : ℕ} (hx : Ind x k P Q) (hy : Ind y k P' Q')
    (h : P + Q' ≤ P' + Q) : y ≤ x := by
  rcases hx with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> rcases hy with ⟨rfl, hy⟩ | ⟨rfl, hy⟩ <;> omega

theorem ind_le2 {x y z k P Q P' Q' P'' Q'' : ℕ} (hx : Ind x k P Q) (hy : Ind y k P' Q')
    (hz : Ind z k P'' Q'') (h : P + Q'' ≤ P'' + Q ∨ P' + Q'' ≤ P'' + Q') : z ≤ x + y := by
  rcases h with h | h
  · exact (ind_le hx hz h).trans (Nat.le_add_right x y)
  · exact (ind_le hy hz h).trans (Nat.le_add_left y x)

theorem ind_one {x k P Q : ℕ} (hx : Ind x k P Q) : x ≤ 1 := by
  rcases hx with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact Nat.zero_le 1
  · exact le_refl 1

theorem ind_val0 {x k P Q : ℕ} (hx : Ind x k P Q) (h : k + Q < P) : x = 0 := by
  rcases hx with ⟨rfl, -⟩ | ⟨-, hx⟩
  · rfl
  · omega

theorem ind_val1 {x k P Q : ℕ} (hx : Ind x k P Q) (h : P ≤ k + Q) : x = 1 := by
  rcases hx with ⟨-, hx⟩ | ⟨rfl, -⟩
  · omega
  · rfl

theorem bitN (P : Prop) [Decidable P] :
    ∃ e : ℕ, (if P then 1 else 0 : ℕ) = e ∧ (P ↔ e = 1) ∧ e ≤ 1 := by
  by_cases h : P
  · exact ⟨1, ite_eq_left h, iff_of_true h rfl, le_refl 1⟩
  · exact ⟨0, ite_eq_right h, iff_of_false h zero_ne_one, Nat.zero_le 1⟩

theorem skel (N p k : ℕ) (hp : 0 < p) (hk : k < p) : ∃ e d9 d10 d11 : ℕ,
    chi N p k = ((e + d9 + d10 + d11 : ℕ) : ℤ) ∧ (11 * N % p < k ↔ e = 1) ∧
    ((k + 9 * N) % p < 8 * N % p ↔ d9 = 1) ∧ ((k + 10 * N) % p < 8 * N % p ↔ d10 = 1) ∧
    ((k + 11 * N) % p < 8 * N % p ↔ d11 = 1) ∧ Ind e k (11 * N + 1) (11 * N / p * p) ∧
    (k + 9 * N) / p = (k + N) / p + 8 * N / p + d9 ∧
    (k + 10 * N) / p = (k + 2 * N) / p + 8 * N / p + d10 ∧
    (k + 11 * N) / p = (k + 3 * N) / p + 8 * N / p + d11 ∧ d9 ≤ 1 ∧ d10 ≤ 1 ∧ d11 ≤ 1 := by
  obtain ⟨d9, e9, i9, f9⟩ := bitN ((k + 9 * N) % p < 8 * N % p)
  obtain ⟨d10, e10, i10, f10⟩ := bitN ((k + 10 * N) % p < 8 * N % p)
  obtain ⟨d11, e11, i11, f11⟩ := bitN ((k + 11 * N) % p < 8 * N % p)
  have c9 := carry_nat (k + N) (8 * N) p hp
  have c10 := carry_nat (k + 2 * N) (8 * N) p hp
  have c11 := carry_nat (k + 3 * N) (8 * N) p hp
  rw [show k + N + 8 * N = k + 9 * N by omega, e9] at c9
  rw [show k + 2 * N + 8 * N = k + 10 * N by omega, e10] at c10
  rw [show k + 3 * N + 8 * N = k + 11 * N by omega, e11] at c11
  have hc := chi_id N p k hp hk
  have hd := Nat.div_add_mod (11 * N) p
  rw [Nat.mul_comm] at hd
  rw [e9, e10, e11] at hc
  by_cases h : 11 * N % p < k
  · rw [ite_eq_left h] at hc
    refine ⟨1, d9, d10, d11, ?_, iff_of_true h rfl, i9, i10, i11, Or.inr ⟨rfl, by omega⟩, c9,
      c10, c11,
      f9, f10, f11⟩
    rw [hc, Nat.cast_add, Nat.cast_add, Nat.cast_add, Nat.cast_one]
  · rw [ite_eq_right h] at hc
    refine ⟨0, d9, d10, d11, ?_, iff_of_false h zero_ne_one, i9, i10, i11,
      Or.inl ⟨rfl, by omega⟩, c9, c10, c11, f9, f10, f11⟩
    rw [hc, Nat.cast_add, Nat.cast_add, Nat.cast_add, Nat.cast_zero]

theorem phi_val (N p h0 k0 : ℕ) (hp : 0 < p) (hw : chi N p k0 = h0)
    (hlb : ∀ k : ℤ, 0 ≤ k → k < p → (h0 : ℤ) ≤ chi N p k) :
    ((phi ((N : ℝ) / p)).toNat : ℤ) = h0 := by
  rw [le_antisymm (hw ▸ phi_le_chi N p hp k0) (phi_ge N p hp h0 hlb), Int.toNat_natCast]

theorem comb (N p k k' h0 : ℕ) {E : Prop} {l9 l10 l11 : ℕ} {D9 D10 D11 : Prop}
    (hd : ∀ j, j < p → chi N p j = (h0 : ℤ) → Pat N p j E l9 l10 l11 D9 D10 D11)
    (hphi : ((phi ((N : ℝ) / p)).toNat : ℤ) = h0) (hk : k < p) (hk' : k' < p)
    (hχ : chi N p k = ((phi ((N : ℝ) / p)).toNat : ℤ))
    (hχ' : chi N p k' = ((phi ((N : ℝ) / p)).toNat : ℤ)) :
    (11 * N % p < k ↔ 11 * N % p < k') ∧
      ∀ u ∈ ({9, 10, 11} : Finset ℕ), (k + u * N) / p = (k' + u * N) / p ∧
        ((k + u * N) % p < 8 * N % p ↔ (k' + u * N) % p < 8 * N % p) := by
  obtain ⟨e, q9, q10, q11, r9, r10, r11⟩ := hd k hk (hχ.trans hphi)
  obtain ⟨e', q9', q10', q11', r9', r10', r11'⟩ := hd k' hk' (hχ'.trans hphi)
  refine ⟨e.trans e'.symm, fun u hu => ?_⟩
  rcases Finset.mem_insert.1 hu with rfl | hu
  · exact ⟨q9.trans q9'.symm, r9.trans r9'.symm⟩
  rcases Finset.mem_insert.1 hu with rfl | hu
  · exact ⟨q10.trans q10'.symm, r10.trans r10'.symm⟩
  rcases Finset.mem_singleton.1 hu with rfl
  exact ⟨q11.trans q11'.symm, r11.trans r11'.symm⟩

theorem excl (N p c : ℕ) (pp : p.Prime) (hN : 1 ≤ N) (hp2 : 50 * N < p ^ 2) (hc : c = 5 ∨ c = 10)
    (h : 11 * N = c * p) : False := by
  have hc3 : 3 ≤ c := by rcases hc with rfl | rfl <;> omega
  replace hc : c ≤ 10 := by rcases hc with rfl | rfl <;> omega
  have hdv : p ∣ 11 * N := ⟨c, by rw [h, Nat.mul_comm]⟩
  rcases (Nat.Prime.dvd_mul pp).1 hdv with h11 | hNd
  · have := (Nat.prime_dvd_prime_iff_eq pp Nat.prime_eleven).1 h11
    subst this
    omega
  · have h1 := Nat.le_of_dvd (by omega) hNd
    have h2 := Nat.mul_le_mul_right p hc
    omega

theorem vfin70 {z1 z2 z3 z4 z5 z6 z7 : ℕ} (W : z1 + z2 + z3 + z4 + z5 + z6 + z7 + 0 ≤ 0) :
    z1 = 0 ∧ z2 = 0 ∧ z3 = 0 ∧ z4 = 0 ∧ z5 = 0 ∧ z6 = 0 ∧ z7 = 0 := by
  omega

theorem vfin61 {z1 z2 z3 z4 z5 z6 o1 : ℕ} (h1 : o1 ≤ 1) (W : z1 + z2 + z3 + z4 + z5 + z6 + 1 ≤ o1) :
    z1 = 0 ∧ z2 = 0 ∧ z3 = 0 ∧ z4 = 0 ∧ z5 = 0 ∧ z6 = 0 ∧ o1 = 1 := by
  omega

theorem vfin52 {z1 z2 z3 z4 z5 o1 o2 : ℕ} (h1 : o1 ≤ 1) (h2 : o2 ≤ 1)
    (W : z1 + z2 + z3 + z4 + z5 + 2 ≤ o1 + o2) :
    z1 = 0 ∧ z2 = 0 ∧ z3 = 0 ∧ z4 = 0 ∧ z5 = 0 ∧ o1 = 1 ∧ o2 = 1 := by
  omega

theorem vfin43 {z1 z2 z3 z4 o1 o2 o3 : ℕ} (h1 : o1 ≤ 1) (h2 : o2 ≤ 1) (h3 : o3 ≤ 1)
    (W : z1 + z2 + z3 + z4 + 3 ≤ o1 + o2 + o3) :
    z1 = 0 ∧ z2 = 0 ∧ z3 = 0 ∧ z4 = 0 ∧ o1 = 1 ∧ o2 = 1 ∧ o3 = 1 := by
  omega

theorem klt {k c K p : ℕ} (hk0 : k + c = K) (h : K < p + c) : k < p := by
  omega

theorem ind_val0' {x k P Q c K : ℕ} (hx : Ind x k P Q) (hk0 : k + c = K) (h : K + Q < P + c) :
    x = 0 :=
  ind_val0 hx (by omega)

theorem ind_val1' {x k P Q c K : ℕ} (hx : Ind x k P Q) (hk0 : k + c = K) (h : P + c ≤ K + Q) :
    x = 1 :=
  ind_val1 hx (by omega)

def BB (N p a c9 c10 c11 s2 s3 : ℕ) : Prop :=
  a * p ≤ 8 * N ∧ 8 * N < a * p + p ∧ c9 * p ≤ 9 * N ∧ 9 * N < c9 * p + p ∧
    c10 * p ≤ 10 * N ∧ 10 * N < c10 * p + p ∧ c11 * p ≤ 11 * N ∧ 11 * N < c11 * p + p ∧
    0 * p ≤ N ∧ N < 0 * p + p ∧ s2 * p ≤ 2 * N ∧ 2 * N < s2 * p + p ∧
    s3 * p ≤ 3 * N ∧ 3 * N < s3 * p + p

theorem setupG (N p k a c9 c10 c11 s2 s3 : ℕ) (hp : 0 < p) (hk : k < p)
    (hB : BB N p a c9 c10 c11 s2 s3) {G : Prop}
    (H : ∀ e d9 d10 d11 t9 t10 t11 v1 v2 v3 : ℕ, chi N p k = ((e + d9 + d10 + d11 : ℕ) : ℤ) →
      (11 * N % p < k ↔ e = 1) → ((k + 9 * N) % p < 8 * N % p ↔ d9 = 1) →
      ((k + 10 * N) % p < 8 * N % p ↔ d10 = 1) → ((k + 11 * N) % p < 8 * N % p ↔ d11 = 1) →
      Ind e k (11 * N + 1) (c11 * p) → Ind t9 k (c9 * p + p) (9 * N) →
      Ind t10 k (c10 * p + p) (10 * N) → Ind t11 k (c11 * p + p) (11 * N) →
      Ind v1 k (0 * p + p) N → Ind v2 k (s2 * p + p) (2 * N) → Ind v3 k (s3 * p + p) (3 * N) →
      c9 + t9 = 0 + v1 + a + d9 → c10 + t10 = s2 + v2 + a + d10 →
      c11 + t11 = s3 + v3 + a + d11 → (k + 9 * N) / p = c9 + t9 → (k + 10 * N) / p = c10 + t10 →
      (k + 11 * N) / p = c11 + t11 → d9 ≤ 1 → d10 ≤ 1 → d11 ≤ 1 → G) : G := by
  unfold BB at hB
  obtain ⟨B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14⟩ := hB
  obtain ⟨e, d9, d10, d11, hc, he, h9, h10, h11, Ie, C9, C10, C11, F9, F10, F11⟩ := skel N p k hp hk
  obtain ⟨t9, L9, I9⟩ := ind_div (9 * N) p k hp hk
  obtain ⟨t10, L10, I10⟩ := ind_div (10 * N) p k hp hk
  obtain ⟨t11, L11, I11⟩ := ind_div (11 * N) p k hp hk
  obtain ⟨v1, M1, J1⟩ := ind_div N p k hp hk
  obtain ⟨v2, M2, J2⟩ := ind_div (2 * N) p k hp hk
  obtain ⟨v3, M3, J3⟩ := ind_div (3 * N) p k hp hk
  rw [(nq _ p _ B1 B2).1] at C9 C10 C11
  rw [(nq _ p _ B3 B4).1] at L9 I9
  rw [(nq _ p _ B5 B6).1] at L10 I10
  rw [(nq _ p _ B7 B8).1] at L11 I11 Ie
  rw [(nq _ p _ B9 B10).1] at M1 J1
  rw [(nq _ p _ B11 B12).1] at M2 J2
  rw [(nq _ p _ B13 B14).1] at M3 J3
  rw [L9, M1] at C9
  rw [L10, M2] at C10
  rw [L11, M3] at C11
  exact H e d9 d10 d11 t9 t10 t11 v1 v2 v3 hc he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 C9 C10 C11 L9 L10
    L11 F9 F10 F11

theorem c1 (N p : ℕ) (h1 : 13 * N < 2 * p) (h2 : p < 8 * N) :
    (∀ k, k < p → chi N p k = ((0 : ℕ) : ℤ) →
      Pat N p k False 1 1 1 False False False) ∧
      chi N p ((0 : ℕ) : ℤ) = ((0 : ℕ) : ℤ) := by
  obtain ⟨hp, hB, ⟨R1, R2, R3, R4, R5, R6⟩, hk0, V1, V2, V3, V4, V5, V6, V7⟩ :
      0 < p ∧ BB N p 1 1 1 1 0 0 ∧ (1 * p + p + N ≤ 0 * p + p + 9 * N ∧
          1 * p + p + 2 * N ≤ 0 * p + p + 10 * N ∧ 1 * p + p + 3 * N ≤ 0 * p + p + 11 * N ∧
          11 * N + 1 + 2 * N ≤ 0 * p + p + 1 * p ∧ 0 * p + p + N ≤ 0 * p + p + 2 * N ∧
          (11 * N + 1 + 3 * N ≤ 0 * p + p + 1 * p ∨ 1 * p + p + 3 * N ≤ 0 * p + p + 10 * N)) ∧
          0 < p ∧ 0 + 1 * p < 11 * N + 1 ∧ 0 + 9 * N < 1 * p + p ∧ 0 + 10 * N < 1 * p + p ∧
          0 + 11 * N < 1 * p + p ∧ 0 + N < 0 * p + p ∧ 0 + 2 * N < 0 * p + p ∧
          0 + 3 * N < 0 * p + p := by
    unfold BB
    omega
  refine ⟨fun k hk hχ => ?_, ?_⟩
  · clear V1 V2 V3 V4 V5 V6 V7
    refine setupG N p k 1 1 1 1 0 0 hp hk hB fun e d9 d10 d11 t9 t10 t11 v1 v2
      v3 hc he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 C9 C10 C11 L9 L10 L11 F9 F10 F11 => ?_
    rw [hχ, Nat.cast_inj] at hc
    have Z1 := ind_le I9 J1 R1
    have Z2 := ind_le I10 J2 R2
    have Z3 := ind_le I11 J3 R3
    have Z4 := ind_le Ie J2 R4
    have Z5 := ind_le J2 J1 R5
    have Z6 := ind_le2 Ie I10 J3 R6
    have OIe := ind_one Ie
    have OI9 := ind_one I9
    have OI10 := ind_one I10
    have OI11 := ind_one I11
    have OJ1 := ind_one J1
    have OJ2 := ind_one J2
    have OJ3 := ind_one J3
    have W : e + t9 + t10 + t11 + d9 + d10 + d11 + 0 ≤ 0 := by
      clear hχ he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 hk hp L9 L10 L11 hB h1 h2 R1 R2 R3 R4 R5 R6 F9
      clear F10 F11 OIe OI9 OI10 OI11 OJ1 OJ2 OJ3
      omega
    obtain ⟨Ve, Vt9, Vt10, Vt11, Vd9, Vd10, Vd11⟩ := vfin70 W
    exact ⟨he.trans (iff_of_false (by rw [Ve]; exact zero_ne_one) id), by rw [L9, Vt9], by rw [L10,
        Vt10], by rw [L11, Vt11],
      h9.trans (iff_of_false (by rw [Vd9]; exact zero_ne_one) id),
      h10.trans (iff_of_false (by rw [Vd10]; exact zero_ne_one) id),
      h11.trans (iff_of_false (by rw [Vd11]; exact zero_ne_one) id)⟩
  · clear R1 R2 R3 R4 R5 R6
    refine setupG N p 0 1 1 1 1 0 0 hp hp hB fun e d9 d10 d11 t9 t10 t11 v1 v2
      v3 hc he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 C9 C10 C11 L9 L10 L11 F9 F10 F11 => ?_
    have Z1 := ind_val0 Ie V1
    have Z2 := ind_val0 I9 V2
    have Z3 := ind_val0 I10 V3
    have Z4 := ind_val0 I11 V4
    have Z5 := ind_val0 J1 V5
    have Z6 := ind_val0 J2 V6
    have Z7 := ind_val0 J3 V7
    have V : e + d9 + d10 + d11 = 0 := by
      clear he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 hc V1 V2 V3 V4 V5 V6 V7 L9 L10 L11 hB h1 h2 hp
      omega
    rw [hc, V]

theorem c2 (N p : ℕ) (h1 : 13 * N < 3 * p) (h2 : 2 * p < 9 * N) :
    (∀ k, k < p → chi N p k = ((2 : ℕ) : ℤ) →
      Pat N p k False 2 2 2 True True False) ∧
      chi N p ((p - 3 * N : ℕ) : ℤ) = ((2 : ℕ) : ℤ) := by
  obtain ⟨hp, hB, ⟨R1, R2, R3, R4⟩, hle, hkK, V1, V2, V3, V4, V5, V6, V7⟩ :
      0 < p ∧ BB N p 1 2 2 2 0 0 ∧ (11 * N + 1 + 2 * N ≤ 0 * p + p + 2 * p ∧
          2 * p + p + N ≤ 0 * p + p + 10 * N ∧ 2 * p + p + 2 * N ≤ 0 * p + p + 11 * N ∧
          0 * p + p + 10 * N ≤ 2 * p + p + 2 * N) ∧ 3 * N ≤ p ∧ p < p + 3 * N ∧
          p + 2 * p < 11 * N + 1 + 3 * N ∧ p + 9 * N < 2 * p + p + 3 * N ∧
          p + 10 * N < 2 * p + p + 3 * N ∧ p + 11 * N < 2 * p + p + 3 * N ∧
          p + N < 0 * p + p + 3 * N ∧ p + 2 * N < 0 * p + p + 3 * N ∧
          0 * p + p + 3 * N ≤ p + 3 * N := by
    unfold BB
    omega
  refine ⟨fun k hk hχ => ?_, ?_⟩
  · clear V1 V2 V3 V4 V5 V6 V7 hle hkK
    refine setupG N p k 1 2 2 2 0 0 hp hk hB fun e d9 d10 d11 t9 t10 t11 v1 v2
      v3 hc he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 C9 C10 C11 L9 L10 L11 F9 F10 F11 => ?_
    rw [hχ, Nat.cast_inj] at hc
    have Z1 := ind_le Ie J2 R1
    have Z2 := ind_le I10 J1 R2
    have Z3 := ind_le I11 J2 R3
    have Z4 := ind_le J2 I10 R4
    have OIe := ind_one Ie
    have OI9 := ind_one I9
    have OI10 := ind_one I10
    have OI11 := ind_one I11
    have OJ1 := ind_one J1
    have OJ2 := ind_one J2
    have OJ3 := ind_one J3
    have W : e + t9 + t10 + t11 + d11 + 2 ≤ d9 + d10 := by
      clear hχ he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 hk hp L9 L10 L11 hB h1 h2 R1 R2 R3 R4 F9 F10 F11
      clear OIe OI9 OI10 OI11 OJ1 OJ2
      omega
    obtain ⟨Ve, Vt9, Vt10, Vt11, Vd11, Vd9, Vd10⟩ := vfin52 F9 F10 W
    exact ⟨he.trans (iff_of_false (by rw [Ve]; exact zero_ne_one) id), by rw [L9, Vt9], by rw [L10,
        Vt10], by rw [L11, Vt11],
      h9.trans (iff_of_true Vd9 trivial),
      h10.trans (iff_of_true Vd10 trivial),
      h11.trans (iff_of_false (by rw [Vd11]; exact zero_ne_one) id)⟩
  · clear R1 R2 R3 R4
    have hk0 := Nat.sub_add_cancel hle
    generalize p - 3 * N = k at hk0 ⊢
    have hk := klt hk0 hkK
    refine setupG N p k 1 2 2 2 0 0 hp hk hB fun e d9 d10 d11 t9 t10 t11 v1 v2
      v3 hc he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 C9 C10 C11 L9 L10 L11 F9 F10 F11 => ?_
    have Z1 := ind_val0' Ie hk0 V1
    have Z2 := ind_val0' I9 hk0 V2
    have Z3 := ind_val0' I10 hk0 V3
    have Z4 := ind_val0' I11 hk0 V4
    have Z5 := ind_val0' J1 hk0 V5
    have Z6 := ind_val0' J2 hk0 V6
    have Z7 := ind_val1' J3 hk0 V7
    have V : e + d9 + d10 + d11 = 2 := by
      clear he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 hc V1 V2 V3 V4 V5 V6 V7 L9 L10 L11 hB h1 h2 hk hp
      clear hk0 hle hkK
      omega
    rw [hc, V]

theorem c3 (N p : ℕ) (h1 : 13 * N < 4 * p) (h2 : 3 * p < 10 * N) :
    (∀ k, k < p → chi N p k = ((1 : ℕ) : ℤ) →
      Pat N p k False 2 3 3 False True False) ∧
      chi N p ((p - 3 * N : ℕ) : ℤ) = ((1 : ℕ) : ℤ) := by
  obtain ⟨hp, hB, ⟨R1, R2, R3, R4⟩, hle, hkK, V1, V2, V3, V4, V5, V6, V7⟩ :
      0 < p ∧ BB N p 2 2 3 3 0 0 ∧ (11 * N + 1 + 2 * N ≤ 0 * p + p + 3 * p ∧
          3 * p + p + N ≤ 0 * p + p + 11 * N ∧ 2 * p + p + 3 * p ≤ 11 * N + 1 + 9 * N ∧
          0 * p + p + 11 * N ≤ 3 * p + p + 2 * N) ∧ 3 * N ≤ p ∧ p < p + 3 * N ∧
          p + 3 * p < 11 * N + 1 + 3 * N ∧ p + 9 * N < 2 * p + p + 3 * N ∧
          p + 10 * N < 3 * p + p + 3 * N ∧ p + 11 * N < 3 * p + p + 3 * N ∧
          p + N < 0 * p + p + 3 * N ∧ p + 2 * N < 0 * p + p + 3 * N ∧
          0 * p + p + 3 * N ≤ p + 3 * N := by
    unfold BB
    omega
  refine ⟨fun k hk hχ => ?_, ?_⟩
  · clear V1 V2 V3 V4 V5 V6 V7 hle hkK
    refine setupG N p k 2 2 3 3 0 0 hp hk hB fun e d9 d10 d11 t9 t10 t11 v1 v2
      v3 hc he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 C9 C10 C11 L9 L10 L11 F9 F10 F11 => ?_
    rw [hχ, Nat.cast_inj] at hc
    have Z1 := ind_le Ie J2 R1
    have Z2 := ind_le I11 J1 R2
    have Z3 := ind_le I9 Ie R3
    have Z4 := ind_le J2 I11 R4
    have OIe := ind_one Ie
    have OI9 := ind_one I9
    have OI10 := ind_one I10
    have OI11 := ind_one I11
    have OJ1 := ind_one J1
    have OJ2 := ind_one J2
    have OJ3 := ind_one J3
    have W : e + t9 + t10 + t11 + d9 + d11 + 1 ≤ d10 := by
      clear hχ he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 hk hp L9 L10 L11 hB h1 h2 R1 R2 R3 R4 F9 F10 F11
      clear OIe OI9 OI10 OI11 OJ1 OJ2
      omega
    obtain ⟨Ve, Vt9, Vt10, Vt11, Vd9, Vd11, Vd10⟩ := vfin61 F10 W
    exact ⟨he.trans (iff_of_false (by rw [Ve]; exact zero_ne_one) id), by rw [L9, Vt9], by rw [L10,
        Vt10], by rw [L11, Vt11],
      h9.trans (iff_of_false (by rw [Vd9]; exact zero_ne_one) id),
      h10.trans (iff_of_true Vd10 trivial),
      h11.trans (iff_of_false (by rw [Vd11]; exact zero_ne_one) id)⟩
  · clear R1 R2 R3 R4
    have hk0 := Nat.sub_add_cancel hle
    generalize p - 3 * N = k at hk0 ⊢
    have hk := klt hk0 hkK
    refine setupG N p k 2 2 3 3 0 0 hp hk hB fun e d9 d10 d11 t9 t10 t11 v1 v2
      v3 hc he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 C9 C10 C11 L9 L10 L11 F9 F10 F11 => ?_
    have Z1 := ind_val0' Ie hk0 V1
    have Z2 := ind_val0' I9 hk0 V2
    have Z3 := ind_val0' I10 hk0 V3
    have Z4 := ind_val0' I11 hk0 V4
    have Z5 := ind_val0' J1 hk0 V5
    have Z6 := ind_val0' J2 hk0 V6
    have Z7 := ind_val1' J3 hk0 V7
    have V : e + d9 + d10 + d11 = 1 := by
      clear he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 hc V1 V2 V3 V4 V5 V6 V7 L9 L10 L11 hB h1 h2 hk hp
      clear hk0 hle hkK
      omega
    rw [hc, V]

theorem c4 (N p : ℕ) (h1 : 13 * N < 5 * p) (h2 : 3 * p < 8 * N) :
    (∀ k, k < p → chi N p k = ((0 : ℕ) : ℤ) →
      Pat N p k False 3 3 4 False False False) ∧
      chi N p ((0 : ℕ) : ℤ) = ((0 : ℕ) : ℤ) := by
  obtain ⟨hp, hB, ⟨R1, R2, R3, R4, R5, R6⟩, hk0, V1, V2, V3, V4, V5, V6, V7⟩ :
      0 < p ∧ BB N p 3 3 3 4 0 1 ∧ (3 * p + p + N ≤ 0 * p + p + 9 * N ∧
          3 * p + p + 2 * N ≤ 0 * p + p + 10 * N ∧ 4 * p + p + 3 * N ≤ 1 * p + p + 11 * N ∧
          11 * N + 1 + 2 * N ≤ 0 * p + p + 4 * p ∧ 0 * p + p + 9 * N ≤ 3 * p + p + 2 * N ∧
          0 * p + p + 11 * N ≤ 4 * p + p + N) ∧ 0 < p ∧ 0 + 4 * p < 11 * N + 1 ∧
          0 + 9 * N < 3 * p + p ∧ 0 + 10 * N < 3 * p + p ∧ 0 + 11 * N < 4 * p + p ∧
          0 + N < 0 * p + p ∧ 0 + 2 * N < 0 * p + p ∧ 0 + 3 * N < 1 * p + p := by
    unfold BB
    omega
  refine ⟨fun k hk hχ => ?_, ?_⟩
  · clear V1 V2 V3 V4 V5 V6 V7
    refine setupG N p k 3 3 3 4 0 1 hp hk hB fun e d9 d10 d11 t9 t10 t11 v1 v2
      v3 hc he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 C9 C10 C11 L9 L10 L11 F9 F10 F11 => ?_
    rw [hχ, Nat.cast_inj] at hc
    have Z1 := ind_le I9 J1 R1
    have Z2 := ind_le I10 J2 R2
    have Z3 := ind_le I11 J3 R3
    have Z4 := ind_le Ie J2 R4
    have Z5 := ind_le J2 I9 R5
    have Z6 := ind_le J1 I11 R6
    have OIe := ind_one Ie
    have OI9 := ind_one I9
    have OI10 := ind_one I10
    have OI11 := ind_one I11
    have OJ1 := ind_one J1
    have OJ2 := ind_one J2
    have OJ3 := ind_one J3
    have W : e + t9 + t10 + t11 + d9 + d10 + d11 + 0 ≤ 0 := by
      clear hχ he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 hk hp L9 L10 L11 hB h1 h2 R1 R2 R3 R4 R5 R6 F9
      clear F10 F11 OIe OI9 OI10 OI11 OJ1 OJ2 OJ3
      omega
    obtain ⟨Ve, Vt9, Vt10, Vt11, Vd9, Vd10, Vd11⟩ := vfin70 W
    exact ⟨he.trans (iff_of_false (by rw [Ve]; exact zero_ne_one) id), by rw [L9, Vt9], by rw [L10,
        Vt10], by rw [L11, Vt11],
      h9.trans (iff_of_false (by rw [Vd9]; exact zero_ne_one) id),
      h10.trans (iff_of_false (by rw [Vd10]; exact zero_ne_one) id),
      h11.trans (iff_of_false (by rw [Vd11]; exact zero_ne_one) id)⟩
  · clear R1 R2 R3 R4 R5 R6
    refine setupG N p 0 3 3 3 4 0 1 hp hp hB fun e d9 d10 d11 t9 t10 t11 v1 v2
      v3 hc he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 C9 C10 C11 L9 L10 L11 F9 F10 F11 => ?_
    have Z1 := ind_val0 Ie V1
    have Z2 := ind_val0 I9 V2
    have Z3 := ind_val0 I10 V3
    have Z4 := ind_val0 I11 V4
    have Z5 := ind_val0 J1 V5
    have Z6 := ind_val0 J2 V6
    have Z7 := ind_val0 J3 V7
    have V : e + d9 + d10 + d11 = 0 := by
      clear he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 hc V1 V2 V3 V4 V5 V6 V7 L9 L10 L11 hB h1 h2 hp
      omega
    rw [hc, V]

theorem c5 (N p : ℕ) (h1 : 13 * N < 6 * p) (h2 : 4 * p < 9 * N) (h3 : 11 * N < 5 * p) :
    (∀ k, k < p → chi N p k = ((1 : ℕ) : ℤ) →
      Pat N p k False 4 5 5 False True False) ∧
      chi N p ((2 * p - 3 * N : ℕ) : ℤ) = ((1 : ℕ) : ℤ) := by
  obtain ⟨hp, hB, ⟨R1, R2, R3, R4⟩, hle, hkK, V1, V2, V3, V4, V5, V6, V7⟩ :
      0 < p ∧ BB N p 3 4 4 4 0 1 ∧ (4 * p + p + N ≤ 0 * p + p + 10 * N ∧
          4 * p + p + 2 * N ≤ 0 * p + p + 11 * N ∧ 0 * p + p + 3 * N ≤ 1 * p + p + N ∧
          0 * p + p + 10 * N ≤ 4 * p + p + 2 * N) ∧ 3 * N ≤ 2 * p ∧ 2 * p < p + 3 * N ∧
          2 * p + 4 * p < 11 * N + 1 + 3 * N ∧ 2 * p + 9 * N < 4 * p + p + 3 * N ∧
          4 * p + p + 3 * N ≤ 2 * p + 10 * N ∧ 4 * p + p + 3 * N ≤ 2 * p + 11 * N ∧
          0 * p + p + 3 * N ≤ 2 * p + N ∧ 0 * p + p + 3 * N ≤ 2 * p + 2 * N ∧
          1 * p + p + 3 * N ≤ 2 * p + 3 * N := by
    unfold BB
    omega
  refine ⟨fun k hk hχ => ?_, ?_⟩
  · clear V1 V2 V3 V4 V5 V6 V7 hle hkK
    refine setupG N p k 3 4 4 4 0 1 hp hk hB fun e d9 d10 d11 t9 t10 t11 v1 v2
      v3 hc he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 C9 C10 C11 L9 L10 L11 F9 F10 F11 => ?_
    rw [hχ, Nat.cast_inj] at hc
    have Z1 := ind_le I10 J1 R1
    have Z2 := ind_le I11 J2 R2
    have Z3 := ind_le J1 J3 R3
    have Z4 := ind_le J2 I10 R4
    have OIe := ind_one Ie
    have OI9 := ind_one I9
    have OI10 := ind_one I10
    have OI11 := ind_one I11
    have OJ1 := ind_one J1
    have OJ2 := ind_one J2
    have OJ3 := ind_one J3
    have W : e + t9 + d9 + d11 + 3 ≤ t10 + t11 + d10 := by
      clear hχ he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 hk hp L9 L10 L11 hB h1 h2 h3 R1 R2 R3 R4 F9 F10
      clear F11 OIe OI9 OI10 OI11
      omega
    obtain ⟨Ve, Vt9, Vd9, Vd11, Vt10, Vt11, Vd10⟩ := vfin43 OI10 OI11 F10 W
    exact ⟨he.trans (iff_of_false (by rw [Ve]; exact zero_ne_one) id), by rw [L9, Vt9], by rw [L10,
        Vt10], by rw [L11, Vt11],
      h9.trans (iff_of_false (by rw [Vd9]; exact zero_ne_one) id),
      h10.trans (iff_of_true Vd10 trivial),
      h11.trans (iff_of_false (by rw [Vd11]; exact zero_ne_one) id)⟩
  · clear R1 R2 R3 R4
    have hk0 := Nat.sub_add_cancel hle
    generalize 2 * p - 3 * N = k at hk0 ⊢
    have hk := klt hk0 hkK
    refine setupG N p k 3 4 4 4 0 1 hp hk hB fun e d9 d10 d11 t9 t10 t11 v1 v2
      v3 hc he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 C9 C10 C11 L9 L10 L11 F9 F10 F11 => ?_
    have Z1 := ind_val0' Ie hk0 V1
    have Z2 := ind_val0' I9 hk0 V2
    have Z3 := ind_val1' I10 hk0 V3
    have Z4 := ind_val1' I11 hk0 V4
    have Z5 := ind_val1' J1 hk0 V5
    have Z6 := ind_val1' J2 hk0 V6
    have Z7 := ind_val1' J3 hk0 V7
    have V : e + d9 + d10 + d11 = 1 := by
      clear he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 hc V1 V2 V3 V4 V5 V6 V7 L9 L10 L11 hB h1 h2 h3 hk
      clear hp hk0 hle hkK
      omega
    rw [hc, V]

theorem c6 (N p : ℕ) (h1 : 13 * N < 6 * p) (h2 : 4 * p < 9 * N) (h3 : 5 * p < 11 * N) :
    (∀ k, k < p → chi N p k = ((2 : ℕ) : ℤ) →
      Pat N p k True 4 5 5 False True False) ∧
      chi N p ((2 * p - 3 * N : ℕ) : ℤ) = ((2 : ℕ) : ℤ) := by
  obtain ⟨hp, hB, ⟨R1, R2, R3, R4⟩, hle, hkK, V1, V2, V3, V4, V5, V6, V7⟩ :
      0 < p ∧ BB N p 3 4 4 5 0 1 ∧ (11 * N + 1 + 2 * N ≤ 0 * p + p + 5 * p ∧
          4 * p + p + N ≤ 0 * p + p + 10 * N ∧ 0 * p + p + 3 * N ≤ 1 * p + p + N ∧
          0 * p + p + 10 * N ≤ 4 * p + p + 2 * N) ∧ 3 * N ≤ 2 * p ∧ 2 * p < p + 3 * N ∧
          11 * N + 1 + 3 * N ≤ 2 * p + 5 * p ∧ 2 * p + 9 * N < 4 * p + p + 3 * N ∧
          4 * p + p + 3 * N ≤ 2 * p + 10 * N ∧ 2 * p + 11 * N < 5 * p + p + 3 * N ∧
          0 * p + p + 3 * N ≤ 2 * p + N ∧ 0 * p + p + 3 * N ≤ 2 * p + 2 * N ∧
          1 * p + p + 3 * N ≤ 2 * p + 3 * N := by
    unfold BB
    omega
  refine ⟨fun k hk hχ => ?_, ?_⟩
  · clear V1 V2 V3 V4 V5 V6 V7 hle hkK
    refine setupG N p k 3 4 4 5 0 1 hp hk hB fun e d9 d10 d11 t9 t10 t11 v1 v2
      v3 hc he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 C9 C10 C11 L9 L10 L11 F9 F10 F11 => ?_
    rw [hχ, Nat.cast_inj] at hc
    have Z1 := ind_le Ie J2 R1
    have Z2 := ind_le I10 J1 R2
    have Z3 := ind_le J1 J3 R3
    have Z4 := ind_le J2 I10 R4
    have OIe := ind_one Ie
    have OI9 := ind_one I9
    have OI10 := ind_one I10
    have OI11 := ind_one I11
    have OJ1 := ind_one J1
    have OJ2 := ind_one J2
    have OJ3 := ind_one J3
    have W : t9 + t11 + d9 + d11 + 3 ≤ e + t10 + d10 := by
      clear hχ he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 hk hp L9 L10 L11 hB h1 h2 h3 R1 R2 R3 R4 F9 F10
      clear F11 OI9 OI10 OI11
      omega
    obtain ⟨Vt9, Vt11, Vd9, Vd11, Ve, Vt10, Vd10⟩ := vfin43 OIe OI10 F10 W
    exact ⟨he.trans (iff_of_true Ve trivial), by rw [L9, Vt9], by rw [L10, Vt10], by rw [L11, Vt11],
      h9.trans (iff_of_false (by rw [Vd9]; exact zero_ne_one) id),
      h10.trans (iff_of_true Vd10 trivial),
      h11.trans (iff_of_false (by rw [Vd11]; exact zero_ne_one) id)⟩
  · clear R1 R2 R3 R4
    have hk0 := Nat.sub_add_cancel hle
    generalize 2 * p - 3 * N = k at hk0 ⊢
    have hk := klt hk0 hkK
    refine setupG N p k 3 4 4 5 0 1 hp hk hB fun e d9 d10 d11 t9 t10 t11 v1 v2
      v3 hc he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 C9 C10 C11 L9 L10 L11 F9 F10 F11 => ?_
    have Z1 := ind_val1' Ie hk0 V1
    have Z2 := ind_val0' I9 hk0 V2
    have Z3 := ind_val1' I10 hk0 V3
    have Z4 := ind_val0' I11 hk0 V4
    have Z5 := ind_val1' J1 hk0 V5
    have Z6 := ind_val1' J2 hk0 V6
    have Z7 := ind_val1' J3 hk0 V7
    have V : e + d9 + d10 + d11 = 2 := by
      clear he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 hc V1 V2 V3 V4 V5 V6 V7 L9 L10 L11 hB h1 h2 h3 hk
      clear hp hk0 hle hkK
      omega
    rw [hc, V]

theorem c7 (N p : ℕ) (h1 : 13 * N < 12 * p) (h2 : 8 * p < 9 * N) (h3 : 11 * N < 10 * p)
    (h4 : 10 * N < 9 * p) :
    (∀ k, k < p → chi N p k = ((0 : ℕ) : ℤ) →
      Pat N p k False 8 9 10 False False False) ∧
      chi N p ((3 * p - 3 * N : ℕ) : ℤ) = ((0 : ℕ) : ℤ) := by
  obtain ⟨hp, hB, ⟨R1, R2, R3, R4⟩, hle, hkK, V1, V2, V3, V4, V5, V6, V7⟩ :
      0 < p ∧ BB N p 7 8 8 9 1 2 ∧ (8 * p + p + 2 * N ≤ 1 * p + p + 10 * N ∧
          9 * p + p + 3 * N ≤ 2 * p + p + 11 * N ∧ 8 * p + p + N ≤ 0 * p + p + 10 * N ∧
          9 * p + p + 2 * N ≤ 1 * p + p + 11 * N) ∧ 3 * N ≤ 3 * p ∧ 3 * p < p + 3 * N ∧
          3 * p + 9 * p < 11 * N + 1 + 3 * N ∧ 3 * p + 9 * N < 8 * p + p + 3 * N ∧
          8 * p + p + 3 * N ≤ 3 * p + 10 * N ∧ 9 * p + p + 3 * N ≤ 3 * p + 11 * N ∧
          0 * p + p + 3 * N ≤ 3 * p + N ∧ 1 * p + p + 3 * N ≤ 3 * p + 2 * N ∧
          2 * p + p + 3 * N ≤ 3 * p + 3 * N := by
    unfold BB
    omega
  refine ⟨fun k hk hχ => ?_, ?_⟩
  · clear V1 V2 V3 V4 V5 V6 V7 hle hkK
    refine setupG N p k 7 8 8 9 1 2 hp hk hB fun e d9 d10 d11 t9 t10 t11 v1 v2
      v3 hc he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 C9 C10 C11 L9 L10 L11 F9 F10 F11 => ?_
    rw [hχ, Nat.cast_inj] at hc
    have Z1 := ind_le I10 J2 R1
    have Z2 := ind_le I11 J3 R2
    have Z3 := ind_le I10 J1 R3
    have Z4 := ind_le I11 J2 R4
    have OIe := ind_one Ie
    have OI9 := ind_one I9
    have OI10 := ind_one I10
    have OI11 := ind_one I11
    have OJ1 := ind_one J1
    have OJ2 := ind_one J2
    have OJ3 := ind_one J3
    have W : e + t9 + d9 + d10 + d11 + 2 ≤ t10 + t11 := by
      clear hχ he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 hk hp L9 L10 L11 hB h1 h2 h3 h4 R1 R2 R3 R4 F9
      clear F10 F11 OIe OI9 OJ2 OJ3
      omega
    obtain ⟨Ve, Vt9, Vd9, Vd10, Vd11, Vt10, Vt11⟩ := vfin52 OI10 OI11 W
    exact ⟨he.trans (iff_of_false (by rw [Ve]; exact zero_ne_one) id), by rw [L9, Vt9], by rw [L10,
        Vt10], by rw [L11, Vt11],
      h9.trans (iff_of_false (by rw [Vd9]; exact zero_ne_one) id),
      h10.trans (iff_of_false (by rw [Vd10]; exact zero_ne_one) id),
      h11.trans (iff_of_false (by rw [Vd11]; exact zero_ne_one) id)⟩
  · clear R1 R2 R3 R4
    have hk0 := Nat.sub_add_cancel hle
    generalize 3 * p - 3 * N = k at hk0 ⊢
    have hk := klt hk0 hkK
    refine setupG N p k 7 8 8 9 1 2 hp hk hB fun e d9 d10 d11 t9 t10 t11 v1 v2
      v3 hc he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 C9 C10 C11 L9 L10 L11 F9 F10 F11 => ?_
    have Z1 := ind_val0' Ie hk0 V1
    have Z2 := ind_val0' I9 hk0 V2
    have Z3 := ind_val1' I10 hk0 V3
    have Z4 := ind_val1' I11 hk0 V4
    have Z5 := ind_val1' J1 hk0 V5
    have Z6 := ind_val1' J2 hk0 V6
    have Z7 := ind_val1' J3 hk0 V7
    have V : e + d9 + d10 + d11 = 0 := by
      clear he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 hc V1 V2 V3 V4 V5 V6 V7 L9 L10 L11 hB h1 h2 h3 h4
      clear hk hp hk0 hle hkK
      omega
    rw [hc, V]

theorem c7b (N p : ℕ) (h1 : 13 * N < 12 * p) (h2 : 8 * p < 9 * N) (h3 : 11 * N < 10 * p)
    (h4 : 9 * p ≤ 10 * N) :
    (∀ k, k < p → chi N p k = ((0 : ℕ) : ℤ) →
      Pat N p k False 8 9 10 False False False) ∧
      chi N p ((3 * p - 3 * N : ℕ) : ℤ) = ((0 : ℕ) : ℤ) := by
  obtain ⟨hp, hB, ⟨R1, R2⟩, hle, hkK, V1, V2, V3, V4, V5, V6, V7⟩ :
      0 < p ∧ BB N p 7 8 9 9 1 2 ∧ (9 * p + p + 3 * N ≤ 2 * p + p + 11 * N ∧
          9 * p + p + N ≤ 0 * p + p + 11 * N) ∧ 3 * N ≤ 3 * p ∧ 3 * p < p + 3 * N ∧
          3 * p + 9 * p < 11 * N + 1 + 3 * N ∧ 3 * p + 9 * N < 8 * p + p + 3 * N ∧
          3 * p + 10 * N < 9 * p + p + 3 * N ∧ 9 * p + p + 3 * N ≤ 3 * p + 11 * N ∧
          0 * p + p + 3 * N ≤ 3 * p + N ∧ 1 * p + p + 3 * N ≤ 3 * p + 2 * N ∧
          2 * p + p + 3 * N ≤ 3 * p + 3 * N := by
    unfold BB
    omega
  refine ⟨fun k hk hχ => ?_, ?_⟩
  · clear V1 V2 V3 V4 V5 V6 V7 hle hkK
    refine setupG N p k 7 8 9 9 1 2 hp hk hB fun e d9 d10 d11 t9 t10 t11 v1 v2
      v3 hc he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 C9 C10 C11 L9 L10 L11 F9 F10 F11 => ?_
    rw [hχ, Nat.cast_inj] at hc
    have Z1 := ind_le I11 J3 R1
    have Z2 := ind_le I11 J1 R2
    have OIe := ind_one Ie
    have OI9 := ind_one I9
    have OI10 := ind_one I10
    have OI11 := ind_one I11
    have OJ1 := ind_one J1
    have OJ2 := ind_one J2
    have OJ3 := ind_one J3
    have W : e + t9 + t10 + d9 + d10 + d11 + 1 ≤ t11 := by
      clear hχ he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 hk hp L9 L10 L11 hB h1 h2 h3 h4 R1 R2 F9 F10 F11
      clear OIe OI9 OI10 OJ3
      omega
    obtain ⟨Ve, Vt9, Vt10, Vd9, Vd10, Vd11, Vt11⟩ := vfin61 OI11 W
    exact ⟨he.trans (iff_of_false (by rw [Ve]; exact zero_ne_one) id), by rw [L9, Vt9], by rw [L10,
        Vt10], by rw [L11, Vt11],
      h9.trans (iff_of_false (by rw [Vd9]; exact zero_ne_one) id),
      h10.trans (iff_of_false (by rw [Vd10]; exact zero_ne_one) id),
      h11.trans (iff_of_false (by rw [Vd11]; exact zero_ne_one) id)⟩
  · clear R1 R2
    have hk0 := Nat.sub_add_cancel hle
    generalize 3 * p - 3 * N = k at hk0 ⊢
    have hk := klt hk0 hkK
    refine setupG N p k 7 8 9 9 1 2 hp hk hB fun e d9 d10 d11 t9 t10 t11 v1 v2
      v3 hc he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 C9 C10 C11 L9 L10 L11 F9 F10 F11 => ?_
    have Z1 := ind_val0' Ie hk0 V1
    have Z2 := ind_val0' I9 hk0 V2
    have Z3 := ind_val0' I10 hk0 V3
    have Z4 := ind_val1' I11 hk0 V4
    have Z5 := ind_val1' J1 hk0 V5
    have Z6 := ind_val1' J2 hk0 V6
    have Z7 := ind_val1' J3 hk0 V7
    have V : e + d9 + d10 + d11 = 0 := by
      clear he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 hc V1 V2 V3 V4 V5 V6 V7 L9 L10 L11 hB h1 h2 h3 h4
      clear hk hp hk0 hle hkK
      omega
    rw [hc, V]

theorem c8 (N p : ℕ) (h1 : 13 * N < 12 * p) (h2 : 8 * p < 9 * N) (h3 : 10 * p < 11 * N) :
    (∀ k, k < p → chi N p k = ((1 : ℕ) : ℤ) →
      Pat N p k True 8 9 10 False False False) ∧
      chi N p ((3 * p - 3 * N : ℕ) : ℤ) = ((1 : ℕ) : ℤ) := by
  obtain ⟨hp, hB, ⟨R1, R2⟩, hle, hkK, V1, V2, V3, V4, V5, V6, V7⟩ :
      0 < p ∧ BB N p 7 8 9 10 1 2 ∧ (11 * N + 1 + 2 * N ≤ 1 * p + p + 10 * p ∧
          1 * p + p + 3 * N ≤ 2 * p + p + 2 * N) ∧ 3 * N ≤ 3 * p ∧ 3 * p < p + 3 * N ∧
          11 * N + 1 + 3 * N ≤ 3 * p + 10 * p ∧ 3 * p + 9 * N < 8 * p + p + 3 * N ∧
          3 * p + 10 * N < 9 * p + p + 3 * N ∧ 3 * p + 11 * N < 10 * p + p + 3 * N ∧
          0 * p + p + 3 * N ≤ 3 * p + N ∧ 1 * p + p + 3 * N ≤ 3 * p + 2 * N ∧
          2 * p + p + 3 * N ≤ 3 * p + 3 * N := by
    unfold BB
    omega
  refine ⟨fun k hk hχ => ?_, ?_⟩
  · clear V1 V2 V3 V4 V5 V6 V7 hle hkK
    refine setupG N p k 7 8 9 10 1 2 hp hk hB fun e d9 d10 d11 t9 t10 t11 v1 v2
      v3 hc he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 C9 C10 C11 L9 L10 L11 F9 F10 F11 => ?_
    rw [hχ, Nat.cast_inj] at hc
    have Z1 := ind_le Ie J2 R1
    have Z2 := ind_le J2 J3 R2
    have OIe := ind_one Ie
    have OI9 := ind_one I9
    have OI10 := ind_one I10
    have OI11 := ind_one I11
    have OJ1 := ind_one J1
    have OJ2 := ind_one J2
    have OJ3 := ind_one J3
    have W : t9 + t10 + t11 + d9 + d10 + d11 + 1 ≤ e := by
      clear hχ he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 hk hp L9 L10 L11 hB h1 h2 h3 R1 R2 F9 F10 F11
      clear OI9 OI10 OI11
      omega
    obtain ⟨Vt9, Vt10, Vt11, Vd9, Vd10, Vd11, Ve⟩ := vfin61 OIe W
    exact ⟨he.trans (iff_of_true Ve trivial), by rw [L9, Vt9], by rw [L10, Vt10], by rw [L11, Vt11],
      h9.trans (iff_of_false (by rw [Vd9]; exact zero_ne_one) id),
      h10.trans (iff_of_false (by rw [Vd10]; exact zero_ne_one) id),
      h11.trans (iff_of_false (by rw [Vd11]; exact zero_ne_one) id)⟩
  · clear R1 R2
    have hk0 := Nat.sub_add_cancel hle
    generalize 3 * p - 3 * N = k at hk0 ⊢
    have hk := klt hk0 hkK
    refine setupG N p k 7 8 9 10 1 2 hp hk hB fun e d9 d10 d11 t9 t10 t11 v1 v2
      v3 hc he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 C9 C10 C11 L9 L10 L11 F9 F10 F11 => ?_
    have Z1 := ind_val1' Ie hk0 V1
    have Z2 := ind_val0' I9 hk0 V2
    have Z3 := ind_val0' I10 hk0 V3
    have Z4 := ind_val0' I11 hk0 V4
    have Z5 := ind_val1' J1 hk0 V5
    have Z6 := ind_val1' J2 hk0 V6
    have Z7 := ind_val1' J3 hk0 V7
    have V : e + d9 + d10 + d11 = 1 := by
      clear he h9 h10 h11 Ie I9 I10 I11 J1 J2 J3 hc V1 V2 V3 V4 V5 V6 V7 L9 L10 L11 hB h1 h2 h3 hk
      clear hp hk0 hle hkK
      omega
    rw [hc, V]

theorem lt_of_add {a r b : ℕ} (h : a + r < b) : a < b := lt_of_le_of_lt (Nat.le_add_right a r) h

theorem chamber_table_core (N r p : ℕ) (hN : 1 ≤ N) (_hr : r < 3)
    (hs : p < 8 * N ∧ p.Prime ∧ 50 * N < p ^ 2 ∧ InShell N r p)
    (k k' : ℕ) (hk : k < p) (hk' : k' < p)
    (hχ : chi N p k = ((phi ((N : ℝ) / p)).toNat : ℤ))
    (hχ' : chi N p k' = ((phi ((N : ℝ) / p)).toNat : ℤ)) :
    (11 * N % p < k ↔ 11 * N % p < k') ∧
      ∀ u ∈ ({9, 10, 11} : Finset ℕ), (k + u * N) / p = (k' + u * N) / p ∧
        ((k + u * N) % p < 8 * N % p ↔ (k' + u * N) % p < 8 * N % p) := by
  obtain ⟨-, pp, hp2, hsh⟩ := hs
  have hp : 0 < p := pp.pos
  have key : ∃ (h0 : ℕ) (E : Prop) (l9 l10 l11 : ℕ) (D9 D10 D11 : Prop),
      ((phi ((N : ℝ) / p)).toNat : ℤ) = h0 ∧
        ∀ j, j < p → chi N p j = (h0 : ℤ) → Pat N p j E l9 l10 l11 D9 D10 D11 := by
    clear hχ hχ' hk hk'
    have nn : ∀ j : ℤ, 0 ≤ j → j < p → ((0 : ℕ) : ℤ) ≤ chi N p j :=
      fun j _ _ => chi_nonneg N p hp j
    rcases hsh with ⟨s1, s2⟩ | ⟨s1, s2⟩ | ⟨s1, s2⟩ | ⟨s1, s2⟩ | ⟨s1, s2⟩ | ⟨s1, s2⟩
    · have c := c1 N p (lt_of_add s1) s2
      exact ⟨0, _, _, _, _, _, _, _, phi_val N p 0 0 hp c.2 nn, c.1⟩
    · have s := lt_of_add s1
      have c := c2 N p s s2
      exact ⟨2, _, _, _, _, _, _, _, phi_val N p 2 _ hp c.2 fun j h0 hj => chi_S3 N p j s s2 h0 hj,
        c.1⟩
    · have s := lt_of_add s1
      have c := c3 N p s s2
      exact ⟨1, _, _, _, _, _, _, _, phi_val N p 1 _ hp c.2 fun j h0 hj => chi_S4 N p j s s2 h0 hj,
        c.1⟩
    · have c := c4 N p (lt_of_add s1) s2
      exact ⟨0, _, _, _, _, _, _, _, phi_val N p 0 0 hp c.2 nn, c.1⟩
    · have s := lt_of_add s1
      rcases Nat.lt_trichotomy (11 * N) (5 * p) with h5 | h5 | h5
      · have c := c5 N p s s2 h5
        exact ⟨1, _, _, _, _, _, _, _, phi_val N p 1 _ hp c.2
          fun j h0 hj => chi_S6a N p j s s2 h5 h0 hj, c.1⟩
      · exact (excl N p 5 pp hN hp2 (Or.inl rfl) h5).elim
      · have c := c6 N p s s2 h5
        exact ⟨2, _, _, _, _, _, _, _, phi_val N p 2 _ hp c.2
          fun j h0 hj => chi_S6b N p j s s2 h5 h0 hj, c.1⟩
    · have s := lt_of_add s1
      rcases Nat.lt_trichotomy (11 * N) (10 * p) with h5 | h5 | h5
      · rcases Nat.lt_or_ge (10 * N) (9 * p) with h6 | h6
        · have c := c7 N p s s2 h5 h6
          exact ⟨0, _, _, _, _, _, _, _, phi_val N p 0 _ hp c.2 nn, c.1⟩
        · have c := c7b N p s s2 h5 h6
          exact ⟨0, _, _, _, _, _, _, _, phi_val N p 0 _ hp c.2 nn, c.1⟩
      · exact (excl N p 10 pp hN hp2 (Or.inr rfl) h5).elim
      · have c := c8 N p s s2 h5
        exact ⟨1, _, _, _, _, _, _, _, phi_val N p 1 _ hp c.2
          fun j h0 hj => chi_S12 N p j s s2 h5 h0 hj, c.1⟩
  obtain ⟨h0, E, l9, l10, l11, D9, D10, D11, hphi, hd⟩ := key
  exact comb N p k k' h0 hd hphi hk hk' hχ hχ'

end Zeta2ANChamber
