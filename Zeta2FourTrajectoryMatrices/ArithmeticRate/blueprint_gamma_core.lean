import Zeta2FourTrajectoryMatrices.Blueprint.defs

open Finset Zeta2Blueprint

noncomputable section

namespace Zeta2GammaCore

/-! ### Thresholds -/

def A (c n : ℤ) (x : ℝ) : ℝ := n + 1 - c * x

theorem A_zero (x : ℝ) : A 0 (-1) x = 0 := by
  simp [A]

theorem A_one (x : ℝ) : A 0 0 x = 1 := by
  simp [A]

theorem A_lt (ck nk cj nj : ℤ) (a b : ℚ) (x : ℝ) (hx1 : (a : ℝ) < x) (hx2 : x < b)
    (h : ((cj - ck : ℤ) : ℚ) * a + ((nk - nj : ℤ) : ℚ) ≤ 0 ∧
      ((cj - ck : ℤ) : ℚ) * b + ((nk - nj : ℤ) : ℚ) ≤ 0 ∧
      (((cj - ck : ℤ) : ℚ) * a + ((nk - nj : ℤ) : ℚ) < 0 ∨
        ((cj - ck : ℤ) : ℚ) * b + ((nk - nj : ℤ) : ℚ) < 0)) :
    A ck nk x < A cj nj x := by
  obtain ⟨h1, h2, h3⟩ := h
  have h1' : ((cj - ck : ℤ) : ℝ) * a + ((nk - nj : ℤ) : ℝ) ≤ 0 := by exact_mod_cast h1
  have h2' : ((cj - ck : ℤ) : ℝ) * b + ((nk - nj : ℤ) : ℝ) ≤ 0 := by exact_mod_cast h2
  have h3' : ((cj - ck : ℤ) : ℝ) * a + ((nk - nj : ℤ) : ℝ) < 0 ∨
      ((cj - ck : ℤ) : ℝ) * b + ((nk - nj : ℤ) : ℝ) < 0 := by exact_mod_cast h3
  unfold A
  rcases lt_trichotomy ((cj - ck : ℤ) : ℝ) 0 with hk | hk | hk
  · have := mul_lt_mul_of_neg_left hx1 hk
    push_cast at this h1' ⊢
    linarith
  · push_cast at hk h3' ⊢
    rcases h3' with h | h <;> nlinarith
  · have := mul_lt_mul_of_pos_left hx2 hk
    push_cast at this h2' ⊢
    linarith

theorem floor_bounds (c n : ℤ) (a b : ℚ) (x : ℝ) (hx1 : (a : ℝ) < x) (hx2 : x < b)
    (h : 0 < c ∧ (n : ℚ) ≤ c * a ∧ (c * b : ℚ) ≤ n + 1) :
    (n : ℝ) ≤ c * x ∧ (c : ℝ) * x < n + 1 := by
  obtain ⟨hc, h1, h2⟩ := h
  have h1' : (n : ℝ) ≤ c * a := by exact_mod_cast h1
  have h2' : (c : ℝ) * b ≤ n + 1 := by exact_mod_cast h2
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have e1 := mul_lt_mul_of_pos_left hx1 hc'
  have e2 := mul_lt_mul_of_pos_left hx2 hc'
  constructor <;> linarith

theorem A_pos (c n : ℤ) (a b : ℚ) (x : ℝ) (hx1 : (a : ℝ) < x) (hx2 : x < b)
    (h : ((c - 0 : ℤ) : ℚ) * a + ((-1 - n : ℤ) : ℚ) ≤ 0 ∧
      ((c - 0 : ℤ) : ℚ) * b + ((-1 - n : ℤ) : ℚ) ≤ 0 ∧
      (((c - 0 : ℤ) : ℚ) * a + ((-1 - n : ℤ) : ℚ) < 0 ∨
        ((c - 0 : ℤ) : ℚ) * b + ((-1 - n : ℤ) : ℚ) < 0)) : 0 < A c n x := by
  have := A_lt 0 (-1) c n a b x hx1 hx2 h
  rwa [A_zero] at this

theorem A_lt_one (c n : ℤ) (a b : ℚ) (x : ℝ) (hx1 : (a : ℝ) < x) (hx2 : x < b)
    (h : ((0 - c : ℤ) : ℚ) * a + ((n - 0 : ℤ) : ℚ) ≤ 0 ∧
      ((0 - c : ℤ) : ℚ) * b + ((n - 0 : ℤ) : ℚ) ≤ 0 ∧
      (((0 - c : ℤ) : ℚ) * a + ((n - 0 : ℤ) : ℚ) < 0 ∨
        ((0 - c : ℤ) : ℚ) * b + ((n - 0 : ℤ) : ℚ) < 0)) : A c n x < 1 := by
  have := A_lt c n 0 0 a b x hx1 hx2 h
  rwa [A_one] at this

theorem s_nonneg (n11 : ℤ) (x : ℝ)
    (h : (n11 : ℝ) ≤ ((11 : ℤ) : ℝ) * x ∧ ((11 : ℤ) : ℝ) * x < n11 + 1) :
    0 ≤ A (-11) (-n11 - 1) x := by
  unfold A
  push_cast at h ⊢
  linarith [h.1]

theorem s_lt_one (n11 : ℤ) (x : ℝ)
    (h : (n11 : ℝ) ≤ ((11 : ℤ) : ℝ) * x ∧ ((11 : ℤ) : ℝ) * x < n11 + 1) :
    A (-11) (-n11 - 1) x < 1 := by
  unfold A
  push_cast at h ⊢
  linarith [h.2]

/-! ### Floors of the linear forms -/

theorem floor_y (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1) : ⌊y⌋ = 0 := by
  rw [Int.floor_eq_iff]
  exact ⟨by simpa using hy0, by simpa using hy1⟩

theorem floor_add_y (c n : ℤ) (x y : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (h : (n : ℝ) ≤ c * x ∧ (c : ℝ) * x < n + 1) :
    ⌊(c : ℝ) * x + y⌋ = n + if A c n x ≤ y then 1 else 0 := by
  split_ifs with hA
  · rw [Int.floor_eq_iff]
    unfold A at hA
    push_cast
    constructor <;> linarith [h.1, h.2]
  · rw [Int.floor_eq_iff]
    unfold A at hA
    push Not at hA
    push_cast
    constructor <;> linarith [h.1, h.2]

theorem floor_sub_y (n : ℤ) (x y : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (h : (n : ℝ) ≤ 11 * x ∧ (11 : ℝ) * x < n + 1) :
    ⌊11 * x - y⌋ = n - if A (-11) (-n - 1) x < y then 1 else 0 := by
  split_ifs with hA
  · rw [Int.floor_eq_iff]
    unfold A at hA
    push_cast at hA ⊢
    constructor <;> linarith [h.1, h.2]
  · rw [Int.floor_eq_iff]
    unfold A at hA
    push Not at hA
    push_cast at hA ⊢
    constructor <;> linarith [h.1, h.2]

/-! ### The decomposition of `ρ` -/

def Ival (x : ℝ) (n11 n10 n9 n2 n1 n3 : ℤ) (y : ℝ) : ℤ :=
  (if A (-11) (-n11 - 1) x < y then 1 else 0) + (if A 10 n10 x ≤ y then 1 else 0) +
    (if A 9 n9 x ≤ y then 1 else 0) + (if A 11 n11 x ≤ y then 1 else 0) -
    (if A 2 n2 x ≤ y then 1 else 0) - (if A 1 n1 x ≤ y then 1 else 0) -
    (if A 3 n3 x ≤ y then 1 else 0)

def Ip (x : ℝ) (n11 n10 n9 n2 n1 n3 : ℤ) : ℤ :=
  1 + (if A 10 n10 x ≤ A (-11) (-n11 - 1) x then 1 else 0) +
    (if A 9 n9 x ≤ A (-11) (-n11 - 1) x then 1 else 0) +
    (if A 11 n11 x ≤ A (-11) (-n11 - 1) x then 1 else 0) -
    (if A 2 n2 x ≤ A (-11) (-n11 - 1) x then 1 else 0) -
    (if A 1 n1 x ≤ A (-11) (-n11 - 1) x then 1 else 0) -
    (if A 3 n3 x ≤ A (-11) (-n11 - 1) x then 1 else 0)

theorem rho_decomp (x : ℝ) (n11 n10 n9 n8 n2 n1 n3 : ℤ)
    (h11 : (n11 : ℝ) ≤ ((11 : ℤ) : ℝ) * x ∧ ((11 : ℤ) : ℝ) * x < n11 + 1)
    (h10 : (n10 : ℝ) ≤ ((10 : ℤ) : ℝ) * x ∧ ((10 : ℤ) : ℝ) * x < n10 + 1)
    (h9 : (n9 : ℝ) ≤ ((9 : ℤ) : ℝ) * x ∧ ((9 : ℤ) : ℝ) * x < n9 + 1)
    (h8 : (n8 : ℝ) ≤ ((8 : ℤ) : ℝ) * x ∧ ((8 : ℤ) : ℝ) * x < n8 + 1)
    (h2 : (n2 : ℝ) ≤ ((2 : ℤ) : ℝ) * x ∧ ((2 : ℤ) : ℝ) * x < n2 + 1)
    (h1 : (n1 : ℝ) ≤ ((1 : ℤ) : ℝ) * x ∧ ((1 : ℤ) : ℝ) * x < n1 + 1)
    (h3 : (n3 : ℝ) ≤ ((3 : ℤ) : ℝ) * x ∧ ((3 : ℤ) : ℝ) * x < n3 + 1)
    (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    rho x y = (n10 + n9 + n11 - 3 * n8 - n2 - n1 - n3) + Ival x n11 n10 n9 n2 n1 n3 y := by
  have e4 := floor_add_y 10 n10 x y hy0 hy1 h10
  have e5 := floor_add_y 9 n9 x y hy0 hy1 h9
  have e6 := floor_add_y 11 n11 x y hy0 hy1 h11
  have e8 := floor_add_y 2 n2 x y hy0 hy1 h2
  have e9 := floor_add_y 1 n1 x y hy0 hy1 h1
  have e10 := floor_add_y 3 n3 x y hy0 hy1 h3
  push_cast at h11 h8
  have e1 : ⌊(11 : ℝ) * x⌋ = n11 := Int.floor_eq_iff.2 h11
  have e2 : ⌊y⌋ = 0 := floor_y y hy0 hy1
  have e3 := floor_sub_y n11 x y hy0 hy1 h11
  have e7 : ⌊(8 : ℝ) * x⌋ = n8 := Int.floor_eq_iff.2 h8
  push_cast at e4 e5 e6 e8 e9 e10
  rw [one_mul] at e9
  rw [rho, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, Ival]
  ring

/-! ### Minimisation over `y` via test points -/

theorem Ival_ge (x : ℝ) (n11 n10 n9 n2 n1 n3 : ℤ) (m : ℤ)
    (h0 : m ≤ Ival x n11 n10 n9 n2 n1 n3 0)
    (h10 : 0 ≤ A 10 n10 x → A 10 n10 x < 1 → m ≤ Ival x n11 n10 n9 n2 n1 n3 (A 10 n10 x))
    (h9 : 0 ≤ A 9 n9 x → A 9 n9 x < 1 → m ≤ Ival x n11 n10 n9 n2 n1 n3 (A 9 n9 x))
    (h11 : 0 ≤ A 11 n11 x → A 11 n11 x < 1 → m ≤ Ival x n11 n10 n9 n2 n1 n3 (A 11 n11 x))
    (h2 : 0 ≤ A 2 n2 x → A 2 n2 x < 1 → m ≤ Ival x n11 n10 n9 n2 n1 n3 (A 2 n2 x))
    (h1 : 0 ≤ A 1 n1 x → A 1 n1 x < 1 → m ≤ Ival x n11 n10 n9 n2 n1 n3 (A 1 n1 x))
    (h3 : 0 ≤ A 3 n3 x → A 3 n3 x < 1 → m ≤ Ival x n11 n10 n9 n2 n1 n3 (A 3 n3 x))
    (hsp : m ≤ Ip x n11 n10 n9 n2 n1 n3) :
    ∀ y, 0 ≤ y → y < 1 → m ≤ Ival x n11 n10 n9 n2 n1 n3 y := by
  intro y hy0 hy1
  classical
  set S : Finset ℝ := {A 10 n10 x, A 9 n9 x, A 11 n11 x, A 2 n2 x, A 1 n1 x, A 3 n3 x} with hS
  set T : Finset ℝ := insert 0 (S.filter fun t => t ≤ y) with hT
  have hT0 : (0 : ℝ) ∈ T := Finset.mem_insert_self _ _
  have hTne : T.Nonempty := ⟨0, hT0⟩
  set τ := T.max' hTne with hτ
  have hτT : τ ∈ T := Finset.max'_mem _ _
  have hτle : ∀ t ∈ T, t ≤ τ := fun t ht => Finset.le_max' _ _ ht
  have hTy : ∀ t ∈ T, t ≤ y := by
    intro t ht
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact hy0
    · exact (Finset.mem_filter.1 ht).2
  have hτy : τ ≤ y := hTy τ hτT
  have hτ0 : 0 ≤ τ := hτle 0 hT0
  have key : ∀ t ∈ S, (t ≤ y ↔ t ≤ τ) := by
    intro t ht
    constructor
    · intro h
      exact hτle t (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨ht, h⟩))
    · intro h
      exact h.trans hτy
  have m10 : A 10 n10 x ∈ S := by simp [hS]
  have m9 : A 9 n9 x ∈ S := by simp [hS]
  have m11 : A 11 n11 x ∈ S := by simp [hS]
  have m2 : A 2 n2 x ∈ S := by simp [hS]
  have m1 : A 1 n1 x ∈ S := by simp [hS]
  have m3 : A 3 n3 x ∈ S := by simp [hS]
  have hval : m ≤ Ival x n11 n10 n9 n2 n1 n3 τ := by
    rcases Finset.mem_insert.1 hτT with h | h
    · rw [h]
      exact h0
    · obtain ⟨hS', hτy'⟩ := Finset.mem_filter.1 h
      have hτ1 : τ < 1 := lt_of_le_of_lt hτy' hy1
      simp only [hS, Finset.mem_insert, Finset.mem_singleton] at hS'
      rcases hS' with h | h | h | h | h | h <;> rw [h] at hτ0 hτ1 ⊢
      · exact h10 hτ0 hτ1
      · exact h9 hτ0 hτ1
      · exact h11 hτ0 hτ1
      · exact h2 hτ0 hτ1
      · exact h1 hτ0 hτ1
      · exact h3 hτ0 hτ1
  by_cases hsy : A (-11) (-n11 - 1) x < y
  · by_cases hsτ : A (-11) (-n11 - 1) x < τ
    · have hI : Ival x n11 n10 n9 n2 n1 n3 y = Ival x n11 n10 n9 n2 n1 n3 τ := by
        simp only [Ival, key _ m10, key _ m9, key _ m11, key _ m2, key _ m1, key _ m3, hsy, hsτ]
      rw [hI]
      exact hval
    · push Not at hsτ
      have key' : ∀ t ∈ S, (t ≤ y ↔ t ≤ A (-11) (-n11 - 1) x) := fun t ht =>
        ⟨fun h => ((key t ht).1 h).trans hsτ, fun h => h.trans hsy.le⟩
      have hI : Ival x n11 n10 n9 n2 n1 n3 y = Ip x n11 n10 n9 n2 n1 n3 := by
        simp only [Ival, Ip, key' _ m10, key' _ m9, key' _ m11, key' _ m2, key' _ m1, key' _ m3,
          hsy, ite_true]
      rw [hI]
      exact hsp
  · have hsτ : ¬ A (-11) (-n11 - 1) x < τ := not_lt.2 (hτy.trans (not_lt.1 hsy))
    have hI : Ival x n11 n10 n9 n2 n1 n3 y = Ival x n11 n10 n9 n2 n1 n3 τ := by
      simp only [Ival, key _ m10, key _ m9, key _ m11, key _ m2, key _ m1, key _ m3, hsy, hsτ]
    rw [hI]
    exact hval

theorem exists_near_s (x : ℝ) (n11 n10 n9 n2 n1 n3 : ℤ)
    (hs0 : 0 ≤ A (-11) (-n11 - 1) x) (hs1 : A (-11) (-n11 - 1) x < 1) :
    ∃ y, 0 ≤ y ∧ y < 1 ∧ Ival x n11 n10 n9 n2 n1 n3 y = Ip x n11 n10 n9 n2 n1 n3 := by
  classical
  set s := A (-11) (-n11 - 1) x with hs
  set S : Finset ℝ := {A 10 n10 x, A 9 n9 x, A 11 n11 x, A 2 n2 x, A 1 n1 x, A 3 n3 x} with hS
  set U : Finset ℝ := insert 1 (S.filter fun t => s < t) with hU
  have hU1 : (1 : ℝ) ∈ U := Finset.mem_insert_self _ _
  have hUne : U.Nonempty := ⟨1, hU1⟩
  set u := U.min' hUne with hu
  have hsu : s < u := by
    rw [hu, Finset.lt_min'_iff]
    intro t ht
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact hs1
    · exact (Finset.mem_filter.1 ht).2
  have hu1 : u ≤ 1 := Finset.min'_le _ _ hU1
  refine ⟨(s + u) / 2, by linarith, by linarith, ?_⟩
  have hy1 : s < (s + u) / 2 := by linarith
  have hy2 : (s + u) / 2 < u := by linarith
  have key : ∀ t ∈ S, (t ≤ (s + u) / 2 ↔ t ≤ s) := by
    intro t ht
    constructor
    · intro h
      by_contra h'
      push Not at h'
      have : u ≤ t := Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨ht, h'⟩))
      linarith
    · intro h
      linarith
  have m10 : A 10 n10 x ∈ S := by simp [hS]
  have m9 : A 9 n9 x ∈ S := by simp [hS]
  have m11 : A 11 n11 x ∈ S := by simp [hS]
  have m2 : A 2 n2 x ∈ S := by simp [hS]
  have m1 : A 1 n1 x ∈ S := by simp [hS]
  have m3 : A 3 n3 x ∈ S := by simp [hS]
  simp only [Ival, Ip, ← hs, key _ m10, key _ m9, key _ m11, key _ m2, key _ m1, key _ m3, hy1,
    ite_true]

/-! ### Elementary properties of `ρ` and `φ` -/

theorem carry_nonneg (u v : ℝ) : 0 ≤ ⌊u + v⌋ - ⌊u⌋ - ⌊v⌋ := by
  have := Int.le_floor_add u v
  omega

theorem carry_le_one (u v : ℝ) : ⌊u + v⌋ - ⌊u⌋ - ⌊v⌋ ≤ 1 := by
  have := Int.le_floor_add_floor u v
  omega

theorem rho_nonneg (x y : ℝ) : 0 ≤ rho x y := by
  have c1 := carry_nonneg (11 * x - y) y
  have c2 := carry_nonneg (8 * x) (2 * x + y)
  have c3 := carry_nonneg (8 * x) (x + y)
  have c4 := carry_nonneg (8 * x) (3 * x + y)
  rw [show 11 * x - y + y = 11 * x by ring] at c1
  rw [show 8 * x + (2 * x + y) = 10 * x + y by ring] at c2
  rw [show 8 * x + (x + y) = 9 * x + y by ring] at c3
  rw [show 8 * x + (3 * x + y) = 11 * x + y by ring] at c4
  rw [rho]
  omega

theorem rho_le_four (x y : ℝ) : rho x y ≤ 4 := by
  have c1 := carry_le_one (11 * x - y) y
  have c2 := carry_le_one (8 * x) (2 * x + y)
  have c3 := carry_le_one (8 * x) (x + y)
  have c4 := carry_le_one (8 * x) (3 * x + y)
  rw [show 11 * x - y + y = 11 * x by ring] at c1
  rw [show 8 * x + (2 * x + y) = 10 * x + y by ring] at c2
  rw [show 8 * x + (x + y) = 9 * x + y by ring] at c3
  rw [show 8 * x + (3 * x + y) = 11 * x + y by ring] at c4
  rw [rho]
  omega

instance : Nonempty (Set.Ico (0 : ℝ) 1) := ⟨⟨0, le_rfl, zero_lt_one⟩⟩

theorem phi_le (x y : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1) : phi x ≤ rho x y := by
  have hb : BddBelow (Set.range fun y : Set.Ico (0 : ℝ) 1 => rho x y) := by
    refine ⟨0, ?_⟩
    rintro z ⟨y', rfl⟩
    exact rho_nonneg _ _
  change (⨅ y : Set.Ico (0 : ℝ) 1, rho x y) ≤ rho x y
  exact ciInf_le hb ⟨y, hy0, hy1⟩

theorem phi_ge (x : ℝ) (m : ℤ) (H : ∀ y, 0 ≤ y → y < 1 → m ≤ rho x y) : m ≤ phi x :=
  le_ciInf fun y => H y y.2.1 y.2.2

theorem phi_nonneg (x : ℝ) : 0 ≤ phi x := phi_ge x 0 fun y _ _ => rho_nonneg x y

theorem phi_le_four (x : ℝ) : phi x ≤ 4 :=
  (phi_le x 0 le_rfl zero_lt_one).trans (rho_le_four x 0)

theorem phi_eq (x : ℝ) (h : ℤ) (hlow : ∀ y, 0 ≤ y → y < 1 → h ≤ rho x y)
    (hup : ∃ y, 0 ≤ y ∧ y < 1 ∧ rho x y ≤ h) : phi x = h := by
  obtain ⟨y, hy0, hy1, hy⟩ := hup
  exact le_antisymm ((phi_le x y hy0 hy1).trans hy) (phi_ge x h hlow)

/-! ### Periodicity -/

theorem rho_add_one (x y : ℝ) : rho (x + 1) y = rho x y := by
  have e1 : ⌊(11 : ℝ) * (x + 1)⌋ = ⌊11 * x⌋ + 11 := by
    rw [show (11 : ℝ) * (x + 1) = 11 * x + 11 by ring, Int.floor_add_ofNat]
  have e2 : ⌊(11 : ℝ) * (x + 1) - y⌋ = ⌊11 * x - y⌋ + 11 := by
    rw [show (11 : ℝ) * (x + 1) - y = 11 * x - y + 11 by ring, Int.floor_add_ofNat]
  have e3 : ⌊(10 : ℝ) * (x + 1) + y⌋ = ⌊10 * x + y⌋ + 10 := by
    rw [show (10 : ℝ) * (x + 1) + y = 10 * x + y + 10 by ring, Int.floor_add_ofNat]
  have e4 : ⌊(9 : ℝ) * (x + 1) + y⌋ = ⌊9 * x + y⌋ + 9 := by
    rw [show (9 : ℝ) * (x + 1) + y = 9 * x + y + 9 by ring, Int.floor_add_ofNat]
  have e5 : ⌊(11 : ℝ) * (x + 1) + y⌋ = ⌊11 * x + y⌋ + 11 := by
    rw [show (11 : ℝ) * (x + 1) + y = 11 * x + y + 11 by ring, Int.floor_add_ofNat]
  have e6 : ⌊(8 : ℝ) * (x + 1)⌋ = ⌊8 * x⌋ + 8 := by
    rw [show (8 : ℝ) * (x + 1) = 8 * x + 8 by ring, Int.floor_add_ofNat]
  have e7 : ⌊(2 : ℝ) * (x + 1) + y⌋ = ⌊2 * x + y⌋ + 2 := by
    rw [show (2 : ℝ) * (x + 1) + y = 2 * x + y + 2 by ring, Int.floor_add_ofNat]
  have e8 : ⌊x + 1 + y⌋ = ⌊x + y⌋ + 1 := by
    rw [show x + 1 + y = x + y + 1 by ring, Int.floor_add_one]
  have e9 : ⌊(3 : ℝ) * (x + 1) + y⌋ = ⌊3 * x + y⌋ + 3 := by
    rw [show (3 : ℝ) * (x + 1) + y = 3 * x + y + 3 by ring, Int.floor_add_ofNat]
  rw [rho, rho, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  ring

theorem phi_add_one (x : ℝ) : phi (x + 1) = phi x := by
  simp only [phi, rho_add_one]

theorem phi_add_nat (x : ℝ) : ∀ k : ℕ, phi (x + k) = phi x
  | 0 => by simp
  | k + 1 => by rw [Nat.cast_succ, ← add_assoc, phi_add_one, phi_add_nat x k]

theorem phi_eq_fract (x : ℝ) (hx : 0 ≤ x) : phi x = phi (Int.fract x) := by
  have h := phi_add_nat (Int.fract x) ⌊x⌋.toNat
  rw [show ((⌊x⌋.toNat : ℕ) : ℝ) = (⌊x⌋ : ℝ) by
    exact_mod_cast Int.toNat_of_nonneg (Int.floor_nonneg.2 hx), Int.fract_add_floor] at h
  exact h

end Zeta2GammaCore
