import Zeta2FourTrajectoryMatrices.Blueprint.defs

open Polynomial Finset Zeta2Blueprint
open scoped Matrix

noncomputable section

namespace Zeta2FirstThree

theorem toy_conservation :
    toyPot 0 0 = 1 ∧ toyPot 1 0 = toyA ∧ toyPot 0 1 = toyB ∧
    toyPot 1 0 * toyC = toyPot 1 1 ∧ toyPot 0 1 * toyD = toyPot 1 1 ∧
    toyPot 1 1 = (6 : ℚ) • 1 ∧ toyA * toyB ≠ toyB * toyA := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.one_fin_two]
    norm_num [toyPot]
  · norm_num [toyPot, toyA]
  · norm_num [toyPot, toyB]
  · norm_num [toyPot, toyC, Matrix.mul_fin_two]
  · norm_num [toyPot, toyD, Matrix.mul_fin_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [toyPot]
  · rw [toyA, toyB, Matrix.mul_fin_two, Matrix.mul_fin_two]
    intro h
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ => M 0 0) h
    norm_num at this

def Apol (w : Vertex) : ℚ[X] := X * ∏ i : Fin 3, (X + C ((w (.inr i) : ℚ) - 1))

def Dpol (w : Vertex) : ℚ[X] := ∏ i : Fin 4, (X + C (w (.inl i) : ℚ))

theorem Qw_eq (w : Vertex) : Qw w = Apol w - Dpol w := rfl

def a3 (w : Vertex) : ℚ := (Qw w).coeff 3

theorem prodXC_monic {n : ℕ} (a : Fin n → ℚ) : (∏ i, (X + C (a i))).Monic :=
  monic_prod_of_monic _ _ fun i _ => monic_X_add_C (a i)

theorem prodXC_natDegree {n : ℕ} (a : Fin n → ℚ) : (∏ i, (X + C (a i))).natDegree = n := by
  rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_add_C (a i)]
  simp only [natDegree_X_add_C, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

theorem prodXC_coeff_top {n : ℕ} (a : Fin n → ℚ) : (∏ i, (X + C (a i))).coeff n = 1 := by
  have h := (prodXC_monic a).coeff_natDegree
  rwa [prodXC_natDegree] at h

theorem prodXC_coeff_pred {n : ℕ} (a : Fin (n + 1) → ℚ) :
    (∏ i, (X + C (a i))).coeff n = ∑ i, a i := by
  have h1 := Monic.nextCoeff_prod univ (fun i => X + C (a i)) fun i _ => monic_X_add_C (a i)
  rw [nextCoeff_of_natDegree_pos (by rw [prodXC_natDegree]; omega), prodXC_natDegree] at h1
  rw [Nat.add_sub_cancel] at h1
  rw [h1]
  exact sum_congr rfl fun i _ => nextCoeff_X_add_C (a i)

theorem Apol_natDegree (w : Vertex) : (Apol w).natDegree ≤ 4 := by
  unfold Apol
  refine (natDegree_mul_le).trans ?_
  rw [natDegree_X, prodXC_natDegree]

theorem Apol_coeff4 (w : Vertex) : (Apol w).coeff 4 = 1 := by
  unfold Apol
  rw [coeff_X_mul]
  exact prodXC_coeff_top (fun i : Fin 3 => (w (.inr i) : ℚ) - 1)

theorem Apol_coeff3 (w : Vertex) : (Apol w).coeff 3 = ∑ i : Fin 3, ((w (.inr i) : ℚ) - 1) := by
  unfold Apol
  rw [coeff_X_mul]
  exact prodXC_coeff_pred (fun i : Fin 3 => (w (.inr i) : ℚ) - 1)

theorem Dpol_natDegree (w : Vertex) : (Dpol w).natDegree ≤ 4 :=
  (prodXC_natDegree (fun i : Fin 4 => (w (.inl i) : ℚ))).le

theorem Dpol_coeff4 (w : Vertex) : (Dpol w).coeff 4 = 1 :=
  prodXC_coeff_top (fun i : Fin 4 => (w (.inl i) : ℚ))

theorem Dpol_coeff3 (w : Vertex) : (Dpol w).coeff 3 = ∑ i : Fin 4, (w (.inl i) : ℚ) :=
  prodXC_coeff_pred (fun i : Fin 4 => (w (.inl i) : ℚ))

theorem Qw_natDegree (w : Vertex) : (Qw w).natDegree ≤ 3 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [Qw_eq, coeff_sub]
  rcases Nat.lt_or_ge N 5 with h | h
  · obtain rfl : N = 4 := by omega
    rw [Apol_coeff4, Dpol_coeff4, sub_self]
  · rw [coeff_eq_zero_of_natDegree_lt ((Apol_natDegree w).trans_lt (by omega)),
      coeff_eq_zero_of_natDegree_lt ((Dpol_natDegree w).trans_lt (by omega)), sub_self]

theorem a3_eq (w : Vertex) :
    a3 w = ∑ i : Fin 3, ((w (.inr i) : ℚ) - 1) - ∑ i : Fin 4, (w (.inl i) : ℚ) := by
  rw [a3, Qw_eq, coeff_sub, Apol_coeff3, Dpol_coeff3]

theorem Qw_expand (w : Vertex) :
    Qw w = C ((Qw w).coeff 0) + C ((Qw w).coeff 1) * X + C ((Qw w).coeff 2) * X ^ 2 +
      C (a3 w) * X ^ 3 := by
  conv_lhs => rw [as_sum_range' (Qw w) 4 (by have := Qw_natDegree w; omega)]
  simp only [sum_range_succ, sum_range_zero, zero_add, ← C_mul_X_pow_eq_monomial, pow_zero,
    mul_one, pow_one, a3]

def Lmap (w : Vertex) : ℚ[X] →ₗ[ℚ] ℚ[X] :=
  LinearMap.mulRight ℚ (Apol w) - (LinearMap.mulRight ℚ (Dpol w)).comp (taylor (1 : ℚ))

theorem Lmap_apply (w : Vertex) (h : ℚ[X]) : Lmap w h = h * Apol w - taylor 1 h * Dpol w := rfl

def polyOf : (Fin 3 → ℚ) →ₗ[ℚ] ℚ[X] :=
  Fintype.linearCombination ℚ (fun j : Fin 3 => (X : ℚ[X]) ^ (j : ℕ))

theorem polyOf_apply (x : Fin 3 → ℚ) : polyOf x = C (x 0) + C (x 1) * X + C (x 2) * X ^ 2 := by
  simp only [polyOf, Fintype.linearCombination_apply, Fin.sum_univ_three, smul_eq_C_mul,
    Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, mul_one, pow_one]

theorem polyOf_coeff_eq (x : Fin 3 → ℚ) (n : ℕ) :
    (polyOf x).coeff n = ∑ i : Fin 3, if n = (i : ℕ) then x i else 0 := by
  rw [polyOf, Fintype.linearCombination_apply, finsetSum_coeff]
  exact sum_congr rfl fun i _ => by rw [coeff_smul, coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero]

theorem polyOf_coeff (x : Fin 3 → ℚ) (j : Fin 3) : (polyOf x).coeff j = x j := by
  rw [polyOf_coeff_eq]
  simp only [Fin.val_inj, sum_ite_eq, mem_univ, ↓reduceIte]

theorem polyOf_coeff_ge (x : Fin 3 → ℚ) (n : ℕ) (hn : 3 ≤ n) : (polyOf x).coeff n = 0 := by
  rw [polyOf_coeff_eq]
  exact sum_eq_zero fun i _ => ite_eq_right_of_eq_false _ _ (eq_false (by have := i.isLt; omega))

theorem taylor_one_coeff (h : ℚ[X]) (n : ℕ) (hn : h.natDegree < n) (m : ℕ) :
    (taylor 1 h).coeff m = ∑ i ∈ range n, h.coeff i * (i.choose m : ℚ) := by
  rw [taylor_apply, comp, eval₂_eq_sum_range' C hn, finsetSum_coeff]
  refine sum_congr rfl fun i _ => ?_
  rw [coeff_C_mul, C_1, coeff_X_add_one_pow]

theorem taylor_sub_self (h : ℚ[X]) (k : ℕ) (hk : h.natDegree ≤ k + 1) :
    (taylor 1 h - h).natDegree ≤ k ∧ (taylor 1 h - h).coeff k = (k + 1) * h.coeff (k + 1) := by
  have hc : ∀ m, (taylor 1 h).coeff m = ∑ i ∈ range (k + 2), h.coeff i * (i.choose m : ℚ) :=
    taylor_one_coeff h (k + 2) (by omega)
  constructor
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeff_sub, hc, sum_range_succ, sum_eq_zero fun i hi => by
      rw [Nat.choose_eq_zero_of_lt (by have := mem_range.1 hi; omega), Nat.cast_zero, mul_zero],
      zero_add]
    rcases Nat.lt_or_ge (k + 1) N with h1 | h1
    · rw [Nat.choose_eq_zero_of_lt h1, coeff_eq_zero_of_natDegree_lt (hk.trans_lt h1), Nat.cast_zero,
        mul_zero, sub_zero]
    · obtain rfl : N = k + 1 := by omega
      rw [Nat.choose_self, Nat.cast_one, mul_one, sub_self]
  · rw [coeff_sub, hc, sum_range_succ, sum_range_succ, sum_eq_zero fun i hi => by
      rw [Nat.choose_eq_zero_of_lt (by have := mem_range.1 hi; omega), Nat.cast_zero, mul_zero],
      Nat.choose_self, Nat.choose_succ_self_right, zero_add, Nat.cast_one, mul_one, Nat.cast_succ]
    ring

theorem Lmap_deg (w : Vertex) (h : ℚ[X]) (k : ℕ) (hk : h.natDegree ≤ k) :
    (Lmap w h).natDegree ≤ k + 3 ∧ (Lmap w h).coeff (k + 3) = h.coeff k * (a3 w - k) := by
  have hL : Lmap w h = h * Qw w - (taylor 1 h - h) * Dpol w := by
    rw [Lmap_apply, Qw_eq, mul_sub, sub_mul, sub_sub_sub_cancel_right]
  rcases k with _ | k
  · obtain ⟨c, rfl⟩ : ∃ c, h = C c := ⟨h.coeff 0, eq_C_of_natDegree_le_zero hk⟩
    rw [hL, taylor_C, sub_self, zero_mul, sub_zero]
    refine ⟨natDegree_C_mul_le _ _ |>.trans (by have := Qw_natDegree w; omega), ?_⟩
    rw [coeff_C_mul, coeff_C_zero, Nat.cast_zero, sub_zero]
    rfl
  · obtain ⟨hd1, hd2⟩ := taylor_sub_self h k hk
    rw [hL]
    constructor
    · refine (natDegree_sub_le _ _).trans (max_le ((natDegree_mul_le).trans ?_)
        ((natDegree_mul_le).trans ?_))
      · have := Qw_natDegree w; omega
      · have := Dpol_natDegree w; omega
    · rw [coeff_sub, show k + 1 + 3 = (k + 1) + 3 from rfl,
        coeff_mul_add_eq_of_natDegree_le hk (Qw_natDegree w),
        show k + 1 + 3 = k + 4 by omega, coeff_mul_add_eq_of_natDegree_le hd1 (Dpol_natDegree w),
        hd2, Dpol_coeff4, a3, Nat.cast_succ]
      ring

def PsiMap (w : Vertex) : (Fin 3 → ℚ) × ℚ[X] →ₗ[ℚ] ℚ[X] := LinearMap.coprod polyOf (Lmap w)

theorem PsiMap_apply (w : Vertex) (p : (Fin 3 → ℚ) × ℚ[X]) :
    PsiMap w p = polyOf p.1 + Lmap w p.2 := rfl

theorem PsiMap_injective (w : Vertex) (hw : a3 w < 0) : Function.Injective (PsiMap w) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨x, h⟩ hxh
  rw [PsiMap_apply] at hxh
  have hh : h = 0 := by
    by_contra hne
    have hc := congrArg (fun q => q.coeff (h.natDegree + 3)) hxh
    simp only [coeff_add, coeff_zero] at hc
    rw [polyOf_coeff_ge x _ (by omega), zero_add, (Lmap_deg w h _ le_rfl).2] at hc
    have h1 : h.coeff h.natDegree ≠ 0 := leadingCoeff_ne_zero.2 hne
    have h2 : a3 w - (h.natDegree : ℚ) ≠ 0 :=
      (sub_neg.2 (hw.trans_le (Nat.cast_nonneg _))).ne
    exact mul_ne_zero h1 h2 hc
  subst hh
  rw [map_zero, add_zero] at hxh
  refine Prod.ext ?_ rfl
  funext j
  have hc := congrArg (fun q => q.coeff (j : ℕ)) hxh
  simp only [coeff_zero] at hc
  rw [polyOf_coeff] at hc
  exact hc

theorem PsiMap_surjective (w : Vertex) (hw : a3 w < 0) : Function.Surjective (PsiMap w) := by
  suffices H : ∀ n, ∀ g : ℚ[X], g.natDegree ≤ n + 2 → ∃ p, PsiMap w p = g from
    fun g => H g.natDegree g (by omega)
  intro n
  induction n with
  | zero =>
    intro g hg
    refine ⟨(fun j => g.coeff j, 0), ?_⟩
    rw [PsiMap_apply, map_zero, add_zero]
    ext m
    rcases Nat.lt_or_ge m 3 with hm | hm
    · exact polyOf_coeff (fun j : Fin 3 => g.coeff j) ⟨m, hm⟩
    · rw [polyOf_coeff_ge _ _ hm, coeff_eq_zero_of_natDegree_lt (by omega)]
  | succ k ih =>
    intro g hg
    have hne : a3 w - (k : ℚ) ≠ 0 := (sub_neg.2 (hw.trans_le (Nat.cast_nonneg _))).ne
    have hcc : g.coeff (k + 3) / (a3 w - k) * (a3 w - k) = g.coeff (k + 3) := div_mul_cancel₀ _ hne
    obtain ⟨hd1, hd2⟩ := Lmap_deg w (C (g.coeff (k + 3) / (a3 w - k)) * X ^ k) k
      (natDegree_C_mul_X_pow_le _ k)
    obtain ⟨p, hp⟩ := ih (g - Lmap w (C (g.coeff (k + 3) / (a3 w - k)) * X ^ k)) (by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [coeff_sub]
      rcases Nat.lt_or_ge (k + 3) N with h1 | h1
      · rw [coeff_eq_zero_of_natDegree_lt (hg.trans_lt (by omega)),
          coeff_eq_zero_of_natDegree_lt (hd1.trans_lt h1), sub_zero]
      · obtain rfl : N = k + 3 := by omega
        rw [hd2, coeff_C_mul_X_pow]
        simp only [↓reduceIte, hcc, sub_self])
    refine ⟨p + (0, C (g.coeff (k + 3) / (a3 w - k)) * X ^ k), ?_⟩
    rw [map_add, hp, PsiMap_apply, map_zero, zero_add, sub_add_cancel]

theorem PsiMap_bijective (w : Vertex) (hw : a3 w < 0) : Function.Bijective (PsiMap w) :=
  ⟨PsiMap_injective w hw, PsiMap_surjective w hw⟩

open Classical in
def red (w : Vertex) : ℚ[X] →ₗ[ℚ] (Fin 3 → ℚ) :=
  if hb : Function.Bijective (PsiMap w) then
    (LinearMap.fst ℚ (Fin 3 → ℚ) ℚ[X]).comp
      (LinearEquiv.ofBijective (PsiMap w) hb).symm.toLinearMap
  else 0

theorem red_PsiMap (w : Vertex) (hw : a3 w < 0) (p : (Fin 3 → ℚ) × ℚ[X]) :
    red w (PsiMap w p) = p.1 := by
  simp only [red, PsiMap_bijective w hw, ↓reduceDIte, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.ofBijective_symm_apply_apply, LinearMap.fst_apply]

theorem red_polyOf (w : Vertex) (hw : a3 w < 0) (x : Fin 3 → ℚ) : red w (polyOf x) = x := by
  have := red_PsiMap w hw (x, 0)
  rwa [PsiMap_apply, map_zero, add_zero] at this

theorem red_Lmap (w : Vertex) (hw : a3 w < 0) (h : ℚ[X]) : red w (Lmap w h) = 0 := by
  have := red_PsiMap w hw (0, h)
  rwa [PsiMap_apply, map_zero, zero_add] at this

theorem red_decomp (w : Vertex) (hw : a3 w < 0) (g : ℚ[X]) :
    ∃ h, g = polyOf (red w g) + Lmap w h := by
  obtain ⟨p, rfl⟩ := PsiMap_surjective w hw g
  exact ⟨p.2, by rw [red_PsiMap w hw, PsiMap_apply]⟩

def Rep (M : Matrix (Fin 3) (Fin 3) ℚ) (u v : Vertex) (P Q : ℚ[X]) : Prop :=
  ∀ g : ℚ[X], M *ᵥ red v (P * g) = red u (Q * g)

theorem Rep.mul {M1 M2 : Matrix (Fin 3) (Fin 3) ℚ} {u v w : Vertex} {P1 Q1 P2 Q2 : ℚ[X]}
    (h1 : Rep M1 u v P1 Q1) (h2 : Rep M2 v w P2 Q2) :
    Rep (M1 * M2) u w (P1 * P2) (Q1 * Q2) := by
  intro g
  rw [← Matrix.mulVec_mulVec, show P1 * P2 * g = P2 * (P1 * g) by ring, h2,
    show Q2 * (P1 * g) = P1 * (Q2 * g) by ring, h1, mul_assoc]

def lam (w : Vertex) (c : Coord) : ℚ[X] := 1 + C (shiftParam w c)⁻¹ * X

theorem prod_update_mul {n : ℕ} (φ : ℤ → ℚ[X]) (f : Fin n → ℤ) (i : Fin n) (a : ℤ) :
    (∏ k, φ (Function.update f i a k)) * φ (f i) = (∏ k, φ (f k)) * φ a := by
  rw [Fintype.prod_eq_mul_prod_compl i, Fintype.prod_eq_mul_prod_compl i (fun k => φ (f k)),
    Function.update_self,
    prod_congr rfl fun k hk => by rw [Function.update_of_ne (by simpa using hk)]]
  ring

theorem update_inl_comp (w : Vertex) (i : Fin 4) (a : ℤ) (k : Fin 4) :
    Function.update w (.inl i) a (.inl k) = Function.update (fun j => w (.inl j)) i a k :=
  congrFun (Function.update_comp_eq_of_injective w Sum.inl_injective i a) k

theorem update_inr_comp (w : Vertex) (i : Fin 3) (a : ℤ) (k : Fin 3) :
    Function.update w (.inr i) a (.inr k) = Function.update (fun j => w (.inr j)) i a k :=
  congrFun (Function.update_comp_eq_of_injective w Sum.inr_injective i a) k

theorem Dpol_update_inl (w : Vertex) (i : Fin 4) (a : ℤ) :
    Dpol (Function.update w (.inl i) a) * (X + C (w (.inl i) : ℚ)) = Dpol w * (X + C (a : ℚ)) := by
  unfold Dpol
  simp only [update_inl_comp]
  exact prod_update_mul (fun z : ℤ => X + C (z : ℚ)) (fun j => w (.inl j)) i a

theorem Apol_update_inr (w : Vertex) (i : Fin 3) (a : ℤ) :
    Apol (Function.update w (.inr i) a) * (X + C ((w (.inr i) : ℚ) - 1)) =
      Apol w * (X + C ((a : ℚ) - 1)) := by
  unfold Apol
  simp only [update_inr_comp]
  have h := prod_update_mul (fun z : ℤ => X + C ((z : ℚ) - 1)) (fun j => w (.inr j)) i a
  beta_reduce at h
  rw [mul_assoc, h, mul_assoc]

theorem Apol_update_inl (w : Vertex) (i : Fin 4) (a : ℤ) :
    Apol (Function.update w (.inl i) a) = Apol w := by
  unfold Apol
  congr 1

theorem Dpol_update_inr (w : Vertex) (i : Fin 3) (a : ℤ) :
    Dpol (Function.update w (.inr i) a) = Dpol w :=
  prod_congr rfl fun k _ => by rw [Function.update_of_ne Sum.inl_ne_inr]

theorem hpinv (p : ℚ) (hp : p ≠ 0) : C p⁻¹ * C p = (1 : ℚ[X]) := by
  rw [← C_mul, inv_mul_cancel₀ hp, C_1]

theorem move_true (w : Vertex) (c : Coord) :
    move w c true = Function.update w c (w c + 1) := rfl

theorem move_false (w : Vertex) (c : Coord) :
    move w c false = Function.update w c (w c - 1) := rfl

theorem transport_inl (w : Vertex) (i : Fin 4) (hp : (w (.inl i) : ℚ) ≠ 0) (h : ℚ[X]) :
    lam w (.inl i) * Lmap (move w (.inl i) true) h =
      Lmap w ((1 + C (w (.inl i) : ℚ)⁻¹ * X) * h) := by
  have hD := Dpol_update_inl w i (w (.inl i) + 1)
  rw [Int.cast_add, Int.cast_one, C_add, C_1] at hD
  have hA := Apol_update_inl w i (w (.inl i) + 1)
  have ht : taylor 1 ((1 + C (w (.inl i) : ℚ)⁻¹ * X) * h) =
      (1 + C (w (.inl i) : ℚ)⁻¹ * (X + 1)) * taylor 1 h := by
    rw [taylor_mul, map_add, taylor_one, taylor_mul, taylor_C, taylor_X, C_1]
  rw [Lmap_apply, Lmap_apply, ht, move_true, hA]
  simp only [lam, shiftParam]
  linear_combination (-(C (w (.inl i) : ℚ)⁻¹) * taylor 1 h) * hD +
    (taylor 1 h * Dpol (Function.update w (.inl i) (w (.inl i) + 1)) - taylor 1 h * Dpol w) *
      hpinv _ hp

theorem transport_inr (w : Vertex) (i : Fin 3) (hp : (w (.inr i) : ℚ) - 1 ≠ 0) (h : ℚ[X]) :
    lam w (.inr i) * Lmap (move w (.inr i) false) h =
      Lmap w ((1 + C ((w (.inr i) : ℚ) - 1)⁻¹ * (X - 1)) * h) := by
  have hA := Apol_update_inr w i (w (.inr i) - 1)
  have hc : C (((w (.inr i) - 1 : ℤ) : ℚ) - 1) = C ((w (.inr i) : ℚ) - 1) - 1 := by
    rw [C_sub, C_1, Int.cast_sub, Int.cast_one]
  have hD := Dpol_update_inr w i (w (.inr i) - 1)
  have ht : taylor 1 ((1 + C ((w (.inr i) : ℚ) - 1)⁻¹ * (X - 1)) * h) =
      (1 + C ((w (.inr i) : ℚ) - 1)⁻¹ * X) * taylor 1 h := by
    rw [taylor_mul, map_add, taylor_one, taylor_mul, taylor_C, map_sub, taylor_X, taylor_one, C_1]
    ring
  rw [Lmap_apply, Lmap_apply, ht, move_false, hD]
  simp only [lam, shiftParam]
  linear_combination (C ((w (.inr i) : ℚ) - 1)⁻¹ * h) * hA +
    (C ((w (.inr i) : ℚ) - 1)⁻¹ * h * Apol w) * hc +
    (h * Apol w - h * Apol (Function.update w (.inr i) (w (.inr i) - 1))) * hpinv _ hp

theorem transport (w : Vertex) (c : Coord) (up : Bool) (hf : isForward c up = true)
    (hp : shiftParam w c ≠ 0) (h : ℚ[X]) : ∃ H, lam w c * Lmap (move w c up) h = Lmap w H := by
  rcases c with i | i
  · obtain rfl : up = true := hf
    exact ⟨_, transport_inl w i hp h⟩
  · obtain rfl : up = false := by simpa [isForward] using hf
    exact ⟨_, transport_inr w i hp h⟩

def tvec (w : Vertex) : Fin 3 → ℚ :=
  -(a3 w)⁻¹ • ![(Qw w).coeff 0, (Qw w).coeff 1, (Qw w).coeff 2]

theorem red_X3 (w : Vertex) (hw : a3 w < 0) : red w (X ^ 3) = tvec w := by
  have h0 := red_Lmap w hw 1
  rw [Lmap_apply, one_mul, taylor_one, C_1, one_mul, ← Qw_eq, Qw_expand] at h0
  have hp : C ((Qw w).coeff 0) + C ((Qw w).coeff 1) * X + C ((Qw w).coeff 2) * X ^ 2 =
      polyOf ![(Qw w).coeff 0, (Qw w).coeff 1, (Qw w).coeff 2] := by
    rw [polyOf_apply]
    rfl
  rw [hp, map_add, red_polyOf w hw, ← smul_eq_C_mul, map_smul] at h0
  have h1 := eq_neg_of_add_eq_zero_right h0
  calc red w (X ^ 3) = (a3 w)⁻¹ • (a3 w • red w (X ^ 3)) := (inv_smul_smul₀ hw.ne _).symm
    _ = tvec w := by rw [h1, tvec, smul_neg, neg_smul]

theorem Tw_eq (w : Vertex) : Tw w = !![0, 0, -(Qw w).coeff 0 / a3 w; 1, 0, -(Qw w).coeff 1 / a3 w;
    0, 1, -(Qw w).coeff 2 / a3 w] := rfl

theorem Tw_mulVec (w : Vertex) (x : Fin 3 → ℚ) :
    Tw w *ᵥ x = ![0, x 0, x 1] + x 2 • tvec w := by
  rw [Tw_eq, tvec]
  funext j
  fin_cases j <;>
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply, Fin.zero_eta,
      Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Pi.neg_apply] <;> ring

theorem red_lam_polyOf (w : Vertex) (hw : a3 w < 0) (p : ℚ) (x : Fin 3 → ℚ) :
    red w ((1 + C p⁻¹ * X) * polyOf x) = (1 + p⁻¹ • Tw w) *ᵥ x := by
  have hpoly : (1 + C p⁻¹ * X) * polyOf x =
      polyOf (x + p⁻¹ • ![0, x 0, x 1]) + (p⁻¹ * x 2) • X ^ 3 := by
    rw [polyOf_apply, polyOf_apply, smul_eq_C_mul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, C_add, C_mul, C_0]
    ring
  rw [hpoly, map_add, map_smul, red_polyOf w hw, red_X3 w hw, Matrix.add_mulVec,
    Matrix.one_mulVec, Matrix.smul_mulVec, Tw_mulVec, smul_add, smul_smul, add_assoc]

theorem rep_forward (w : Vertex) (c : Coord) (up : Bool) (hf : isForward c up = true)
    (hw : a3 w < 0) (hw' : a3 (move w c up) < 0) (hp : shiftParam w c ≠ 0) :
    Rep (stepMat w c up) w (move w c up) 1 (lam w c) := by
  intro g
  obtain ⟨h, hg⟩ := red_decomp _ hw' g
  obtain ⟨H, hH⟩ := transport w c up hf hp h
  have hs : stepMat w c up = 1 + (shiftParam w c)⁻¹ • Tw w := by
    simp only [stepMat, hf, ↓reduceIte]
  rw [one_mul, hs]
  conv_rhs => rw [hg, mul_add, map_add, hH, red_Lmap w hw, add_zero]
  exact (red_lam_polyOf w hw _ _).symm

theorem isForward_not (c : Coord) (up : Bool) : isForward c (!up) = !isForward c up := by
  rcases c with i | i <;> cases up <;> rfl

theorem move_self (w : Vertex) (c : Coord) (up : Bool) :
    move w c up c = if up then w c + 1 else w c - 1 :=
  Function.update_self _ _ _

theorem move_ne (w : Vertex) (c c' : Coord) (up : Bool) (h : c' ≠ c) : move w c up c' = w c' :=
  Function.update_of_ne h _ _

theorem move_move (w : Vertex) (c : Coord) (up : Bool) : move (move w c up) c (!up) = w := by
  funext c'
  by_cases h : c' = c
  · subst h
    rw [move_self, move_self]
    cases up <;> simp
  · rw [move_ne _ _ _ _ h, move_ne _ _ _ _ h]

theorem stepMat_inv (w : Vertex) (c : Coord) (up : Bool) (hf : isForward c up = false) :
    stepMat w c up = (stepMat (move w c up) c (!up))⁻¹ := by
  have hf' : isForward c (!up) = true := by rw [isForward_not, hf]; rfl
  simp only [stepMat, hf, hf', Bool.false_eq_true, ↓reduceIte]

theorem rep_inverse (w : Vertex) (c : Coord) (up : Bool) (hf : isForward c up = false)
    (hw : a3 w < 0) (hw' : a3 (move w c up) < 0) (hp : shiftParam (move w c up) c ≠ 0)
    (hdet : IsUnit (stepMat (move w c up) c (!up)).det) :
    Rep (stepMat w c up) w (move w c up) (lam (move w c up) c) 1 := by
  have hf' : isForward c (!up) = true := by rw [isForward_not, hf]; rfl
  have hF := rep_forward (move w c up) c (!up) hf' hw' (by rw [move_move]; exact hw) hp
  rw [move_move] at hF
  intro g
  rw [stepMat_inv w c up hf, ← hF g, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet,
    Matrix.one_mulVec, one_mul]

theorem det3 (a b c d e f g h i : ℚ) :
    Matrix.det !![a, b, c; d, e, f; g, h, i] =
      a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g := by
  rw [Matrix.det_fin_three]
  rfl

theorem det_step (w : Vertex) (p : ℚ) (hp : p ≠ 0) (ha : a3 w ≠ 0) :
    (1 + p⁻¹ • Tw w).det * (a3 w * p ^ 3) = -(Qw w).eval (-p) := by
  have hQ : (Qw w).eval (-p) = (Qw w).coeff 0 + (Qw w).coeff 1 * (-p) +
      (Qw w).coeff 2 * (-p) ^ 2 + (Qw w).coeff 3 * (-p) ^ 3 := by
    conv_lhs => rw [Qw_expand]
    simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow, a3]
  have ha' : (Qw w).coeff 3 ≠ 0 := ha
  have hM : 1 + p⁻¹ • Tw w = !![1, 0, p⁻¹ * (-(Qw w).coeff 0 / a3 w);
      p⁻¹, 1, p⁻¹ * (-(Qw w).coeff 1 / a3 w); 0, p⁻¹, 1 + p⁻¹ * (-(Qw w).coeff 2 / a3 w)] := by
    rw [Tw_eq, Matrix.one_fin_three, Matrix.smul_of, Matrix.of_add_of]
    simp only [Matrix.smul_cons, Matrix.smul_empty, Matrix.cons_add_cons, Matrix.empty_add_empty,
      smul_eq_mul, mul_zero, add_zero, mul_one, zero_add]
  rw [hQ, hM, det3]
  have hp1 : p * p⁻¹ = 1 := mul_inv_cancel₀ hp
  have ha1 : a3 w * (a3 w)⁻¹ = 1 := mul_inv_cancel₀ ha
  simp only [div_eq_mul_inv, a3] at ha1 ⊢
  linear_combination (-((Qw w).coeff 2) * p ^ 2 * ((Qw w).coeff 3 * ((Qw w).coeff 3)⁻¹) +
    (Qw w).coeff 1 * p * (p * p⁻¹ + 1) * ((Qw w).coeff 3 * ((Qw w).coeff 3)⁻¹) -
    (Qw w).coeff 0 * ((p * p⁻¹) ^ 2 + p * p⁻¹ + 1) * ((Qw w).coeff 3 * ((Qw w).coeff 3)⁻¹)) * hp1 +
    (-((Qw w).coeff 2) * p ^ 2 + (Qw w).coeff 1 * p - (Qw w).coeff 0) * ha1

theorem isUnit_det_step (w : Vertex) (p : ℚ) (hp : p ≠ 0) (ha : a3 w ≠ 0)
    (hq : (Qw w).eval (-p) ≠ 0) : IsUnit (1 + p⁻¹ • Tw w).det := by
  refine isUnit_iff_ne_zero.2 fun h0 => hq ?_
  have h1 := det_step w p hp ha
  rw [h0, zero_mul] at h1
  exact neg_eq_zero.mp h1.symm

def endpt : Vertex → List (Coord × Bool) → Vertex
  | w, [] => w
  | w, (c, up) :: l => endpt (move w c up) l

def Pf (w : Vertex) (c : Coord) (up : Bool) : ℚ[X] :=
  if isForward c up then 1 else lam (move w c up) c

def Qf (w : Vertex) (c : Coord) (up : Bool) : ℚ[X] := if isForward c up then lam w c else 1

def Pfac : Vertex → List (Coord × Bool) → ℚ[X]
  | _, [] => 1
  | w, (c, up) :: l => Pf w c up * Pfac (move w c up) l

def Qfac : Vertex → List (Coord × Bool) → ℚ[X]
  | _, [] => 1
  | w, (c, up) :: l => Qf w c up * Qfac (move w c up) l

def Good (w : Vertex) (c : Coord) (up : Bool) : Prop :=
  a3 w < 0 ∧ a3 (move w c up) < 0 ∧ (isForward c up = true → shiftParam w c ≠ 0) ∧
    (isForward c up = false → shiftParam (move w c up) c ≠ 0 ∧
      IsUnit (stepMat (move w c up) c (!up)).det)

def RouteStep (w : Vertex) (c : Coord) (up : Bool) : Prop :=
  match c with
  | .inl i => if (i : ℕ) < 3 then up = true ∧ 1 ≤ w c else up = false ∧ w c ≤ 0
  | .inr _ => up = true ∧ 1 ≤ w c

def AllGood : Vertex → List (Coord × Bool) → Prop
  | _, [] => True
  | w, (c, up) :: l => (Good w c up ∧ RouteStep w c up) ∧ AllGood (move w c up) l

theorem rep_step (w : Vertex) (c : Coord) (up : Bool) (h : Good w c up) :
    Rep (stepMat w c up) w (move w c up) (Pf w c up) (Qf w c up) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases hf : isForward c up
  · obtain ⟨hp, hd⟩ := h4 hf
    simp only [Pf, Qf, hf, Bool.false_eq_true, ↓reduceIte]
    exact rep_inverse w c up hf h1 h2 hp hd
  · simp only [Pf, Qf, hf, ↓reduceIte]
    exact rep_forward w c up hf h1 h2 (h3 hf)

theorem rep_walk : ∀ (l : List (Coord × Bool)) (w : Vertex), AllGood w l →
    Rep (walk w l) w (endpt w l) (Pfac w l) (Qfac w l)
  | [], w, _ => fun g => by
    simp only [walk, endpt, Pfac, Qfac, one_mul, Matrix.one_mulVec]
  | (c, up) :: l, w, h => (rep_step w c up h.1.1).mul (rep_walk l _ h.2)

theorem det_walk : ∀ (l : List (Coord × Bool)) (w : Vertex), AllGood w l →
    (∀ x ∈ l, isForward x.1 x.2 = false) → IsUnit (walk w l).det
  | [], w, _, _ => by simp only [walk, Matrix.det_one, isUnit_one]
  | (c, up) :: l, w, h, hl => by
    have hf : isForward c up = false := hl (c, up) List.mem_cons_self
    simp only [walk]
    rw [Matrix.det_mul, stepMat_inv w c up hf]
    exact (Matrix.isUnit_nonsing_inv_det _ (h.1.1.2.2.2 hf).2).mul
      (det_walk l _ h.2 fun x hx => hl x (List.mem_cons_of_mem _ hx))

theorem Qfac_inv : ∀ (l : List (Coord × Bool)) (w : Vertex),
    (∀ x ∈ l, isForward x.1 x.2 = false) → Qfac w l = 1
  | [], _, _ => rfl
  | (c, up) :: l, w, hl => by
    have hf : isForward c up = false := hl (c, up) List.mem_cons_self
    simp only [Qfac, Qf, hf, Bool.false_eq_true, ↓reduceIte, one_mul]
    exact Qfac_inv l _ fun x hx => hl x (List.mem_cons_of_mem _ hx)

def U (x : ℤ) : ℚ[X] := ∏ t ∈ Ico 1 x.toNat, (1 + C ((t : ℚ))⁻¹ * X)

def Xi (x : ℤ) : ℚ[X] := ∏ t ∈ Ico 1 (1 - x).toNat, (1 - C ((t : ℚ))⁻¹ * X)

def phT : Coord → ℤ → ℚ[X]
  | .inl i, x => if (i : ℕ) < 3 then U x else 1
  | .inr _, _ => 1

def phP : Coord → ℤ → ℚ[X]
  | .inl i, x => if (i : ℕ) < 3 then 1 else Xi x
  | .inr _, y => U y

def Th (w : Vertex) : ℚ[X] := ∏ c, phT c (w c)

def Pp (w : Vertex) : ℚ[X] := ∏ c, phP c (w c)

theorem prod_update_coord (φ : Coord → ℤ → ℚ[X]) (w : Vertex) (c : Coord) (a : ℤ) (f : ℚ[X])
    (hf : φ c a = φ c (w c) * f) :
    ∏ c', φ c' (Function.update w c a c') = (∏ c', φ c' (w c')) * f := by
  rw [Fintype.prod_eq_mul_prod_compl c, Fintype.prod_eq_mul_prod_compl c (fun c' => φ c' (w c')),
    Function.update_self, hf,
    prod_congr rfl fun k hk => by rw [Function.update_of_ne (by simpa using hk)]]
  ring

theorem U_succ (x : ℤ) (hx : 1 ≤ x) : U (x + 1) = U x * (1 + C (x : ℚ)⁻¹ * X) := by
  unfold U
  rw [show (x + 1).toNat = x.toNat + 1 by omega, prod_Ico_succ_top (by omega)]
  have h : ((x.toNat : ℕ) : ℚ) = (x : ℚ) := by
    have := Int.toNat_of_nonneg (show 0 ≤ x by omega)
    exact_mod_cast this
  rw [h]

theorem Xi_pred (x : ℤ) (hx : x ≤ 0) :
    Xi (x - 1) = Xi x * (1 + C ((x - 1 : ℤ) : ℚ)⁻¹ * X) := by
  unfold Xi
  rw [show (1 - (x - 1)).toNat = (1 - x).toNat + 1 by omega, prod_Ico_succ_top (by omega)]
  have h : (((1 - x).toNat : ℕ) : ℚ) = 1 - (x : ℚ) := by
    have := Int.toNat_of_nonneg (show 0 ≤ 1 - x by omega)
    exact_mod_cast this
  rw [h, Int.cast_sub, Int.cast_one, show ((x : ℚ) - 1)⁻¹ = -(1 - (x : ℚ))⁻¹ by
    rw [← inv_neg, neg_sub], C_neg]
  ring

theorem pot_step (w : Vertex) (c : Coord) (up : Bool) (h : RouteStep w c up) :
    Th (move w c up) = Th w * Qf w c up ∧ Pp (move w c up) = Pp w * Pf w c up := by
  rcases c with i | i
  · by_cases hi : (i : ℕ) < 3
    · have h' : up = true ∧ 1 ≤ w (.inl i) := by simpa [RouteStep, hi] using h
      obtain ⟨rfl, h1⟩ := h'
      have hQ : Qf w (.inl i) true = 1 + C ((w (.inl i) : ℤ) : ℚ)⁻¹ * X := rfl
      have hP : Pf w (.inl i) true = 1 := rfl
      rw [hQ, hP, move_true]
      exact ⟨prod_update_coord phT w (.inl i) _ _ (by simp only [phT, hi, ↓reduceIte]; exact U_succ _ h1),
        prod_update_coord phP w (.inl i) _ _ (by simp only [phP, hi, ↓reduceIte, mul_one])⟩
    · have h' : up = false ∧ w (.inl i) ≤ 0 := by simpa [RouteStep, hi] using h
      obtain ⟨rfl, h1⟩ := h'
      have hQ : Qf w (.inl i) false = 1 := rfl
      have hP : Pf w (.inl i) false = 1 + C ((w (.inl i) - 1 : ℤ) : ℚ)⁻¹ * X := by
        simp only [Pf, isForward, Bool.false_eq_true, ↓reduceIte, lam, shiftParam, move_self]
      rw [hQ, hP, move_false]
      exact ⟨prod_update_coord phT w (.inl i) _ _ (by simp only [phT, hi, ↓reduceIte, mul_one]),
        prod_update_coord phP w (.inl i) _ _ (by simp only [phP, hi, ↓reduceIte]; exact Xi_pred _ h1)⟩
  · have h' : up = true ∧ 1 ≤ w (.inr i) := by simpa [RouteStep] using h
    obtain ⟨rfl, h1⟩ := h'
    have hQ : Qf w (.inr i) true = 1 := rfl
    have hP : Pf w (.inr i) true = 1 + C ((w (.inr i) : ℤ) : ℚ)⁻¹ * X := by
      simp only [Pf, isForward, Bool.not_true, Bool.false_eq_true, ↓reduceIte, lam, shiftParam,
        move_self, Int.cast_add, Int.cast_one, add_sub_cancel_right]
    rw [hQ, hP, move_true]
    exact ⟨prod_update_coord phT w (.inr i) _ _ (by simp only [phT, mul_one]),
      prod_update_coord phP w (.inr i) _ _ (by simp only [phP]; exact U_succ _ h1)⟩

theorem pot_walk : ∀ (l : List (Coord × Bool)) (w : Vertex), AllGood w l →
    Th (endpt w l) = Th w * Qfac w l ∧ Pp (endpt w l) = Pp w * Pfac w l
  | [], w, _ => by simp only [endpt, Qfac, Pfac, mul_one, and_self]
  | (c, up) :: l, w, h => by
    obtain ⟨h1, h2⟩ := pot_walk l _ h.2
    obtain ⟨h3, h4⟩ := pot_step w c up h.1.2
    simp only [endpt, Qfac, Pfac]
    rw [h1, h2, h3, h4]
    constructor <;> ring

theorem ite_up {up : Bool} (h : up = true) (a b : ℤ) : (if up then a else b) = a := by
  subst h; rfl

theorem ite_down {up : Bool} (h : up = false) (a b : ℤ) : (if up then a else b) = b := by
  subst h; rfl

def sig : Coord → Bool
  | .inl i => decide ((i : ℕ) < 3)
  | .inr _ => true

def InBox (a b v : Vertex) : Prop :=
  ∀ c, (sig c = true → a c ≤ v c ∧ v c ≤ b c) ∧ (sig c = false → b c ≤ v c ∧ v c ≤ a c)

theorem endpt_mono : ∀ (l : List (Coord × Bool)) (w : Vertex), (∀ x ∈ l, x.2 = sig x.1) →
    ∀ c, (sig c = true → w c ≤ endpt w l c) ∧ (sig c = false → endpt w l c ≤ w c)
  | [], w, _ => fun c => ⟨fun _ => le_rfl, fun _ => le_rfl⟩
  | (c0, up) :: l, w, hl => fun c => by
    have ih := endpt_mono l (move w c0 up) (fun x hx => hl x (List.mem_cons_of_mem _ hx)) c
    have hup : up = sig c0 := hl (c0, up) List.mem_cons_self
    simp only [endpt]
    by_cases hc : c = c0
    · subst hc hup
      rw [move_self] at ih
      constructor
      · intro hs
        have h1 := ih.1 hs
        rw [ite_up hs] at h1
        omega
      · intro hs
        have h1 := ih.2 hs
        rw [ite_down hs] at h1
        omega
    · rw [move_ne _ _ _ _ hc] at ih
      exact ih

theorem allGood_box : ∀ (l : List (Coord × Bool)) (w : Vertex), (∀ x ∈ l, x.2 = sig x.1) →
    (∀ v c, InBox w (endpt w l) v → (sig c = true → v c < endpt w l c) →
      (sig c = false → endpt w l c < v c) → Good v c (sig c) ∧ RouteStep v c (sig c)) →
    AllGood w l
  | [], _, _, _ => trivial
  | (c0, up) :: l, w, hl, H => by
    have hup : up = sig c0 := hl (c0, up) List.mem_cons_self
    have hl' : ∀ x ∈ l, x.2 = sig x.1 := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have hm := endpt_mono l (move w c0 up) hl'
    have hm0 := endpt_mono ((c0, up) :: l) w hl
    simp only [endpt] at H hm0
    subst hup
    have hmc := hm c0
    rw [move_self] at hmc
    refine ⟨H w c0 (fun c => ⟨fun hs => ⟨le_rfl, (hm0 c).1 hs⟩, fun hs => ⟨(hm0 c).2 hs, le_rfl⟩⟩)
      (fun hs => by have h1 := hmc.1 hs; rw [ite_up hs] at h1; omega)
      (fun hs => by have h1 := hmc.2 hs; rw [ite_down hs] at h1; omega),
      allGood_box l _ hl' fun v c hb h1 h2 => H v c (fun c' => ?_) h1 h2⟩
    have hbc := hb c'
    by_cases hc : c' = c0
    · subst hc
      rw [move_self] at hbc
      constructor
      · intro hs
        have h1 := hbc.1 hs
        rw [ite_up hs] at h1
        exact ⟨by omega, h1.2⟩
      · intro hs
        have h1 := hbc.2 hs
        rw [ite_down hs] at h1
        exact ⟨h1.1, by omega⟩
    · rw [move_ne _ _ _ _ hc] at hbc
      exact hbc

def sgn (up : Bool) : ℤ := if up then 1 else -1

theorem move_eq (w : Vertex) (c : Coord) (up : Bool) : move w c up = w + Pi.single c (sgn up) := by
  funext c'
  by_cases h : c' = c
  · subst h
    rw [move_self, Pi.add_apply, Pi.single_eq_same]
    cases up <;> rfl
  · rw [move_ne _ _ _ _ h, Pi.add_apply, Pi.single_eq_of_ne h, add_zero]

def disp : List (Coord × Bool) → Vertex
  | [] => 0
  | (c, up) :: l => Pi.single c (sgn up) + disp l

theorem endpt_eq : ∀ (l : List (Coord × Bool)) (w : Vertex), endpt w l = w + disp l
  | [], w => (add_zero w).symm
  | (c, up) :: l, w => by rw [endpt, endpt_eq l, move_eq, disp, add_assoc]

theorem disp_append : ∀ (l1 l2 : List (Coord × Bool)), disp (l1 ++ l2) = disp l1 + disp l2
  | [], l2 => (zero_add _).symm
  | (c, up) :: l1, l2 => by rw [List.cons_append, disp, disp, disp_append l1 l2, add_assoc]

theorem disp_flatten_replicate (l : List (Coord × Bool)) :
    ∀ n : ℕ, disp (List.replicate n l).flatten = (n : ℤ) • disp l
  | 0 => by simp [disp]
  | n + 1 => by
    rw [List.replicate_succ, List.flatten_cons, disp_append, disp_flatten_replicate l n]
    push_cast
    rw [add_smul, one_smul, add_comm]

theorem disp_replicate (c : Coord) (up : Bool) :
    ∀ k : ℕ, disp (List.replicate k (c, up)) = Pi.single c ((k : ℤ) * sgn up)
  | 0 => by simp [disp]
  | k + 1 => by
    rw [List.replicate_succ, disp, disp_replicate c up k, ← Pi.single_add]
    push_cast
    ring_nf

theorem natAbs_mul_sgn (z : ℤ) : (z.natAbs : ℤ) * sgn (decide (0 ≤ z)) = z := by
  unfold sgn
  split_ifs with h <;> simp at h <;> omega

theorem disp_blockStep (d : Vertex) : disp (blockStep d) = d := by
  simp only [blockStep, coordOrder, List.flatMap_cons, List.flatMap_nil, disp_append,
    disp_replicate, natAbs_mul_sgn, List.append_nil]
  conv_rhs => rw [← Finset.univ_sum_single d, Fintype.sum_sum_type, Fin.sum_univ_four,
    Fin.sum_univ_three]
  simp only [disp, add_zero, add_assoc]

theorem endpt_block (w d : Vertex) (n : ℕ) :
    endpt w (List.replicate n (blockStep d)).flatten = w + (n : ℤ) • d := by
  rw [endpt_eq, disp_flatten_replicate, disp_blockStep]

theorem mem_block (d : Vertex) (n : ℕ) (x : Coord × Bool)
    (hx : x ∈ (List.replicate n (blockStep d)).flatten) : d x.1 ≠ 0 ∧ x.2 = decide (0 ≤ d x.1) := by
  rw [List.mem_flatten] at hx
  obtain ⟨l, hl, hx⟩ := hx
  rw [(List.mem_replicate.1 hl).2, blockStep, List.mem_flatMap] at hx
  obtain ⟨c, _, hc⟩ := hx
  obtain ⟨hn, rfl⟩ := List.mem_replicate.1 hc
  exact ⟨Int.natAbs_ne_zero.mp hn, rfl⟩

theorem mono_block (n : ℕ) (d : Vertex) (hd : ∀ c, d c ≠ 0 → sig c = decide (0 ≤ d c)) :
    ∀ x ∈ (List.replicate n (blockStep d)).flatten, x.2 = sig x.1 := fun x hx => by
  obtain ⟨h1, h2⟩ := mem_block d n x hx
  rw [h2, hd _ h1]

theorem allGood_append : ∀ (l1 l2 : List (Coord × Bool)) (w : Vertex),
    AllGood w l1 → AllGood (endpt w l1) l2 → AllGood w (l1 ++ l2)
  | [], _, _, _, h => h
  | (_, _) :: l1, l2, _, h1, h2 => ⟨h1.1, allGood_append l1 l2 _ h1.2 h2⟩

theorem endpt_append : ∀ (l1 l2 : List (Coord × Bool)) (w : Vertex),
    endpt w (l1 ++ l2) = endpt (endpt w l1) l2
  | [], _, _ => rfl
  | (c, up) :: l1, l2, w => endpt_append l1 l2 (move w c up)

theorem walk_append : ∀ (l1 l2 : List (Coord × Bool)) (w : Vertex),
    walk w (l1 ++ l2) = walk w l1 * walk (endpt w l1) l2
  | [], _, _ => by simp only [List.nil_append, walk, endpt, one_mul]
  | (c, up) :: l1, l2, w => by
    simp only [List.cons_append, walk, endpt]
    rw [walk_append l1 l2, mul_assoc]

def a3Z (w : Vertex) : ℤ := ∑ i : Fin 3, (w (.inr i) - 1) - ∑ i : Fin 4, w (.inl i)

theorem a3_eq_a3Z (w : Vertex) : a3 w = (a3Z w : ℚ) := by
  rw [a3_eq, a3Z]
  push_cast
  ring

theorem a3Z_move_inl (w : Vertex) (i : Fin 4) (up : Bool) :
    a3Z (move w (.inl i) up) = a3Z w - sgn up := by
  simp only [a3Z, move_eq, Pi.add_apply, sum_add_distrib, Pi.single_apply, reduceCtorEq,
    ↓reduceIte, Sum.inl.injEq, sum_ite_eq', mem_univ, add_zero]
  ring

theorem a3Z_move_inr (w : Vertex) (i : Fin 3) (up : Bool) :
    a3Z (move w (.inr i) up) = a3Z w + sgn up := by
  simp only [a3Z, move_eq, Pi.add_apply, Pi.single_apply, reduceCtorEq,
    ↓reduceIte, Sum.inr.injEq, add_zero]
  rw [show ∑ k : Fin 3, (w (.inr k) + (if k = i then sgn up else 0) - 1) =
    ∑ k : Fin 3, (w (.inr k) - 1) + ∑ k : Fin 3, (if k = i then sgn up else 0) by
      rw [← sum_add_distrib]; exact sum_congr rfl fun k _ => by ring,
    sum_ite_eq']
  simp only [mem_univ, ↓reduceIte]
  ring

theorem goodR_up (v : Vertex) (i : Fin 4) (hi : (i : ℕ) < 3) (h1 : 1 ≤ v (.inl i))
    (ha : a3Z v < 0) : Good v (.inl i) true ∧ RouteStep v (.inl i) true := by
  refine ⟨⟨by rw [a3_eq_a3Z]; exact_mod_cast ha, by
    rw [a3_eq_a3Z, a3Z_move_inl]; simp only [sgn, ↓reduceIte]; exact_mod_cast (by omega : a3Z v - 1 < 0),
    fun _ => by simp only [shiftParam]; exact_mod_cast (by omega : v (.inl i) ≠ 0),
    fun h => nomatch h⟩, ?_⟩
  simp only [RouteStep, hi, ↓reduceIte, true_and]
  exact h1

theorem goodR_low (v : Vertex) (i : Fin 3) (h1 : 1 ≤ v (.inr i))
    (hx : ∀ k : Fin 4, v (.inl k) ≠ v (.inr i)) (ha : a3Z v + 1 < 0) :
    Good v (.inr i) true ∧ RouteStep v (.inr i) true := by
  have hv' : a3 (move v (.inr i) true) < 0 := by
    rw [a3_eq_a3Z, a3Z_move_inr]; simp only [sgn, ↓reduceIte]; exact_mod_cast ha
  have hsp : shiftParam (move v (.inr i) true) (.inr i) = (v (.inr i) : ℚ) := by
    simp only [shiftParam, move_self, ↓reduceIte, Int.cast_add, Int.cast_one, add_sub_cancel_right]
  have hp : (v (.inr i) : ℚ) ≠ 0 := by exact_mod_cast (by omega : v (.inr i) ≠ 0)
  refine ⟨⟨by rw [a3_eq_a3Z]; exact_mod_cast (by omega : a3Z v < 0), hv',
    fun h => absurd h Bool.false_ne_true, fun _ => ⟨by rw [hsp]; exact hp, ?_⟩⟩,
    by simp only [RouteStep, true_and]; exact h1⟩
  have hs : stepMat (move v (.inr i) true) (.inr i) (!true) =
      1 + (shiftParam (move v (.inr i) true) (.inr i))⁻¹ • Tw (move v (.inr i) true) := by
    simp only [stepMat, isForward, Bool.not_true, Bool.not_false, ↓reduceIte]
  rw [hs, hsp]
  refine isUnit_det_step _ _ hp hv'.ne ?_
  rw [Qw_eq, eval_sub, move_true, Dpol_update_inr]
  have hA : (Apol (Function.update v (.inr i) (v (.inr i) + 1))).eval (-(v (.inr i) : ℚ)) = 0 := by
    unfold Apol
    rw [eval_mul, eval_prod, prod_eq_zero (mem_univ i), mul_zero]
    rw [eval_add, eval_X, eval_C, Function.update_self, Int.cast_add, Int.cast_one]
    ring
  rw [hA, zero_sub, neg_ne_zero, Dpol, eval_prod, prod_ne_zero_iff]
  intro k _
  rw [eval_add, eval_X, eval_C]
  intro h0
  exact hx k (Int.cast_inj.mp (neg_add_eq_zero.mp h0)).symm

theorem goodR_x3 (v : Vertex) (h0 : v (.inl 3) ≤ 0) (hy : ∀ k : Fin 3, 1 ≤ v (.inr k))
    (ha : a3Z v + 1 < 0) : Good v (.inl 3) false ∧ RouteStep v (.inl 3) false := by
  have hv' : a3 (move v (.inl 3) false) < 0 := by
    rw [a3_eq_a3Z, a3Z_move_inl]; simp only [sgn, Bool.false_eq_true, ↓reduceIte]
    exact_mod_cast (by omega : a3Z v - -1 < 0)
  have hsp : shiftParam (move v (.inl 3) false) (.inl 3) = (v (.inl 3) : ℚ) - 1 := by
    simp only [shiftParam, move_self, Bool.false_eq_true, ↓reduceIte, Int.cast_sub, Int.cast_one]
  have hp : (v (.inl 3) : ℚ) - 1 ≠ 0 := by
    have : ((v (.inl 3) - 1 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast (show v (.inl 3) - 1 ≠ 0 by omega)
    rwa [Int.cast_sub, Int.cast_one] at this
  refine ⟨⟨by rw [a3_eq_a3Z]; exact_mod_cast (by omega : a3Z v < 0), hv',
    fun h => absurd h Bool.false_ne_true, fun _ => ⟨by rw [hsp]; exact hp, ?_⟩⟩,
    ⟨rfl, h0⟩⟩
  have hs : stepMat (move v (.inl 3) false) (.inl 3) (!false) =
      1 + (shiftParam (move v (.inl 3) false) (.inl 3))⁻¹ • Tw (move v (.inl 3) false) := by
    simp only [stepMat, isForward, Bool.not_false, ↓reduceIte]
  rw [hs, hsp]
  refine isUnit_det_step _ _ hp hv'.ne ?_
  rw [Qw_eq, eval_sub, move_false, Apol_update_inl]
  have hD : (Dpol (Function.update v (.inl 3) (v (.inl 3) - 1))).eval (-((v (.inl 3) : ℚ) - 1)) = 0 := by
    unfold Dpol
    rw [eval_prod, prod_eq_zero (mem_univ 3)]
    rw [eval_add, eval_X, eval_C, Function.update_self, Int.cast_sub, Int.cast_one]
    ring
  rw [hD, sub_zero, Apol, eval_mul, eval_X, eval_prod]
  refine mul_ne_zero (neg_ne_zero.2 hp) ?_
  rw [prod_ne_zero_iff]
  intro k _
  rw [eval_add, eval_X, eval_C]
  have : ((-(v (.inl 3) - 1) + (v (.inr k) - 1) : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast (show -(v (.inl 3) - 1) + (v (.inr k) - 1) ≠ 0 by have := hy k; omega)
  rwa [Int.cast_add, Int.cast_neg, Int.cast_sub, Int.cast_sub, Int.cast_one] at this

def vtx (x0 x1 x2 x3 y0 y1 y2 : ℤ) : Vertex := dir ![x0, x1, x2, x3] ![y0, y1, y2]

theorem box_vtx {a0 a1 a2 a3 b0 b1 b2 e0 e1 e2 e3 f0 f1 f2 : ℤ} {v : Vertex}
    (h : InBox (vtx a0 a1 a2 a3 b0 b1 b2) (vtx e0 e1 e2 e3 f0 f1 f2) v) :
    (a0 ≤ v (.inl 0) ∧ v (.inl 0) ≤ e0) ∧ (a1 ≤ v (.inl 1) ∧ v (.inl 1) ≤ e1) ∧
    (a2 ≤ v (.inl 2) ∧ v (.inl 2) ≤ e2) ∧ (e3 ≤ v (.inl 3) ∧ v (.inl 3) ≤ a3) ∧
    (b0 ≤ v (.inr 0) ∧ v (.inr 0) ≤ f0) ∧ (b1 ≤ v (.inr 1) ∧ v (.inr 1) ≤ f1) ∧
    (b2 ≤ v (.inr 2) ∧ v (.inr 2) ≤ f2) :=
  ⟨(h (.inl 0)).1 rfl, (h (.inl 1)).1 rfl, (h (.inl 2)).1 rfl, (h (.inl 3)).2 rfl,
    (h (.inr 0)).1 rfl, (h (.inr 1)).1 rfl, (h (.inr 2)).1 rfl⟩

theorem forall_fin4 (P : Fin 4 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) : ∀ k, P k := by
  intro k
  fin_cases k <;> assumption

theorem forall_fin3 (P : Fin 3 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ k, P k := by
  intro k
  fin_cases k <;> assumption

theorem vtx_eq (v : Vertex) (a0 a1 a2 a3 b0 b1 b2 : ℤ) (h0 : v (.inl 0) = a0) (h1 : v (.inl 1) = a1)
    (h2 : v (.inl 2) = a2) (h3 : v (.inl 3) = a3) (h4 : v (.inr 0) = b0) (h5 : v (.inr 1) = b1)
    (h6 : v (.inr 2) = b2) : v = vtx a0 a1 a2 a3 b0 b1 b2 := by
  funext c
  rcases c with i | i <;> fin_cases i <;> assumption

theorem a3Z_expand (v : Vertex) : a3Z v = v (.inr 0) + v (.inr 1) + v (.inr 2) - 3 -
    (v (.inl 0) + v (.inl 1) + v (.inl 2) + v (.inl 3)) := by
  simp only [a3Z, Fin.sum_univ_three, Fin.sum_univ_four]
  ring

theorem a3_neg_of (v : Vertex) (h : a3Z v < 0) : a3 v < 0 := by
  rw [a3_eq_a3Z]
  exact_mod_cast h

def blkA (t N : ℕ) : List (Coord × Bool) :=
  (List.replicate (t * N) (blockStep (dir ![1, 1, 1, 0] ![0, 0, 0]))).flatten

def blkB (N : ℕ) : List (Coord × Bool) :=
  (List.replicate N (blockStep (dir ![0, 0, 0, 0] ![2, 1, 3]))).flatten

def blkC (t N : ℕ) : List (Coord × Bool) :=
  (List.replicate N
    (blockStep (dir ![(10 : ℤ) - t, (9 : ℤ) - t, (11 : ℤ) - t, 0] ![0, 0, 0]))).flatten

def blkD (N : ℕ) : List (Coord × Bool) :=
  (List.replicate (11 * N) (blockStep (dir ![0, 0, 0, -1] ![0, 0, 0]))).flatten

theorem route_eq (t N : ℕ) : route t N = blkA t N ++ blkB N ++ blkC t N ++ blkD N := rfl

def eN (N : ℕ) : Vertex :=
  vtx (10 * N + 1) (9 * N + 1) (11 * N + 1) (-(11 * N)) (2 * N + 1) (N + 1) (3 * N + 1)

theorem w0_eq : w0 = vtx 1 1 1 0 1 1 1 := rfl

theorem endpt_A (t N : ℕ) :
    endpt w0 (blkA t N) = vtx (t * N + 1) (t * N + 1) (t * N + 1) 0 1 1 1 := by
  rw [blkA, endpt_block]
  apply vtx_eq <;>
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, w0, vtx, dir, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val] <;> omega

theorem endpt_B (N : ℕ) (U0 U1 U2 : ℤ) :
    endpt (vtx U0 U1 U2 0 1 1 1) (blkB N) = vtx U0 U1 U2 0 (2 * N + 1) (N + 1) (3 * N + 1) := by
  rw [blkB, endpt_block]
  apply vtx_eq <;>
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, w0, vtx, dir, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val] <;> omega

theorem endpt_C (t N : ℕ) :
    endpt (vtx (t * N + 1) (t * N + 1) (t * N + 1) 0 (2 * N + 1) (N + 1) (3 * N + 1)) (blkC t N) =
      vtx (10 * N + 1) (9 * N + 1) (11 * N + 1) 0 (2 * N + 1) (N + 1) (3 * N + 1) := by
  rw [blkC, endpt_block]
  apply vtx_eq <;>
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, w0, vtx, dir, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val] <;> push_cast <;> ring

theorem endpt_D (N : ℕ) :
    endpt (vtx (10 * N + 1) (9 * N + 1) (11 * N + 1) 0 (2 * N + 1) (N + 1) (3 * N + 1)) (blkD N) =
      eN N := by
  rw [blkD, endpt_block, eN]
  apply vtx_eq <;>
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, vtx, dir, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val] <;> omega

theorem allGood_A (t N : ℕ) : AllGood w0 (blkA t N) := by
  refine allGood_box _ _ (mono_block _ _ (by decide)) fun v c hb h1 h2 => ?_
  · rw [endpt_A, w0_eq] at hb
    rw [endpt_A] at h1 h2
    obtain ⟨⟨a0, e0⟩, ⟨a1, e1⟩, ⟨a2, e2⟩, ⟨a3', e3⟩, ⟨b0, f0⟩, ⟨b1, f1⟩, ⟨b2, f2⟩⟩ := box_vtx hb
    have ha : a3Z v < 0 := by rw [a3Z_expand]; omega
    rcases c with i | i <;> fin_cases i
    · exact goodR_up v 0 (by decide) a0 ha
    · exact goodR_up v 1 (by decide) a1 ha
    · exact goodR_up v 2 (by decide) a2 ha
    · have s : (0 : ℤ) < v (.inl 3) := h2 rfl
      exfalso; omega
    · have s : v (.inr 0) < 1 := h1 rfl
      exfalso; omega
    · have s : v (.inr 1) < 1 := h1 rfl
      exfalso; omega
    · have s : v (.inr 2) < 1 := h1 rfl
      exfalso; omega

theorem allGood_B (N : ℕ) (U0 U1 U2 : ℤ) (hU0 : 3 * N + 1 ≤ U0) (hU1 : 3 * N + 1 ≤ U1)
    (hU2 : 3 * N + 1 ≤ U2) : AllGood (vtx U0 U1 U2 0 1 1 1) (blkB N) := by
  refine allGood_box _ _ (mono_block _ _ (by decide)) fun v c hb h1 h2 => ?_
  · rw [endpt_B] at hb h1 h2
    obtain ⟨⟨a0, e0⟩, ⟨a1, e1⟩, ⟨a2, e2⟩, ⟨a3', e3⟩, ⟨b0, f0⟩, ⟨b1, f1⟩, ⟨b2, f2⟩⟩ := box_vtx hb
    have ha : a3Z v + 1 < 0 := by rw [a3Z_expand]; omega
    rcases c with i | i <;> fin_cases i
    · have s : v (.inl 0) < U0 := h1 rfl
      exfalso; omega
    · have s : v (.inl 1) < U1 := h1 rfl
      exfalso; omega
    · have s : v (.inl 2) < U2 := h1 rfl
      exfalso; omega
    · have s : (0 : ℤ) < v (.inl 3) := h2 rfl
      exfalso; omega
    · have s : v (.inr 0) < 2 * N + 1 := h1 rfl
      exact goodR_low v 0 b0 (forall_fin4 _ (by omega) (by omega) (by omega) (by omega)) ha
    · have s : v (.inr 1) < N + 1 := h1 rfl
      exact goodR_low v 1 b1 (forall_fin4 _ (by omega) (by omega) (by omega) (by omega)) ha
    · have s : v (.inr 2) < 3 * N + 1 := h1 rfl
      exact goodR_low v 2 b2 (forall_fin4 _ (by omega) (by omega) (by omega) (by omega)) ha

theorem allGood_C (t N : ℕ) (ht : t = 3 ∨ t = 4) :
    AllGood (vtx (t * N + 1) (t * N + 1) (t * N + 1) 0 (2 * N + 1) (N + 1) (3 * N + 1))
      (blkC t N) := by
  refine allGood_box _ _ (mono_block _ _ (by rcases ht with rfl | rfl <;> decide))
    fun v c hb h1 h2 => ?_
  · rw [endpt_C] at hb h1 h2
    obtain ⟨⟨a0, e0⟩, ⟨a1, e1⟩, ⟨a2, e2⟩, ⟨a3', e3⟩, ⟨b0, f0⟩, ⟨b1, f1⟩, ⟨b2, f2⟩⟩ := box_vtx hb
    have hx : (2 * N : ℤ) ≤ t * N := by
      rcases ht with rfl | rfl <;> omega
    have ha : a3Z v < 0 := by
      rw [a3Z_expand]
      omega
    rcases c with i | i <;> fin_cases i
    · exact goodR_up v 0 (by decide) (by omega) ha
    · exact goodR_up v 1 (by decide) (by omega) ha
    · exact goodR_up v 2 (by decide) (by omega) ha
    · have s : (0 : ℤ) < v (.inl 3) := h2 rfl
      exfalso; omega
    · have s : v (.inr 0) < 2 * N + 1 := h1 rfl
      exfalso; omega
    · have s : v (.inr 1) < N + 1 := h1 rfl
      exfalso; omega
    · have s : v (.inr 2) < 3 * N + 1 := h1 rfl
      exfalso; omega

theorem allGood_D (N : ℕ) :
    AllGood (vtx (10 * N + 1) (9 * N + 1) (11 * N + 1) 0 (2 * N + 1) (N + 1) (3 * N + 1))
      (blkD N) := by
  refine allGood_box _ _ (mono_block _ _ (by decide)) fun v c hb h1 h2 => ?_
  · rw [endpt_D, eN] at hb h1 h2
    obtain ⟨⟨a0, e0⟩, ⟨a1, e1⟩, ⟨a2, e2⟩, ⟨a3', e3⟩, ⟨b0, f0⟩, ⟨b1, f1⟩, ⟨b2, f2⟩⟩ := box_vtx hb
    have ha : a3Z v + 1 < 0 := by rw [a3Z_expand]; omega
    rcases c with i | i <;> fin_cases i
    · have s : v (.inl 0) < 10 * N + 1 := h1 rfl
      exfalso; omega
    · have s : v (.inl 1) < 9 * N + 1 := h1 rfl
      exfalso; omega
    · have s : v (.inl 2) < 11 * N + 1 := h1 rfl
      exfalso; omega
    · exact goodR_x3 v e3 (forall_fin3 _ (by omega) (by omega) (by omega)) ha
    · have s : v (.inr 0) < 2 * N + 1 := h1 rfl
      exfalso; omega
    · have s : v (.inr 1) < N + 1 := h1 rfl
      exfalso; omega
    · have s : v (.inr 2) < 3 * N + 1 := h1 rfl
      exfalso; omega

theorem allGood_route (t N : ℕ) (ht : t = 3 ∨ t = 4) : AllGood w0 (route t N) := by
  rw [route_eq]
  refine allGood_append _ _ _ (allGood_append _ _ _ (allGood_append _ _ _ (allGood_A t N) ?_) ?_) ?_
  · rw [endpt_A]
    exact allGood_B N _ _ _ (by rcases ht with rfl | rfl <;> push_cast <;> omega)
      (by rcases ht with rfl | rfl <;> push_cast <;> omega)
      (by rcases ht with rfl | rfl <;> push_cast <;> omega)
  · rw [endpt_append, endpt_A, endpt_B]
    exact allGood_C t N ht
  · rw [endpt_append, endpt_append, endpt_A, endpt_B, endpt_C]
    exact allGood_D N

theorem endpt_route (t N : ℕ) : endpt w0 (route t N) = eN N := by
  rw [route_eq, endpt_append, endpt_append, endpt_append, endpt_A, endpt_B, endpt_C, endpt_D]

theorem U_one : U 1 = 1 := by
  rw [U, show (1 : ℤ).toNat = 1 from rfl, Ico_self, prod_empty]

theorem Xi_zero : Xi 0 = 1 := by
  rw [Xi, show (1 - (0 : ℤ)).toNat = 1 from rfl, Ico_self, prod_empty]

theorem Th_w0 : Th w0 = 1 := by
  rw [Th, Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_three,
    show phT (.inl 0) (w0 (.inl 0)) = U 1 from rfl, show phT (.inl 1) (w0 (.inl 1)) = U 1 from rfl,
    show phT (.inl 2) (w0 (.inl 2)) = U 1 from rfl, show phT (.inl 3) (w0 (.inl 3)) = 1 from rfl,
    show phT (.inr 0) (w0 (.inr 0)) = 1 from rfl, show phT (.inr 1) (w0 (.inr 1)) = 1 from rfl,
    show phT (.inr 2) (w0 (.inr 2)) = 1 from rfl, U_one]
  simp only [mul_one]

theorem Pp_w0 : Pp w0 = 1 := by
  rw [Pp, Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_three,
    show phP (.inl 0) (w0 (.inl 0)) = 1 from rfl, show phP (.inl 1) (w0 (.inl 1)) = 1 from rfl,
    show phP (.inl 2) (w0 (.inl 2)) = 1 from rfl, show phP (.inl 3) (w0 (.inl 3)) = Xi 0 from rfl,
    show phP (.inr 0) (w0 (.inr 0)) = U 1 from rfl, show phP (.inr 1) (w0 (.inr 1)) = U 1 from rfl,
    show phP (.inr 2) (w0 (.inr 2)) = U 1 from rfl, U_one, Xi_zero]
  simp only [mul_one]

def cpr (N : ℕ) : Vertex := vtx (10 * N + 1) (9 * N + 1) (11 * N + 1) 0 1 1 1

theorem Pp_cpr (N : ℕ) : Pp (cpr N) = 1 := by
  rw [Pp, Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_three,
    show phP (.inl 0) (cpr N (.inl 0)) = 1 from rfl, show phP (.inl 1) (cpr N (.inl 1)) = 1 from rfl,
    show phP (.inl 2) (cpr N (.inl 2)) = 1 from rfl,
    show phP (.inl 3) (cpr N (.inl 3)) = Xi 0 from rfl,
    show phP (.inr 0) (cpr N (.inr 0)) = U 1 from rfl,
    show phP (.inr 1) (cpr N (.inr 1)) = U 1 from rfl,
    show phP (.inr 2) (cpr N (.inr 2)) = U 1 from rfl, U_one, Xi_zero]
  simp only [mul_one]

theorem rep_route (t N : ℕ) (ht : t = 3 ∨ t = 4) :
    Rep (walk w0 (route t N)) w0 (eN N) (Pp (eN N)) (Th (eN N)) := by
  have h := rep_walk _ _ (allGood_route t N ht)
  obtain ⟨hT, hP⟩ := pot_walk _ _ (allGood_route t N ht)
  rw [endpt_route] at h hT hP
  rw [Th_w0, one_mul] at hT
  rw [Pp_w0, one_mul] at hP
  rw [hT, hP]
  exact h

theorem allGood_Z (N : ℕ) : AllGood (cpr N) (blkB N ++ blkD N) := by
  refine allGood_append _ _ _ (allGood_B N _ _ _ (by omega) (by omega) (by omega)) ?_
  rw [cpr, endpt_B]
  exact allGood_D N

theorem inv_Z (N : ℕ) : ∀ x ∈ blkB N ++ blkD N, isForward x.1 x.2 = false := by
  rintro ⟨c, up⟩ hx
  rcases List.mem_append.1 hx with hx | hx
  · obtain ⟨h1, h2⟩ := mem_block _ _ _ hx
    exact (by decide : ∀ (c : Coord) (up : Bool), dir ![0, 0, 0, 0] ![2, 1, 3] c ≠ 0 →
      up = decide (0 ≤ dir ![0, 0, 0, 0] ![2, 1, 3] c) → isForward c up = false) c up h1 h2
  · obtain ⟨h1, h2⟩ := mem_block _ _ _ hx
    exact (by decide : ∀ (c : Coord) (up : Bool), dir ![0, 0, 0, -1] ![0, 0, 0] c ≠ 0 →
      up = decide (0 ≤ dir ![0, 0, 0, -1] ![0, 0, 0] c) → isForward c up = false) c up h1 h2

theorem a3_eN (N : ℕ) : a3 (eN N) < 0 :=
  a3_neg_of _ (by
    rw [a3Z_expand]
    show (2 * (N : ℤ) + 1) + (N + 1) + (3 * N + 1) - 3 -
      ((10 * N + 1) + (9 * N + 1) + (11 * N + 1) + -(11 * N)) < 0
    omega)

theorem a3_w0 : a3 w0 < 0 := a3_neg_of _ (by rw [a3Z_expand]; decide)

theorem a3_cpr (N : ℕ) : a3 (cpr N) < 0 :=
  a3_neg_of _ (by
    rw [a3Z_expand]
    show (1 : ℤ) + 1 + 1 - 3 - ((10 * N + 1) + (9 * N + 1) + (11 * N + 1) + 0) < 0
    omega)

theorem surj_eN (N : ℕ) (z : Fin 3 → ℚ) : ∃ g, red (eN N) (Pp (eN N) * g) = z := by
  have hall := allGood_Z N
  have hrep := rep_walk _ _ hall
  obtain ⟨-, hP⟩ := pot_walk _ _ hall
  have he : endpt (cpr N) (blkB N ++ blkD N) = eN N := by
    rw [endpt_append, cpr, endpt_B, endpt_D]
  rw [he] at hrep hP
  rw [Pp_cpr, one_mul] at hP
  rw [← hP, Qfac_inv _ _ (inv_Z N)] at hrep
  have hdet := det_walk _ _ hall (inv_Z N)
  set Z := walk (cpr N) (blkB N ++ blkD N)
  refine ⟨polyOf (Z *ᵥ z), ?_⟩
  have h1 := hrep (polyOf (Z *ᵥ z))
  rw [one_mul, red_polyOf _ (a3_cpr N)] at h1
  have h2 := congrArg (fun y => Z⁻¹ *ᵥ y) h1
  simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec] at h2
  exact h2

theorem mat_eq_of_mulVec {n : ℕ} (M M' : Matrix (Fin n) (Fin 3) ℚ)
    (h : ∀ z, M *ᵥ z = M' *ᵥ z) : M = M' := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  rwa [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at this

theorem route_independent (N : ℕ) : walk w0 (route 3 N) = walk w0 (route 4 N) := by
  refine mat_eq_of_mulVec _ _ fun z => ?_
  obtain ⟨g, rfl⟩ := surj_eN N z
  rw [rep_route 3 N (Or.inl rfl) g, rep_route 4 N (Or.inr rfl) g]

def dl (h : ℕ) (P : ℚ[X]) (x : ℚ) : ℚ :=
  ∑ i ∈ range (h + 1), (-1) ^ (h - i) * (h.choose i : ℚ) * P.eval ((i : ℚ) + x)

theorem dl_eq_fwdDiff (h : ℕ) (P : ℚ[X]) (x : ℚ) :
    dl h P x = (fwdDiff 1)^[h] (fun y => P.eval y) x := by
  rw [fwdDiff_iter_eq_sum_shift, dl]
  refine sum_congr rfl fun i _ => ?_
  rw [zsmul_eq_mul, nsmul_eq_mul, mul_one, add_comm x, Int.cast_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one, Int.cast_natCast]

theorem dl_zero_of_lt (h : ℕ) (P : ℚ[X]) (x : ℚ) (hP : P.natDegree < h) : dl h P x = 0 := by
  rw [dl_eq_fwdDiff, Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hP]
  rfl

theorem dl_add (h : ℕ) (P Q : ℚ[X]) (x : ℚ) : dl h (P + Q) x = dl h P x + dl h Q x := by
  simp only [dl, eval_add, mul_add, sum_add_distrib]

theorem dl_C_mul (h : ℕ) (c : ℚ) (P : ℚ[X]) (x : ℚ) : dl h (C c * P) x = c * dl h P x := by
  simp only [dl, eval_mul, eval_C, mul_sum]
  exact sum_congr rfl fun i _ => mul_left_comm _ _ _

def Jsum (B η : ℕ) (P : ℚ[X]) : ℚ :=
  ∑ h ∈ range B, (-1) ^ h / ((h : ℚ) + 1) * dl h P (-(η : ℚ))

theorem Jfun_eq (η : ℕ) (P : ℚ[X]) (B : ℕ) (hB : P.natDegree < B) : Jfun η P = Jsum B η P := by
  have h1 : Jfun η P = Jsum (P.natDegree + 1) η P := by
    refine sum_congr rfl fun h _ => ?_
    congr 1
    exact sum_congr rfl fun i _ => by rw [sub_eq_add_neg]
  rw [h1, Jsum, Jsum, ← sum_range_add_sum_Ico _ (show P.natDegree + 1 ≤ B by omega)]
  refine (add_eq_left.mpr (sum_eq_zero fun h hh => ?_)).symm
  rw [dl_zero_of_lt _ _ _ (by have := (mem_Ico.1 hh).1; omega), mul_zero]

theorem Jfun_add (η : ℕ) (P Q : ℚ[X]) : Jfun η (P + Q) = Jfun η P + Jfun η Q := by
  have hPQ := natDegree_add_le P Q
  rw [Jfun_eq η (P + Q) (P.natDegree + Q.natDegree + 1) (by omega),
    Jfun_eq η P (P.natDegree + Q.natDegree + 1) (by omega),
    Jfun_eq η Q (P.natDegree + Q.natDegree + 1) (by omega)]
  simp only [Jsum, dl_add, mul_add, sum_add_distrib]

theorem Jfun_C_mul (η : ℕ) (c : ℚ) (P : ℚ[X]) : Jfun η (C c * P) = c * Jfun η P := by
  rw [Jfun_eq η (C c * P) (P.natDegree + 1) ((natDegree_C_mul_le c P).trans_lt (by omega)),
    Jfun_eq η P (P.natDegree + 1) (by omega)]
  simp only [Jsum, dl_C_mul, mul_sum]
  exact sum_congr rfl fun i _ => mul_left_comm _ _ _

theorem Jfun_neg (η : ℕ) (P : ℚ[X]) : Jfun η (-P) = -Jfun η P := by
  rw [neg_eq_neg_one_mul P, ← C_1, ← C_neg, Jfun_C_mul, neg_one_mul]

theorem Jfun_sub (η : ℕ) (P Q : ℚ[X]) : Jfun η (P - Q) = Jfun η P - Jfun η Q := by
  rw [sub_eq_add_neg, Jfun_add, Jfun_neg, ← sub_eq_add_neg]

def bin (k : ℕ) : ℚ[X] := C ((k.factorial : ℚ)⁻¹) * descPochhammer ℚ k

theorem bin_eval_nat (k n : ℕ) : (bin k).eval (n : ℚ) = (n.choose k : ℚ) := by
  rw [bin, eval_mul, eval_C, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  exact inv_mul_cancel_left₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)) _

theorem desc_eval_neg_one (k : ℕ) :
    (descPochhammer ℚ k).eval (-1) = (-1) ^ k * (k.factorial : ℚ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [descPochhammer_succ_right, eval_mul, ih, eval_sub, eval_X, eval_natCast,
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ]
    ring

theorem bin_deriv_zero (k : ℕ) :
    (bin (k + 1)).derivative.eval 0 = (-1) ^ k / ((k : ℚ) + 1) := by
  rw [bin, derivative_C_mul, eval_mul, eval_C, descPochhammer_succ_left, derivative_mul,
    derivative_X, one_mul, eval_add, eval_mul, eval_X, zero_mul, add_zero, eval_comp, eval_sub,
    eval_X, eval_one, zero_sub, desc_eval_neg_one, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_succ, mul_inv]
  have hk : ((k.factorial : ℕ) : ℚ)⁻¹ * (k.factorial : ℚ) = 1 :=
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k))
  linear_combination ((-1 : ℚ) ^ k * ((k : ℚ) + 1)⁻¹) * hk

theorem newton (P : ℚ[X]) (x : ℚ) (B : ℕ) (hB : P.natDegree < B) :
    P.comp (X + C x) = ∑ k ∈ range B, C (dl k P x) * bin k := by
  apply eq_of_infinite_eval_eq
  apply Set.Infinite.mono _ (Set.infinite_range_of_injective (Nat.cast_injective (R := ℚ)))
  rintro _ ⟨n, rfl⟩
  show (P.comp (X + C x)).eval (n : ℚ) = (∑ k ∈ range B, C (dl k P x) * bin k).eval (n : ℚ)
  simp only [eval_comp, eval_add, eval_X, eval_C, eval_finsetSum, eval_mul,
    bin_eval_nat]
  have h1 := shift_eq_sum_fwdDiff_iter (1 : ℚ) (fun y => P.eval y) n x
  rw [nsmul_eq_mul, mul_one, add_comm x] at h1
  rw [h1]
  rw [sum_subset (s₂ := range (n + 1 + B)) (by intro k hk; simp at hk ⊢; omega)
      (fun k _ hk => by rw [Nat.choose_eq_zero_of_lt (by simpa using hk), zero_smul]),
    sum_subset (s₁ := range B) (s₂ := range (n + 1 + B)) (by intro k hk; simp at hk ⊢; omega)
      (fun k _ hk => by rw [dl_zero_of_lt _ _ _ (by simp at hk; omega), zero_mul])]
  refine sum_congr rfl fun k _ => ?_
  rw [nsmul_eq_mul, dl_eq_fwdDiff, mul_comm]

theorem deriv_eq (P : ℚ[X]) (x : ℚ) (B : ℕ) (hB : P.natDegree < B + 1) :
    P.derivative.eval x = ∑ h ∈ range B, (-1) ^ h / ((h : ℚ) + 1) * dl (h + 1) P x := by
  have hN := congrArg (fun q => q.derivative.eval 0) (newton P x (B + 1) hB)
  simp only [derivative_comp, derivative_add, derivative_X, derivative_C, add_zero, one_mul,
    eval_comp, eval_add, eval_X, eval_C, zero_add, derivative_sum, derivative_C_mul,
    eval_finsetSum, eval_mul] at hN
  rw [hN, sum_range_succ']
  have h0 : (bin 0).derivative.eval 0 = 0 := by simp [bin]
  rw [h0, mul_zero, add_zero]
  exact sum_congr rfl fun h _ => by rw [bin_deriv_zero]; ring

theorem J_delta (η : ℕ) (P : ℚ[X]) :
    Jfun η (taylor 1 P - P) = P.derivative.eval (-(η : ℚ)) := by
  have hd : (taylor 1 P - P).natDegree < P.natDegree + 1 :=
    lt_of_le_of_lt (natDegree_sub_le _ _) (by rw [natDegree_taylor, max_self]; omega)
  rw [Jfun_eq η _ _ hd, Jsum, deriv_eq P _ (P.natDegree + 1) (by omega)]
  refine sum_congr rfl fun h _ => ?_
  congr 1
  have hf : (fun y => eval y (taylor 1 P - P)) = fwdDiff 1 (fun y => eval y P) := by
    funext y
    simp only [eval_sub, taylor_eval, fwdDiff]
  rw [dl_eq_fwdDiff, dl_eq_fwdDiff, Function.iterate_succ_apply, hf]

theorem J_succ (η : ℕ) (P : ℚ[X]) : Jfun (η + 1) P = Jfun η (taylor (-1) P) := by
  unfold Jfun
  rw [natDegree_taylor]
  refine sum_congr rfl fun h _ => ?_
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [taylor_eval, Nat.cast_succ]
  congr 2
  ring

theorem J_shift (η : ℕ) (P : ℚ[X]) :
    Jfun (η + 1) P - Jfun η P = -P.derivative.eval (-(η : ℚ) - 1) := by
  rw [J_succ, ← Jfun_sub]
  have h : taylor (-1) P - P = -(taylor 1 (taylor (-1) P) - taylor (-1) P) := by
    rw [taylor_taylor, add_neg_cancel, taylor_zero]
    ring
  rw [h, Jfun_neg, J_delta, taylor_apply, derivative_comp, derivative_add, derivative_X,
    derivative_C, add_zero, one_mul, eval_comp, eval_add, eval_X, eval_C]
  congr 3
  ring

def DD (p : ℚ[X]) (a : ℚ) : ℚ[X] := (p - C (p.eval a)) /ₘ (X - C a)

theorem DD_spec (p : ℚ[X]) (a : ℚ) : (X - C a) * DD p a = p - C (p.eval a) :=
  mul_divByMonic_eq_iff_isRoot.mpr (by simp [IsRoot])

theorem DD_unique (p : ℚ[X]) (a : ℚ) (q : ℚ[X]) (h : (X - C a) * q = p - C (p.eval a)) :
    DD p a = q :=
  mul_left_cancel₀ (X_sub_C_ne_zero a) ((DD_spec p a).trans h.symm)

theorem DD_add (p q : ℚ[X]) (a : ℚ) : DD (p + q) a = DD p a + DD q a :=
  DD_unique _ _ _ (by rw [mul_add, DD_spec, DD_spec, eval_add, C_add]; ring)

theorem DD_C_mul (c : ℚ) (p : ℚ[X]) (a : ℚ) : DD (C c * p) a = C c * DD p a :=
  DD_unique _ _ _ (by rw [mul_left_comm, DD_spec, eval_mul, eval_C, C_mul]; ring)

theorem DD_eval (p : ℚ[X]) (a s : ℚ) (h : s ≠ a) :
    (DD p a).eval s = (p.eval s - p.eval a) / (s - a) := by
  have h1 := congrArg (eval s) (DD_spec p a)
  simp only [eval_mul, eval_sub, eval_X, eval_C] at h1
  rw [eq_div_iff (sub_ne_zero.2 h), ← h1]
  ring

theorem DD_deriv (p : ℚ[X]) (a b : ℚ) (hb : (X + C b) ^ 2 ∣ p) (hab : a + b ≠ 0) :
    (DD p a).derivative.eval (-b) = p.eval a / (a + b) ^ 2 := by
  obtain ⟨r, hr⟩ := hb
  have hs := DD_spec p a
  have hd := congrArg derivative hs
  rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
    derivative_sub, derivative_C, sub_zero] at hd
  have e1 := congrArg (eval (-b)) hs
  have e2 := congrArg (eval (-b)) hd
  have hp0 : p.eval (-b) = 0 := by rw [hr]; simp
  have hX : (X + C b).eval (-b) = 0 := by rw [eval_add, eval_X, eval_C, neg_add_cancel]
  have hp1 : p.derivative.eval (-b) = 0 := by
    rw [hr, pow_two, mul_assoc, derivative_mul, eval_add, eval_mul, eval_mul, eval_mul, hX, zero_mul,
      mul_zero, zero_mul, add_zero]
  simp only [eval_mul, eval_sub, eval_X, eval_C, eval_add, hp0, hp1] at e1 e2
  have hq0 : (DD p a).eval (-b) = p.eval a / (a + b) := by
    rw [eq_div_iff hab]
    linear_combination -e1
  have hq1 : (DD p a).derivative.eval (-b) = (DD p a).eval (-b) / (a + b) := by
    rw [eq_div_iff hab]
    linear_combination -e2
  rw [hq1, hq0, div_div, ← pow_two]

def om (m j : ℕ) : ℚ := (-1) ^ j * (m.choose j : ℚ)

def Sm (m : ℕ) (p : ℚ[X]) : ℚ[X] := ∑ j ∈ range (m + 1), om m j • DD p j

def Phi (m η : ℕ) (p : ℚ[X]) : Fin 2 → ℚ :=
  ![∑ j ∈ range (m + 1), om m j * p.eval (j : ℚ) * harm2 (j + η) + Jfun η (Sm m p),
    ∑ j ∈ range (m + 1), om m j * p.eval (j : ℚ)]

theorem Sm_add (m : ℕ) (p q : ℚ[X]) : Sm m (p + q) = Sm m p + Sm m q := by
  simp only [Sm, DD_add, smul_add, sum_add_distrib]

theorem Sm_C_mul (m : ℕ) (c : ℚ) (p : ℚ[X]) : Sm m (C c * p) = C c * Sm m p := by
  simp only [Sm, DD_C_mul, mul_sum, smul_eq_C_mul]
  exact sum_congr rfl fun j _ => by ring

theorem Phi_add (m η : ℕ) (p q : ℚ[X]) : Phi m η (p + q) = Phi m η p + Phi m η q := by
  funext i
  fin_cases i
  · simp only [Phi, Sm_add, Jfun_add, eval_add, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
      Pi.add_apply, mul_add, add_mul, sum_add_distrib]
    ring
  · simp only [Phi, eval_add, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Pi.add_apply, mul_add, sum_add_distrib]

theorem Phi_C_mul (m η : ℕ) (c : ℚ) (p : ℚ[X]) : Phi m η (C c * p) = c • Phi m η p := by
  funext i
  fin_cases i
  · simp only [Phi, Sm_C_mul, Jfun_C_mul, eval_mul, eval_C, Fin.zero_eta, Fin.isValue,
      Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul, mul_add, mul_sum]
    congr 1
    exact sum_congr rfl fun j _ => by ring
  · simp only [Phi, eval_mul, eval_C, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Pi.smul_apply, smul_eq_mul, mul_sum]
    exact sum_congr rfl fun j _ => by ring

theorem Phi_sub (m η : ℕ) (p q : ℚ[X]) : Phi m η (p - q) = Phi m η p - Phi m η q := by
  rw [sub_eq_add_neg, neg_eq_neg_one_mul q, ← C_1, ← C_neg, Phi_add, Phi_C_mul, neg_one_smul,
    ← sub_eq_add_neg]

theorem om_succ_mul (m j : ℕ) : om m (j + 1) * ((j : ℚ) + 1) = om m j * ((j : ℚ) - m) := by
  unfold om
  by_cases hj : j ≤ m
  · have h := Nat.choose_succ_right_eq m j
    have hq : ((m.choose (j + 1) : ℕ) : ℚ) * ((j : ℚ) + 1) = (m.choose j : ℚ) * ((m : ℚ) - j) := by
      have := congrArg (fun n : ℕ => (n : ℚ)) h
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hj] at this
      exact this
    rw [pow_succ]
    linear_combination (-(-1 : ℚ) ^ j) * hq
  · rw [Nat.choose_eq_zero_of_lt (by omega : m < j), Nat.choose_eq_zero_of_lt (by omega : m < j + 1),
      Nat.cast_zero, mul_zero, zero_mul, mul_zero, zero_mul]

theorem om_red (m j : ℕ) (hj : j ≤ m + 1) :
    om (m + 1) j * (1 - (j : ℚ) / ((m : ℚ) + 1)) = om m j := by
  unfold om
  have h := Nat.choose_mul_succ_eq m j
  have hq : (m.choose j : ℚ) * ((m : ℚ) + 1) = ((m + 1).choose j : ℚ) * ((m : ℚ) + 1 - j) := by
    have := congrArg (fun n : ℕ => (n : ℚ)) h
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hj] at this
    exact this
  have hm1 : ((m : ℚ) + 1) * ((m : ℚ) + 1)⁻¹ = 1 := mul_inv_cancel₀ (Nat.cast_add_one_ne_zero m)
  rw [div_eq_mul_inv]
  linear_combination (-(-1 : ℚ) ^ j * ((m : ℚ) + 1)⁻¹) * hq +
    (-(-1 : ℚ) ^ j * (((m + 1).choose j : ℕ) - (m.choose j : ℚ))) * hm1

theorem alt_sum (m : ℕ) : ∑ j ∈ range (m + 2), om (m + 1) j = 0 := by
  have h := Int.alternating_sum_range_choose (n := m + 1)
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte] at h
  have := congrArg (fun z : ℤ => (z : ℚ)) h
  push_cast at this
  exact this

theorem Phi_mred (m η : ℕ) (p : ℚ[X]) :
    Phi (m + 1) η ((1 - C ((m : ℚ) + 1)⁻¹ * X) * p) = Phi m η p := by
  set k : ℚ := ((m : ℚ) + 1)⁻¹ with hk
  have hk1 : k * ((m : ℚ) + 1) = 1 := inv_mul_cancel₀ (Nat.cast_add_one_ne_zero m)
  have hw : ∀ w : ℕ → ℚ, ∑ j ∈ range (m + 1 + 1), om (m + 1) j *
      ((1 - C k * X) * p).eval (j : ℚ) * w j = ∑ j ∈ range (m + 1), om m j * p.eval (j : ℚ) * w j := by
    intro w
    rw [sum_range_succ]
    have hl : ((1 - C k * X) * p).eval (((m + 1 : ℕ) : ℚ)) = 0 := by
      rw [eval_mul, eval_sub, eval_one, eval_mul, eval_C, eval_X]
      push_cast
      rw [hk1, sub_self, zero_mul]
    rw [hl, mul_zero, zero_mul, add_zero]
    refine sum_congr rfl fun j hj => ?_
    rw [← om_red m j (by have := mem_range.1 hj; omega), eval_mul, eval_sub, eval_one, eval_mul,
      eval_C, eval_X, hk]
    ring
  have hDD : ∀ j : ℕ, DD ((1 - C k * X) * p) j = C (1 - k * j) * DD p j - C k * p := by
    intro j
    refine DD_unique _ _ _ ?_
    have hs := DD_spec p j
    have hc : C (1 - k * j) = 1 - C k * C (j : ℚ) := by rw [C_sub, C_1, C_mul]
    rw [eval_mul, eval_sub, eval_one, eval_mul, eval_C, eval_X, C_mul, hc]
    linear_combination (1 - C k * C (j : ℚ)) * hs
  have hS : Sm (m + 1) ((1 - C k * X) * p) = Sm m p := by
    rw [Sm, Sm]
    simp only [hDD, smul_eq_C_mul, mul_sub, sum_sub_distrib]
    have e1 : ∑ j ∈ range (m + 1 + 1), C (om (m + 1) j) * (C (1 - k * j) * DD p j) =
        ∑ j ∈ range (m + 1), C (om m j) * DD p j := by
      rw [sum_range_succ]
      have hl : (1 : ℚ) - k * ((m + 1 : ℕ) : ℚ) = 0 := by push_cast; linear_combination -hk1
      rw [hl, C_0, zero_mul, mul_zero, add_zero]
      refine sum_congr rfl fun j hj => ?_
      rw [← mul_assoc, ← C_mul, ← om_red m j (by have := mem_range.1 hj; omega), hk, div_eq_inv_mul]
    have e2 : ∑ j ∈ range (m + 1 + 1), C (om (m + 1) j) * (C k * p) = 0 := by
      rw [← sum_mul, ← map_sum C, alt_sum, C_0, zero_mul]
    rw [e1, e2, sub_zero]
  funext i
  fin_cases i
  · simp only [Phi, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [hS, hw]
  · simp only [Phi, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have := hw (fun _ => 1)
    simp only [mul_one] at this
    exact this

theorem Xi_neg_succ (m : ℕ) :
    Xi (-(((m + 1 : ℕ) : ℤ))) = Xi (-(m : ℤ)) * (1 - C ((m : ℚ) + 1)⁻¹ * X) := by
  rw [show (-(((m + 1 : ℕ) : ℤ))) = -(m : ℤ) - 1 by omega, Xi_pred _ (by omega)]
  congr 2
  rw [show (((-(m : ℤ) - 1 : ℤ)) : ℚ)⁻¹ = -((m : ℚ) + 1)⁻¹ by
    rw [Int.cast_sub, Int.cast_neg, Int.cast_natCast, Int.cast_one, ← neg_add', inv_neg],
    C_neg, neg_mul]

theorem Phi_Xi (η : ℕ) (p : ℚ[X]) : ∀ m : ℕ, Phi m η (Xi (-(m : ℤ)) * p) = Phi 0 η p
  | 0 => by
    have : Xi (-((0 : ℕ) : ℤ)) = 1 := by simp [Xi]
    rw [this, one_mul]
  | m + 1 => by
    rw [Xi_neg_succ, mul_comm (Xi _), mul_assoc, Phi_mred, Phi_Xi η p m]

theorem harm2_succ (n : ℕ) : harm2 (n + 1) = harm2 n + 1 / ((n : ℚ) + 1) ^ 2 := by
  rw [harm2, harm2, sum_Icc_succ_top (by omega), Nat.cast_succ]

theorem Phi0_shift (η : ℕ) (p : ℚ[X]) (hp : (X + C ((η : ℚ) + 1)) ^ 2 ∣ p) :
    Phi 0 (η + 1) p = Phi 0 η p := by
  have hS : Sm 0 p = DD p 0 := by simp [Sm, om]
  have hJ := J_shift η (DD p 0)
  have hD := DD_deriv p 0 ((η : ℚ) + 1) hp (by rw [zero_add]; exact Nat.cast_add_one_ne_zero η)
  rw [show -(η : ℚ) - 1 = -((η : ℚ) + 1) by ring, hD, zero_add] at hJ
  have hH := harm2_succ η
  funext i
  fin_cases i
  · simp only [Phi, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, sum_range_one, hS, zero_add,
      Nat.cast_zero]
    rw [show η + 1 = η + 1 from rfl, hH]
    have : om 0 0 = 1 := by simp [om]
    rw [this]
    linear_combination hJ
  · simp only [Phi, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]

theorem Phi0_shift_iter (p : ℚ[X]) : ∀ η : ℕ,
    (∀ k : ℕ, 1 ≤ k → k ≤ η → (X + C (k : ℚ)) ^ 2 ∣ p) → Phi 0 η p = Phi 0 0 p
  | 0, _ => rfl
  | η + 1, h => by
    rw [Phi0_shift η p (by have := h (η + 1) (by omega) le_rfl; push_cast at this; exact this),
      Phi0_shift_iter p η fun k h1 h2 => h k h1 (by omega)]

theorem tele (u : ℕ → ℚ) (η : ℕ) (h0 : u 0 = 0) : ∀ m : ℕ,
    ∑ j ∈ range (m + 1), (u j - u (j + 1)) * harm2 (j + η) =
      ∑ j ∈ range (m + 1), u j / ((j : ℚ) + η) ^ 2 - u (m + 1) * harm2 (m + η)
  | 0 => by simp [h0]
  | m + 1 => by
    rw [sum_range_succ (fun j => (u j - u (j + 1)) * harm2 (j + η)) (m + 1), tele u η h0 m,
      sum_range_succ (fun j => u j / ((j : ℚ) + η) ^ 2) (m + 1),
      show m + 1 + η = (m + η) + 1 by omega, harm2_succ]
    push_cast
    ring

theorem Lsum_id (m : ℕ) (s : ℚ) (hs : (m : ℚ) < s) :
    (s + 1) * ∑ j ∈ range (m + 1), om m j / (s + 1 - j) =
      (s - m) * ∑ j ∈ range (m + 1), om m j / (s - j) := by
  have hjm : ∀ j ∈ range (m + 1), (j : ℚ) < s := fun j hj =>
    (Nat.cast_le.2 (Nat.lt_succ_iff.1 (mem_range.1 hj))).trans_lt hs
  have hne : ∀ j ∈ range (m + 1), s - (j : ℚ) ≠ 0 := fun j hj => sub_ne_zero.2 (hjm j hj).ne'
  have hne' : ∀ j ∈ range (m + 1), s + 1 - (j : ℚ) ≠ 0 := fun j hj =>
    sub_ne_zero.2 ((hjm j hj).trans (lt_add_one s)).ne'
  have h1 : (s + 1) * ∑ j ∈ range (m + 1), om m j / (s + 1 - j) =
      ∑ j ∈ range (m + 1), om m j + ∑ j ∈ range (m + 1), om m j * j / (s + 1 - j) := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun j hj => ?_
    rw [mul_div_assoc', add_div' _ _ _ (hne' j hj)]
    congr 1
    ring
  have h2 : ∑ j ∈ range (m + 1), om m j * j / (s + 1 - j) =
      ∑ j ∈ range (m + 1), om m j * ((j : ℚ) - m) / (s - j) := by
    rw [sum_range_succ', sum_range_succ]
    simp only [Nat.cast_zero, mul_zero, zero_div, add_zero, sub_self]
    refine sum_congr rfl fun j _ => ?_
    push_cast
    rw [om_succ_mul, show s + 1 - ((j : ℚ) + 1) = s - j by ring]
  have h3 : ∑ j ∈ range (m + 1), om m j * ((j : ℚ) - m) / (s - j) =
      (s - m) * ∑ j ∈ range (m + 1), om m j / (s - j) - ∑ j ∈ range (m + 1), om m j := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun j hj => ?_
    rw [eq_sub_iff_add_eq, div_add' _ _ _ (hne j hj), mul_div_assoc']
    congr 1
    ring
  rw [h1, h2, h3]
  ring

theorem Sm_eval (m : ℕ) (p : ℚ[X]) (s : ℚ) (hs : (m : ℚ) < s) :
    (Sm m p).eval s = p.eval s * ∑ j ∈ range (m + 1), om m j / (s - j) -
      ∑ j ∈ range (m + 1), om m j * p.eval (j : ℚ) / (s - j) := by
  rw [Sm, eval_finsetSum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun j hj => ?_
  have : (j : ℚ) < s := (Nat.cast_le.2 (Nat.lt_succ_iff.1 (mem_range.1 hj))).trans_lt hs
  rw [eval_smul, DD_eval _ _ _ this.ne', smul_eq_mul]
  ring

theorem mul3_mul3 {M : Type*} [CommMonoid M] (a1 a2 a3 b1 b2 b3 : M) :
    a1 * a2 * a3 * (b1 * b2 * b3) = a1 * b1 * (a2 * b2) * (a3 * b3) := by
  rw [mul_mul_mul_comm, mul_mul_mul_comm a1]

theorem Sm_sub (m : ℕ) (p q : ℚ[X]) : Sm m (p - q) = Sm m p - Sm m q := by
  rw [sub_eq_add_neg, neg_eq_neg_one_mul, ← C_1, ← C_neg, Sm_add, Sm_C_mul, C_neg, C_1]
  ring

theorem ann_gen (v : Vertex) (m η : ℕ) (F : ℚ[X]) (hm : v (.inl 3) = -(m : ℤ))
    (hK : ∀ s : ℚ, F.eval (s + 1) * ∏ i : Fin 3, (s + v (.inr i)) =
      F.eval s * ∏ i : Fin 3, (s + v (.inl i.castSucc)))
    (hη : 1 ≤ η) (hZ : (X + C (η : ℚ)) ^ 2 ∣ (∏ i : Fin 3, (X + C ((v (.inr i) : ℚ) - 1))) * F)
    (h : ℚ[X]) : Phi m η (Lmap v h * F) = 0 := by
  have hL : Lmap v h * F = h * Apol v * F - taylor 1 h * Dpol v * F := by rw [Lmap_apply]; ring
  have eA : ∀ s : ℚ, (Apol v).eval (s + 1) = (s + 1) * ∏ i : Fin 3, (s + v (.inr i)) := by
    intro s
    rw [Apol, eval_mul, eval_X, eval_prod]
    congr 1
    refine prod_congr rfl fun i _ => ?_
    rw [eval_add, eval_X, eval_C]
    ring
  have eD : ∀ s : ℚ, (Dpol v).eval s =
      (∏ i : Fin 3, (s + v (.inl i.castSucc))) * (s - m) := by
    intro s
    rw [Dpol, eval_prod, Fin.prod_univ_castSucc]
    simp only [eval_add, eval_X, eval_C]
    congr 1
    rw [show (Fin.last 3) = (3 : Fin 4) from rfl, hm]
    push_cast
    ring
  have eG : ∀ s : ℚ, (h * Apol v * F).eval (s + 1) =
      h.eval (s + 1) * (s + 1) * (∏ i : Fin 3, (s + v (.inl i.castSucc))) * F.eval s := by
    intro s
    rw [eval_mul, eval_mul, eA]
    linear_combination (h.eval (s + 1) * (s + 1)) * hK s
  have eP : ∀ s : ℚ, (taylor 1 h * Dpol v * F).eval s =
      h.eval (s + 1) * ((∏ i : Fin 3, (s + v (.inl i.castSucc))) * (s - m)) * F.eval s := by
    intro s
    rw [eval_mul, eval_mul, taylor_eval, eD]
  have urec : ∀ j : ℕ, om m j * (taylor 1 h * Dpol v * F).eval (j : ℚ) =
      om m (j + 1) * (h * Apol v * F).eval ((j + 1 : ℕ) : ℚ) := by
    intro j
    rw [eP, show ((j + 1 : ℕ) : ℚ) = (j : ℚ) + 1 by push_cast; ring, eG]
    linear_combination (-(h.eval ((j : ℚ) + 1) * (∏ i : Fin 3, ((j : ℚ) + v (.inl i.castSucc))) *
      F.eval (j : ℚ))) * om_succ_mul m j
  have u0 : om m 0 * (h * Apol v * F).eval ((0 : ℕ) : ℚ) = 0 := by
    rw [Nat.cast_zero, eval_mul, eval_mul, Apol, eval_mul, eval_X]
    ring
  have um : om m (m + 1) = 0 := by
    rw [om, Nat.choose_succ_self, Nat.cast_zero, mul_zero]
  have hshift : Sm m (taylor 1 h * Dpol v * F) = taylor 1 (Sm m (h * Apol v * F)) := by
    apply eq_of_infinite_eval_eq
    refine (Set.Ioi_infinite (m : ℚ)).mono fun s hs => ?_
    have hs' : (m : ℚ) < s := hs
    show eval s (Sm m (taylor 1 h * Dpol v * F)) = eval s (taylor 1 (Sm m (h * Apol v * F)))
    rw [taylor_eval, Sm_eval m _ s hs', Sm_eval m _ (s + 1) (by linarith), eP, eG]
    have e1 : ∑ j ∈ range (m + 1), om m j * (taylor 1 h * Dpol v * F).eval (j : ℚ) / (s - j) =
        ∑ j ∈ range (m + 1), om m (j + 1) * (h * Apol v * F).eval ((j + 1 : ℕ) : ℚ) / (s - j) :=
      sum_congr rfl fun j _ => by rw [urec]
    have e2 : ∑ j ∈ range (m + 1), om m j * (h * Apol v * F).eval (j : ℚ) / (s + 1 - j) =
        ∑ j ∈ range (m + 1), om m (j + 1) * (h * Apol v * F).eval ((j + 1 : ℕ) : ℚ) / (s - j) := by
      rw [sum_range_succ', sum_range_succ (fun j => om m (j + 1) *
        (h * Apol v * F).eval ((j + 1 : ℕ) : ℚ) / (s - j)), u0, um, zero_mul, zero_div, zero_div,
        add_zero, add_zero]
      refine sum_congr rfl fun j _ => ?_
      congr 1
      push_cast
      ring
    rw [e1, e2]
    linear_combination (-(h.eval (s + 1) * (∏ i : Fin 3, (s + v (.inl i.castSucc))) *
      F.eval s)) * Lsum_id m s hs'
  have hg2 : (X + C (η : ℚ)) ^ 2 ∣ h * Apol v * F := by
    have : h * Apol v * F = (h * X) * ((∏ i : Fin 3, (X + C ((v (.inr i) : ℚ) - 1))) * F) := by
      rw [Apol]; ring
    rw [this]
    exact Dvd.dvd.mul_left hZ _
  have hder : (Sm m (h * Apol v * F)).derivative.eval (-(η : ℚ)) =
      ∑ j ∈ range (m + 1), om m j * (h * Apol v * F).eval (j : ℚ) / ((j : ℚ) + η) ^ 2 := by
    rw [Sm, derivative_sum, eval_finsetSum]
    refine sum_congr rfl fun j _ => ?_
    rw [derivative_smul, eval_smul, DD_deriv _ _ _ hg2 (by positivity), smul_eq_mul, mul_div_assoc]
  have htele := tele (fun j => om m j * (h * Apol v * F).eval (j : ℚ)) η u0 m
  simp only [um, zero_mul, sub_zero] at htele
  rw [hL]
  funext i
  fin_cases i
  · simp only [Phi, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Pi.zero_apply]
    have hsum : ∑ j ∈ range (m + 1), om m j * (h * Apol v * F - taylor 1 h * Dpol v * F).eval (j : ℚ) *
        harm2 (j + η) = ∑ j ∈ range (m + 1), (om m j * (h * Apol v * F).eval (j : ℚ) -
          om m (j + 1) * (h * Apol v * F).eval ((j + 1 : ℕ) : ℚ)) * harm2 (j + η) :=
      sum_congr rfl fun j _ => by rw [eval_sub, ← urec j]; ring
    have hS : Sm m (h * Apol v * F - taylor 1 h * Dpol v * F) =
        -(taylor 1 (Sm m (h * Apol v * F)) - Sm m (h * Apol v * F)) := by
      rw [Sm_sub, hshift]
      ring
    rw [hsum, htele, hS, Jfun_neg, J_delta, hder]
    simp only [mul_div_assoc]
    ring
  · simp only [Phi, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Pi.zero_apply]
    have hsum : ∑ j ∈ range (m + 1), om m j * (h * Apol v * F - taylor 1 h * Dpol v * F).eval (j : ℚ) =
        ∑ j ∈ range (m + 1), (om m j * (h * Apol v * F).eval (j : ℚ) -
          om m (j + 1) * (h * Apol v * F).eval ((j + 1 : ℕ) : ℚ)) :=
      sum_congr rfl fun j _ => by rw [eval_sub, ← urec j]; ring
    rw [hsum, sum_range_sub' (fun j => om m j * (h * Apol v * F).eval (j : ℚ)), u0, um, zero_mul,
      sub_zero]

theorem binom_eval (a : ℚ) (b : ℕ) (s : ℚ) :
    (binomPoly ℚ a b).eval s = ((b.factorial : ℚ))⁻¹ * (descPochhammer ℚ b).eval (s + a) := by
  rw [binomPoly, eval_mul, eval_C, eval_comp, eval_add, eval_X, eval_C]

theorem binom_rec (a : ℚ) (b : ℕ) (s : ℚ) :
    (binomPoly ℚ a b).eval (s + 1) * (s + a + 1 - b) = (binomPoly ℚ a b).eval s * (s + a + 1) := by
  rw [binom_eval, binom_eval, show s + 1 + a = s + a + 1 by ring]
  have h1 := congrArg (eval (s + a + 1)) (descPochhammer_succ_right ℚ b)
  have h2 := congrArg (eval (s + a + 1)) (descPochhammer_succ_left ℚ b)
  simp only [eval_mul, eval_sub, eval_X, eval_natCast, eval_comp, eval_one,
    add_sub_cancel_right] at h1 h2
  linear_combination ((b.factorial : ℚ))⁻¹ * (h1.symm.trans h2)

theorem binom_root (a b η : ℕ) (h1 : η ≤ a) (h2 : a ≤ η + b) :
    (X + C (η : ℚ)) ∣ (X + C ((a : ℚ) - b)) * binomPoly ℚ (a : ℚ) b := by
  rw [show X + C (η : ℚ) = X - C (-(η : ℚ)) by rw [C_neg, sub_neg_eq_add], dvd_iff_isRoot,
    IsRoot, eval_mul, binom_eval, eval_add, eval_X, eval_C,
    show -(η : ℚ) + a = ((a - η : ℕ) : ℚ) by rw [Nat.cast_sub h1]; ring,
    descPochhammer_eval_eq_descFactorial]
  by_cases hlt : a - η < b
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hlt]
    simp
  · have : a = η + b := by omega
    subst this
    push_cast
    ring

theorem binom_succ (a b : ℕ) :
    binomPoly ℚ (((a + 1 : ℕ)) : ℚ) (b + 1) =
      C ((b : ℚ) + 1)⁻¹ * (X + C ((a : ℚ) + 1)) * binomPoly ℚ (a : ℚ) b := by
  unfold binomPoly
  rw [descPochhammer_succ_left, mul_comp, X_comp, comp_assoc, sub_comp, X_comp, one_comp,
    show X + C (((a + 1 : ℕ)) : ℚ) - 1 = X + C (a : ℚ) by push_cast; rw [C_add, C_1]; ring,
    Nat.factorial_succ, Nat.cast_mul, mul_inv, C_mul]
  push_cast
  ring

theorem dvd_U (k : ℕ) (x : ℤ) (hk : 1 ≤ k) (hkx : (k : ℤ) < x) : (X + C (k : ℚ)) ∣ U x := by
  have hmem : k ∈ Ico 1 x.toNat := mem_Ico.2 ⟨hk, by omega⟩
  have hk0 : (k : ℚ) ≠ 0 := by positivity
  have h1 : (X + C (k : ℚ)) ∣ (1 + C ((k : ℚ))⁻¹ * X) :=
    ⟨C (k : ℚ)⁻¹, by linear_combination (-(1 : ℚ[X])) * hpinv (k : ℚ) hk0⟩
  exact h1.trans (dvd_prod_of_mem (fun t : ℕ => 1 + C ((t : ℚ))⁻¹ * X) hmem)

theorem U_binom (y : ℕ) (hy : 1 ≤ y) : ∀ b : ℕ,
    U (y : ℤ) * binomPoly ℚ ((y - 1 + b : ℕ) : ℚ) b =
      C (((y - 1 + b).choose b : ℕ) : ℚ) * U ((y + b : ℕ) : ℤ)
  | 0 => by
    simp only [binomPoly, descPochhammer_zero, one_comp, Nat.factorial_zero, Nat.cast_one, inv_one,
      C_1, mul_one, Nat.choose_zero_right, one_mul, Nat.add_zero]
  | b + 1 => by
    have ih := U_binom y hy b
    rw [show y - 1 + (b + 1) = (y - 1 + b) + 1 by omega, binom_succ,
      show y + (b + 1) = (y + b) + 1 by omega, Nat.cast_succ, U_succ _ (by omega)]
    have hq : (((y + b : ℕ) : ℤ) : ℚ) = ((y - 1 + b : ℕ) : ℚ) + 1 := by
      rw [Int.cast_natCast]
      exact_mod_cast (show y + b = (y - 1 + b) + 1 by omega)
    have hc : (((y - 1 + b + 1).choose (b + 1) : ℕ) : ℚ) =
        ((y - 1 + b).choose b : ℚ) * (((y - 1 + b : ℕ) : ℚ) + 1) * ((b : ℚ) + 1)⁻¹ := by
      have := Nat.add_one_mul_choose_eq (y - 1 + b) b
      have hb : ((b : ℚ) + 1) ≠ 0 := by positivity
      rw [eq_mul_inv_iff_mul_eq₀ hb]
      exact_mod_cast this.symm.trans (mul_comm _ _)
    have hq0 : (((y - 1 + b : ℕ) : ℚ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero _
    rw [hq, hc]
    calc U (y : ℤ) * (C ((b : ℚ) + 1)⁻¹ * (X + C (((y - 1 + b : ℕ) : ℚ) + 1)) *
          binomPoly ℚ ((y - 1 + b : ℕ) : ℚ) b)
        = C ((b : ℚ) + 1)⁻¹ * (X + C (((y - 1 + b : ℕ) : ℚ) + 1)) *
          (U (y : ℤ) * binomPoly ℚ ((y - 1 + b : ℕ) : ℚ) b) := by ring
      _ = C ((b : ℚ) + 1)⁻¹ * (X + C (((y - 1 + b : ℕ) : ℚ) + 1)) *
          (C (((y - 1 + b).choose b : ℕ) : ℚ) * U ((y + b : ℕ) : ℤ)) := by rw [ih]
      _ = _ := by
        rw [C_mul, C_mul]
        linear_combination (-(C ((b : ℚ) + 1)⁻¹ * C (((y - 1 + b).choose b : ℕ) : ℚ) *
          U ((y + b : ℕ) : ℤ) * X)) * hpinv _ hq0

theorem Th_eN (N : ℕ) : Th (eN N) =
    U ((10 * N + 1 : ℕ) : ℤ) * U ((9 * N + 1 : ℕ) : ℤ) * U ((11 * N + 1 : ℕ) : ℤ) := by
  simp only [Th, Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_three, phT, eN, vtx, dir]
  push_cast
  simp

theorem Pp_eN (N : ℕ) : Pp (eN N) = Xi (-((11 * N : ℕ) : ℤ)) *
    (U ((2 * N + 1 : ℕ) : ℤ) * U ((N + 1 : ℕ) : ℤ) * U ((3 * N + 1 : ℕ) : ℤ)) := by
  simp only [Pp, Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_three, phP, eN, vtx, dir]
  push_cast
  simp

theorem global_id (N η : ℕ) (h2 : η ≤ 9 * N) (g : ℚ[X]) :
    Phi (11 * N) η (Pp (eN N) * g * Fpoly N) = (CN N : ℚ) • Phi 0 0 (Th (eN N) * g) := by
  have e0 := U_binom (2 * N + 1) (by omega) (8 * N)
  have e1 := U_binom (N + 1) (by omega) (8 * N)
  have e2 := U_binom (3 * N + 1) (by omega) (8 * N)
  rw [show 2 * N + 1 - 1 + 8 * N = 10 * N by omega, show 2 * N + 1 + 8 * N = 10 * N + 1 by omega,
    Nat.choose_symm_of_eq_add (show 10 * N = 8 * N + 2 * N by omega)] at e0
  rw [show N + 1 - 1 + 8 * N = 9 * N by omega, show N + 1 + 8 * N = 9 * N + 1 by omega,
    Nat.choose_symm_of_eq_add (show 9 * N = 8 * N + N by omega)] at e1
  rw [show 3 * N + 1 - 1 + 8 * N = 11 * N by omega, show 3 * N + 1 + 8 * N = 11 * N + 1 by omega,
    Nat.choose_symm_of_eq_add (show 11 * N = 8 * N + 3 * N by omega)] at e2
  have hF : Pp (eN N) * g * Fpoly N =
      Xi (-((11 * N : ℕ) : ℤ)) * (C (CN N : ℚ) * (Th (eN N) * g)) := by
    have hCN : (C (CN N : ℚ) : ℚ[X]) = C (((10 * N).choose (2 * N) : ℕ) : ℚ) *
        C (((9 * N).choose N : ℕ) : ℚ) * C (((11 * N).choose (3 * N) : ℕ) : ℚ) := by
      rw [← C_mul, ← C_mul, CN]
      push_cast
      rfl
    rw [Pp_eN, Th_eN, Fpoly, hCN]
    calc Xi (-((11 * N : ℕ) : ℤ)) * (U ((2 * N + 1 : ℕ) : ℤ) * U ((N + 1 : ℕ) : ℤ) *
          U ((3 * N + 1 : ℕ) : ℤ)) * g *
          (binomPoly ℚ ((10 * N : ℕ) : ℚ) (8 * N) * binomPoly ℚ ((9 * N : ℕ) : ℚ) (8 * N) *
            binomPoly ℚ ((11 * N : ℕ) : ℚ) (8 * N))
        = Xi (-((11 * N : ℕ) : ℤ)) *
          ((U ((2 * N + 1 : ℕ) : ℤ) * binomPoly ℚ ((10 * N : ℕ) : ℚ) (8 * N)) *
           (U ((N + 1 : ℕ) : ℤ) * binomPoly ℚ ((9 * N : ℕ) : ℚ) (8 * N)) *
           (U ((3 * N + 1 : ℕ) : ℤ) * binomPoly ℚ ((11 * N : ℕ) : ℚ) (8 * N))) * g := by ring
      _ = _ := by
        rw [e0, e1, e2]
        ring
  rw [hF, Phi_Xi, Phi_C_mul, Phi0_shift_iter _ η fun k hk1 hk2 => ?_]
  rw [Th_eN, pow_two]
  refine dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (mul_dvd_mul ?_ ?_) _) _
  · exact dvd_U k _ hk1 (by push_cast; omega)
  · exact dvd_U k _ hk1 (by push_cast; omega)

theorem eN_hK (N : ℕ) (s : ℚ) :
    (Fpoly N).eval (s + 1) * ∏ i : Fin 3, (s + (eN N (.inr i) : ℚ)) =
      (Fpoly N).eval s * ∏ i : Fin 3, (s + (eN N (.inl i.castSucc) : ℚ)) := by
  have r0 := binom_rec ((10 * N : ℕ) : ℚ) (8 * N) s
  have r1 := binom_rec ((9 * N : ℕ) : ℚ) (8 * N) s
  have r2 := binom_rec ((11 * N : ℕ) : ℚ) (8 * N) s
  have c0 : ((eN N (.inr 0) : ℤ) : ℚ) = ((10 * N : ℕ) : ℚ) + 1 - ((8 * N : ℕ) : ℚ) := by
    show ((2 * (N : ℤ) + 1 : ℤ) : ℚ) = _
    rw [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Int.cast_one, Nat.cast_mul,
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_ofNat]
    ring
  have c1 : ((eN N (.inr 1) : ℤ) : ℚ) = ((9 * N : ℕ) : ℚ) + 1 - ((8 * N : ℕ) : ℚ) := by
    show (((N : ℤ) + 1 : ℤ) : ℚ) = _
    rw [Int.cast_add, Int.cast_natCast, Int.cast_one, Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_ofNat]
    ring
  have c2 : ((eN N (.inr 2) : ℤ) : ℚ) = ((11 * N : ℕ) : ℚ) + 1 - ((8 * N : ℕ) : ℚ) := by
    show ((3 * (N : ℤ) + 1 : ℤ) : ℚ) = _
    rw [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Int.cast_one, Nat.cast_mul,
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_ofNat]
    ring
  have d0 : ((eN N (.inl (0 : Fin 3).castSucc) : ℤ) : ℚ) = ((10 * N : ℕ) : ℚ) + 1 := by
    show ((10 * (N : ℤ) + 1 : ℤ) : ℚ) = _
    rw [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Int.cast_one, Nat.cast_mul,
      Nat.cast_ofNat]
  have d1 : ((eN N (.inl (1 : Fin 3).castSucc) : ℤ) : ℚ) = ((9 * N : ℕ) : ℚ) + 1 := by
    show ((9 * (N : ℤ) + 1 : ℤ) : ℚ) = _
    rw [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Int.cast_one, Nat.cast_mul,
      Nat.cast_ofNat]
  have d2 : ((eN N (.inl (2 : Fin 3).castSucc) : ℤ) : ℚ) = ((11 * N : ℕ) : ℚ) + 1 := by
    show ((11 * (N : ℤ) + 1 : ℤ) : ℚ) = _
    rw [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Int.cast_one, Nat.cast_mul,
      Nat.cast_ofNat]
  rw [Fin.prod_univ_three, Fin.prod_univ_three, c0, c1, c2, d0, d1, d2, Fpoly, eval_mul, eval_mul,
    eval_mul, eval_mul]
  generalize (binomPoly ℚ ((10 * N : ℕ) : ℚ) (8 * N)) = B0 at r0 ⊢
  generalize (binomPoly ℚ ((9 * N : ℕ) : ℚ) (8 * N)) = B1 at r1 ⊢
  generalize (binomPoly ℚ ((11 * N : ℕ) : ℚ) (8 * N)) = B2 at r2 ⊢
  linear_combination (B1.eval (s + 1) * (s + ((9 * N : ℕ) : ℚ) + 1 - ((8 * N : ℕ) : ℚ)) *
      B2.eval (s + 1) * (s + ((11 * N : ℕ) : ℚ) + 1 - ((8 * N : ℕ) : ℚ))) * r0 +
    (B0.eval s * (s + ((10 * N : ℕ) : ℚ) + 1) * B2.eval (s + 1) *
      (s + ((11 * N : ℕ) : ℚ) + 1 - ((8 * N : ℕ) : ℚ))) * r1 +
    (B0.eval s * (s + ((10 * N : ℕ) : ℚ) + 1) * B1.eval s * (s + ((9 * N : ℕ) : ℚ) + 1)) * r2

theorem eN_hZ (N η : ℕ) (h1 : 2 * N ≤ η) (h2 : η ≤ 9 * N) :
    (X + C (η : ℚ)) ^ 2 ∣ (∏ i : Fin 3, (X + C ((eN N (.inr i) : ℚ) - 1))) * Fpoly N := by
  have hp : ∏ i : Fin 3, (X + C ((eN N (.inr i) : ℚ) - 1)) =
      (X + C (((10 * N : ℕ) : ℚ) - ((8 * N : ℕ) : ℚ))) *
        (X + C (((9 * N : ℕ) : ℚ) - ((8 * N : ℕ) : ℚ))) *
          (X + C (((11 * N : ℕ) : ℚ) - ((8 * N : ℕ) : ℚ))) := by
    have a0 : ((eN N (.inr 0) : ℤ) : ℚ) - 1 = ((10 * N : ℕ) : ℚ) - ((8 * N : ℕ) : ℚ) := by
      show ((2 * (N : ℤ) + 1 : ℤ) : ℚ) - 1 = _
      rw [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Int.cast_one, Nat.cast_mul,
        Nat.cast_mul, Nat.cast_ofNat, Nat.cast_ofNat]
      ring
    have a1 : ((eN N (.inr 1) : ℤ) : ℚ) - 1 = ((9 * N : ℕ) : ℚ) - ((8 * N : ℕ) : ℚ) := by
      show (((N : ℤ) + 1 : ℤ) : ℚ) - 1 = _
      rw [Int.cast_add, Int.cast_natCast, Int.cast_one, Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_ofNat]
      ring
    have a2 : ((eN N (.inr 2) : ℤ) : ℚ) - 1 = ((11 * N : ℕ) : ℚ) - ((8 * N : ℕ) : ℚ) := by
      show ((3 * (N : ℤ) + 1 : ℤ) : ℚ) - 1 = _
      rw [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Int.cast_one, Nat.cast_mul,
        Nat.cast_mul, Nat.cast_ofNat, Nat.cast_ofNat]
      ring
    rw [Fin.prod_univ_three, a0, a1, a2]
  rw [hp, Fpoly, pow_two]
  have e : (X + C (((10 * N : ℕ) : ℚ) - ((8 * N : ℕ) : ℚ))) *
        (X + C (((9 * N : ℕ) : ℚ) - ((8 * N : ℕ) : ℚ))) *
          (X + C (((11 * N : ℕ) : ℚ) - ((8 * N : ℕ) : ℚ))) *
      (binomPoly ℚ ((10 * N : ℕ) : ℚ) (8 * N) * binomPoly ℚ ((9 * N : ℕ) : ℚ) (8 * N) *
        binomPoly ℚ ((11 * N : ℕ) : ℚ) (8 * N)) =
      ((X + C (((10 * N : ℕ) : ℚ) - ((8 * N : ℕ) : ℚ))) * binomPoly ℚ ((10 * N : ℕ) : ℚ) (8 * N)) *
        ((X + C (((9 * N : ℕ) : ℚ) - ((8 * N : ℕ) : ℚ))) * binomPoly ℚ ((9 * N : ℕ) : ℚ) (8 * N)) *
          ((X + C (((11 * N : ℕ) : ℚ) - ((8 * N : ℕ) : ℚ))) *
            binomPoly ℚ ((11 * N : ℕ) : ℚ) (8 * N)) := mul3_mul3 _ _ _ _ _ _
  rw [e]
  exact dvd_mul_of_dvd_left (mul_dvd_mul (binom_root _ _ _ (by omega) (by omega))
    (binom_root _ _ _ (by omega) (by omega))) _

theorem ann_eN (N η : ℕ) (hN : 1 ≤ N) (h1 : 2 * N ≤ η) (h2 : η ≤ 9 * N) (h : ℚ[X]) :
    Phi (11 * N) η (Lmap (eN N) h * Fpoly N) = 0 :=
  ann_gen (eN N) (11 * N) η (Fpoly N) (by show -(11 * (N : ℤ)) = _; omega) (eN_hK N) (by omega)
    (eN_hZ N η h1 h2) h

def Ye (N η : ℕ) : Matrix (Fin 2) (Fin 3) ℚ :=
  Matrix.of fun i r => (2 / (CN N : ℚ)) * Phi (11 * N) η (X ^ (r : ℕ) * Fpoly N) i

theorem Ye_mulVec_red (N η : ℕ) (hN : 1 ≤ N) (h1 : 2 * N ≤ η) (h2 : η ≤ 9 * N) (f : ℚ[X]) :
    Ye N η *ᵥ red (eN N) f = (2 / (CN N : ℚ)) • Phi (11 * N) η (f * Fpoly N) := by
  obtain ⟨k, hk⟩ := red_decomp _ (a3_eN N) f
  have hPhi : Phi (11 * N) η (f * Fpoly N) =
      Phi (11 * N) η (polyOf (red (eN N) f) * Fpoly N) := by
    conv_lhs => rw [hk]
    rw [add_mul, Phi_add, ann_eN N η hN h1 h2 k, add_zero]
  rw [hPhi, polyOf_apply]
  have e : (C (red (eN N) f 0) + C (red (eN N) f 1) * X + C (red (eN N) f 2) * X ^ 2) * Fpoly N =
      C (red (eN N) f 0) * (X ^ 0 * Fpoly N) + C (red (eN N) f 1) * (X ^ 1 * Fpoly N) +
        C (red (eN N) f 2) * (X ^ 2 * Fpoly N) := by ring
  rw [e, Phi_add, Phi_add, Phi_C_mul, Phi_C_mul, Phi_C_mul]
  funext i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Ye, Matrix.of_apply, Pi.smul_apply,
    Pi.add_apply, smul_eq_mul, Fin.val_zero, Fin.val_one, Fin.val_two]
  ring

theorem DD_X_mul (q : ℚ[X]) : DD (X * q) 0 = q :=
  DD_unique _ _ _ (by simp only [eval_mul, eval_X, zero_mul, C_0, sub_zero])

theorem Phi00 (p : ℚ[X]) : Phi 0 0 p = ![Jfun 0 (DD p 0), p.eval 0] := by
  have ho : om 0 0 = 1 := by rw [om, pow_zero, Nat.choose_self, Nat.cast_one, one_mul]
  have hS : Sm 0 p = DD p 0 := by rw [Sm, sum_range_one, ho, one_smul, Nat.cast_zero]
  have hH : harm2 (0 + 0) = 0 := by rw [harm2, Finset.Icc_eq_empty (by omega), sum_empty]
  rw [Phi, sum_range_one, sum_range_one, hS, ho, hH, Nat.cast_zero, mul_zero, zero_add, one_mul]

theorem Jfun_zero (η : ℕ) : Jfun η 0 = 0 := by
  rw [show (0 : ℚ[X]) = C 0 * 0 by rw [C_0, zero_mul], Jfun_C_mul, zero_mul]

theorem Phi00_one : Phi 0 0 1 = ![0, 1] := by
  rw [Phi00, show DD 1 0 = 0 from DD_unique _ _ _ (by rw [mul_zero, eval_one, C_1, sub_self]),
    Jfun_zero, eval_one]

theorem Phi00_X : Phi 0 0 X = ![1, 0] := by
  rw [Phi00, show DD X 0 = 1 by rw [← DD_X_mul 1, mul_one], eval_X, Jfun, natDegree_one,
    sum_range_one, sum_range_one, eval_one]
  simp only [pow_zero, Nat.cast_zero, zero_add, div_one, Nat.choose_self, Nat.cast_one, mul_one,
    Nat.sub_self]

theorem Phi00_X2 : Phi 0 0 (X ^ 2) = ![-1 / 2, 0] := by
  rw [Phi00, show DD (X ^ 2) 0 = X by rw [pow_two]; exact DD_X_mul X]
  simp [Jfun, sum_range_succ]
  norm_num

theorem Phi00_L (k : ℚ[X]) : Phi 0 0 (Lmap w0 k) = 0 := by
  have hA : Apol w0 = X * X ^ 3 := by
    rw [Apol, Fin.prod_univ_three]
    show X * ((X + C (((1 : ℤ) : ℚ) - 1)) * (X + C (((1 : ℤ) : ℚ) - 1)) *
      (X + C (((1 : ℤ) : ℚ) - 1))) = _
    rw [Int.cast_one, sub_self, C_0, add_zero]
    ring
  have hD : Dpol w0 = (X + 1) ^ 3 * X := by
    rw [Dpol, Fin.prod_univ_four]
    show (X + C ((1 : ℤ) : ℚ)) * (X + C ((1 : ℤ) : ℚ)) * (X + C ((1 : ℤ) : ℚ)) *
      (X + C ((0 : ℤ) : ℚ)) = _
    rw [Int.cast_one, Int.cast_zero, C_1, C_0, add_zero]
    ring
  have hL : Lmap w0 k = X * (-(taylor 1 (X ^ 3 * k) - X ^ 3 * k)) := by
    rw [Lmap_apply, hA, hD, taylor_mul, taylor_X_pow, C_1]
    ring
  have hG : (X ^ 3 * k).derivative.eval (-((0 : ℕ) : ℚ)) = 0 := by
    rw [show X ^ 3 * k = X * (X * (X * k)) by ring, derivative_mul, derivative_X, one_mul,
      Nat.cast_zero, neg_zero]
    simp only [eval_add, eval_mul, eval_X, zero_mul, add_zero]
  rw [hL, Phi00, DD_X_mul, Jfun_neg, J_delta, hG, neg_zero, eval_mul, eval_X, zero_mul]
  funext i
  fin_cases i <;> rfl

theorem R_red (h : ℚ[X]) : Rmat *ᵥ red w0 h = (2 : ℚ) • Phi 0 0 h := by
  obtain ⟨k, hk⟩ := red_decomp w0 a3_w0 h
  have hP : Phi 0 0 h = Phi 0 0 (polyOf (red w0 h)) := by
    conv_lhs => rw [hk]
    rw [Phi_add, Phi00_L, add_zero]
  rw [hP, polyOf_apply, show C (red w0 h 0) + C (red w0 h 1) * X + C (red w0 h 2) * X ^ 2 =
    C (red w0 h 0) * 1 + C (red w0 h 1) * X + C (red w0 h 2) * X ^ 2 by ring, Phi_add, Phi_add,
    Phi_C_mul, Phi_C_mul, Phi_C_mul, Phi00_one, Phi00_X, Phi00_X2]
  funext i
  fin_cases i <;>
    simp only [Rmat, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply, Fin.zero_eta,
      Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_fin_one] <;> ring

theorem CN_ne (N : ℕ) : (CN N : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.2 (Nat.mul_pos (Nat.mul_pos (Nat.choose_pos (by omega))
    (Nat.choose_pos (by omega))) (Nat.choose_pos (by omega))).ne'

theorem Rmat_W_eq (N η : ℕ) (hN : 1 ≤ N) (h1 : 2 * N ≤ η) (h2 : η ≤ 9 * N) :
    Rmat * W N = Ye N η := by
  refine mat_eq_of_mulVec _ _ fun z => ?_
  obtain ⟨g, rfl⟩ := surj_eN N z
  rw [← Matrix.mulVec_mulVec, show W N = walk w0 (route 3 N) from rfl, rep_route 3 N (Or.inl rfl) g,
    R_red, Ye_mulVec_red N η hN h1 h2, global_id N η h2, smul_smul, div_mul_cancel₀ _ (CN_ne N)]

theorem Ye_zero : Ye 0 0 = Rmat := by
  refine mat_eq_of_mulVec _ _ fun z => ?_
  have hR := R_red (polyOf z)
  rw [red_polyOf w0 a3_w0] at hR
  rw [hR, Ye, polyOf_apply]
  have hC : CN 0 = 1 := rfl
  have hB : binomPoly ℚ ((0 : ℕ) : ℚ) 0 = 1 := by
    rw [binomPoly, descPochhammer_zero, one_comp, Nat.factorial_zero, Nat.cast_one, inv_one, C_1,
      mul_one]
  have hF : Fpoly 0 = 1 := by
    simp only [Fpoly, Nat.mul_zero, hB, mul_one]
  rw [show C (z 0) + C (z 1) * X + C (z 2) * X ^ 2 =
    C (z 0) * 1 + C (z 1) * X + C (z 2) * X ^ 2 by ring, Phi_add, Phi_add,
    Phi_C_mul, Phi_C_mul, Phi_C_mul]
  funext i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply, hC, hF, Nat.mul_zero,
    Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, mul_one, Pi.smul_apply, Pi.add_apply,
    smul_eq_mul, Nat.cast_one]
  ring

theorem W_zero : W 0 = 1 := rfl

theorem readout_formula (N : ℕ) (r : Fin 3) (η : ℕ) (hη₁ : 2 * N ≤ η) (hη₂ : η ≤ 9 * N) :
    (CN N : ℚ) • (fun i => readout N i r) =
      ![2 * (∑ j ∈ range (11 * N + 1), (j : ℚ) ^ (r : ℕ) * cj N j * harm2 (j + η) +
          Jfun η (Spoly N r)),
        2 * ∑ j ∈ range (11 * N + 1), (j : ℚ) ^ (r : ℕ) * cj N j] := by
  have hY : readout N = Ye N η := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · obtain rfl : η = 0 := by omega
      rw [readout, W_zero, Matrix.mul_one, Ye_zero]
    · exact Rmat_W_eq N η hN hη₁ hη₂
  have h2 : (CN N : ℚ) * (2 / CN N) = 2 := by rw [mul_div_assoc', mul_div_cancel_left₀ _ (CN_ne N)]
  have hS : Sm (11 * N) (X ^ (r : ℕ) * Fpoly N) = Spoly N r := rfl
  have hs : ∀ j : ℕ, om (11 * N) j * (X ^ (r : ℕ) * Fpoly N).eval (j : ℚ) =
      (j : ℚ) ^ (r : ℕ) * cj N j := fun j => by
    rw [om, cj, eval_mul, eval_pow, eval_X]
    ring
  funext i
  rw [Pi.smul_apply, hY, Ye, Matrix.of_apply, smul_eq_mul, ← mul_assoc, h2]
  fin_cases i
  · simp only [Phi, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, hS, hs]
  · simp only [Phi, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, hs]

end Zeta2FirstThree
