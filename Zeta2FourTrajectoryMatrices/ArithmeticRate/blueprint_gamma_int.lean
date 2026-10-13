import Zeta2FourTrajectoryMatrices.ArithmeticRate.blueprint_gamma_sum

open MeasureTheory Set Filter Topology Finset Zeta2Blueprint Zeta2GammaCore Zeta2GammaTable
  Zeta2GammaSum

noncomputable section

namespace Zeta2GammaInt

/-! ### The cut points as reals -/

def cutR (i : ℕ) : ℝ := ((cut i : ℚ) : ℝ)

def hvR (i : ℕ) : ℝ := ((hv i : ℤ) : ℝ)

theorem cutR_zero : cutR 0 = 0 := by
  rw [cutR, cut_zero]
  push_cast
  rfl

theorem cutR_last : cutR 94 = 1 := by
  rw [cutR, cut_last]
  push_cast
  rfl

theorem cutR_13 : cutR 5 = 1 / 13 := by
  rw [cutR, cut_13]
  push_cast
  rfl

theorem cutR_lt (i : ℕ) (hi : i < 94) : cutR i < cutR (i + 1) := by
  unfold cutR
  exact_mod_cast cut_lt i hi

theorem cutR_mono_add : ∀ n i, i + n ≤ 94 → cutR i ≤ cutR (i + n)
  | 0, _, _ => le_rfl
  | n + 1, i, h => by
    rw [← add_assoc]
    exact (cutR_mono_add n i (by omega)).trans (cutR_lt (i + n) (by omega)).le

theorem cutR_mono (i j : ℕ) (hij : i ≤ j) (hj : j ≤ 94) : cutR i ≤ cutR j := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hij
  exact cutR_mono_add n i hj

theorem cutR_nonneg (i : ℕ) (hi : i ≤ 94) : 0 ≤ cutR i :=
  cutR_zero ▸ cutR_mono 0 i (Nat.zero_le _) hi

theorem cutR_le_one (i : ℕ) (hi : i ≤ 94) : cutR i ≤ 1 :=
  cutR_last ▸ cutR_mono i 94 hi le_rfl

theorem hvR_nonneg (i : ℕ) (hi : i < 94) : 0 ≤ hvR i := by
  unfold hvR
  exact_mod_cast hv_nonneg i hi

theorem hvR_le (i : ℕ) (hi : i < 94) : hvR i ≤ 3 := by
  unfold hvR
  exact_mod_cast hv_le i hi

theorem find_cell (t : ℝ) (h0 : 0 ≤ t) (h1 : t < 1) :
    ∃ i, i < 94 ∧ cutR i ≤ t ∧ t < cutR (i + 1) := by
  classical
  have hex : ∃ j, j < 94 ∧ t < cutR (j + 1) := ⟨93, by norm_num, by rw [cutR_last]; exact h1⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, ?_, (Nat.find_spec hex).2⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · rw [h, cutR_zero]
    exact h0
  · have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    push Not at hmin
    have h2 := hmin (by have := (Nat.find_spec hex).1; omega)
    rwa [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at h2

/-! ### The periodic step function -/

def G (x : ℝ) : ℝ :=
  ∑ i ∈ range 94, hvR i * (Ico (cutR i) (cutR (i + 1))).indicator (fun _ => (1 : ℝ)) (Int.fract x)

theorem G_eq (x : ℝ) (i : ℕ) (hi : i < 94) (h1 : cutR i ≤ Int.fract x)
    (h2 : Int.fract x < cutR (i + 1)) : G x = hvR i := by
  unfold G
  rw [Finset.sum_eq_single i]
  · rw [indicator_of_mem (show Int.fract x ∈ Ico (cutR i) (cutR (i + 1)) from ⟨h1, h2⟩), mul_one]
  · intro j hj hji
    rw [indicator_of_notMem, mul_zero]
    rw [Set.mem_Ico, not_and_or, not_le, not_lt]
    rcases lt_or_gt_of_ne hji with h | h
    · right
      exact (cutR_mono (j + 1) i h (by omega)).trans h1
    · left
      exact h2.trans_le (cutR_mono (i + 1) j h (mem_range.1 hj).le)
  · intro h
    exact absurd (mem_range.2 hi) h

theorem G_bounds (x : ℝ) : 0 ≤ G x ∧ G x ≤ 3 := by
  obtain ⟨i, hi, h1, h2⟩ := find_cell (Int.fract x) (Int.fract_nonneg x) (Int.fract_lt_one x)
  rw [G_eq x i hi h1 h2]
  exact ⟨hvR_nonneg i hi, hvR_le i hi⟩

theorem measurable_G : Measurable G := by
  unfold G
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((measurable_const.indicator measurableSet_Ico).comp measurable_fract).const_mul _

def g (x : ℝ) : ℝ := G x / x ^ 2

def f (x : ℝ) : ℝ := (phi x : ℝ) / x ^ 2

theorem measurable_g : Measurable g := measurable_G.div (measurable_id.pow_const 2)

def cutpts : Set ℝ := ⋃ (k : ℕ) (i ∈ (range 95 : Finset ℕ)), {(k : ℝ) + cutR i}

theorem cutpts_countable : cutpts.Countable :=
  Set.countable_iUnion fun _ =>
    (Finset.countable_toSet _).biUnion fun _ _ => Set.countable_singleton _

theorem cutpts_null : volume cutpts = 0 := cutpts_countable.measure_zero _

theorem mem_cutpts (k i : ℕ) (hi : i < 95) : (k : ℝ) + cutR i ∈ cutpts := by
  simp only [cutpts, mem_iUnion, mem_singleton_iff, exists_prop]
  exact ⟨k, i, mem_range.2 hi, rfl⟩

theorem phi_eq_G (x : ℝ) (hx : 0 ≤ x) (hc : x ∉ cutpts) : (phi x : ℝ) = G x := by
  obtain ⟨i, hi, h1, h2⟩ := find_cell (Int.fract x) (Int.fract_nonneg x) (Int.fract_lt_one x)
  have h1' : cutR i < Int.fract x := by
    rcases h1.lt_or_eq with h | h
    · exact h
    · exfalso
      apply hc
      have := mem_cutpts ⌊x⌋.toNat i (by omega)
      rwa [show ((⌊x⌋.toNat : ℕ) : ℝ) = (⌊x⌋ : ℝ) by
        exact_mod_cast Int.toNat_of_nonneg (Int.floor_nonneg.2 hx), h, Int.floor_add_fract] at this
  rw [G_eq x i hi h1 h2, phi_eq_fract x hx, cell_all i hi _ h1' h2]
  rfl

theorem f_ae_g : f =ᵐ[volume.restrict (Ici (0 : ℝ))] g := by
  have h1 : ∀ᵐ x ∂volume, x ∉ cutpts := by
    rw [ae_iff]
    simpa using cutpts_null
  have h2 : ∀ᵐ x ∂(volume.restrict (Ici (0 : ℝ))), x ∈ Ici (0 : ℝ) :=
    ae_restrict_mem measurableSet_Ici
  filter_upwards [ae_restrict_of_ae h1, h2] with x hx hx0
  simp only [f, g, phi_eq_G x hx0 hx]

theorem integral_f_eq_g (s : Set ℝ) (hs : s ⊆ Ici 0) : ∫ x in s, f x = ∫ x in s, g x :=
  integral_congr_ae (ae_restrict_of_ae_restrict_of_subset hs f_ae_g)

/-! ### Integrability -/

theorem integrableOn_inv_sq (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => (x ^ 2)⁻¹) (Ioi a) := by
  have := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha
  refine this.congr_fun (fun x hx => ?_) measurableSet_Ioi
  change x ^ (-2 : ℝ) = (x ^ 2)⁻¹
  rw [Real.rpow_neg (le_of_lt (ha.trans hx)), Real.rpow_two]

theorem g_integrableOn_Ioi (a : ℝ) (ha : 0 < a) : IntegrableOn g (Ioi a) := by
  have h := (integrableOn_inv_sq a ha).bdd_mul (c := 3) measurable_G.aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  · refine IntegrableOn.congr_fun h (fun x _ => ?_) measurableSet_Ioi
    simp only [g, div_eq_mul_inv]
  · rw [Real.norm_eq_abs, abs_le]
    have := G_bounds x
    constructor <;> linarith

theorem g_zero_of_lt (x : ℝ) (hx0 : 0 ≤ x) (hx : x < 1 / 13) : g x = 0 := by
  obtain ⟨i, hi, h1, h2⟩ := find_cell x hx0 (by linarith)
  have hfr : Int.fract x = x := Int.fract_eq_self.2 ⟨hx0, by linarith⟩
  have hi5 : i + 1 ≤ 5 := by
    by_contra h
    push Not at h
    have := cutR_mono 5 i (by omega) hi.le
    rw [cutR_13] at this
    linarith
  have hz : hv i = 0 := by
    refine hv_zero_of_lt i hi ?_
    have := cutR_mono (i + 1) 5 hi5 (by norm_num)
    rw [cutR_13] at this
    unfold cutR at this
    exact (Rat.cast_le (K := ℝ)).1 (by simpa using this)
  rw [g, G_eq x i hi (by rw [hfr]; exact h1) (by rw [hfr]; exact h2), hvR, hz]
  simp

theorem g_integrableOn_Ico (n : ℕ) : IntegrableOn g (Ico 0 n) := by
  have h1 : IntegrableOn g (Ico 0 (1 / 13)) := by
    refine integrableOn_zero.congr_fun (fun x hx => ?_) measurableSet_Ico
    exact (g_zero_of_lt x hx.1 hx.2).symm
  have h2 : IntegrableOn g (Ici (1 / 13)) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).2 (g_integrableOn_Ioi _ (by norm_num))
  refine (h1.union h2).mono_set ?_
  intro x hx
  by_cases h : x < 1 / 13
  · exact Or.inl ⟨hx.1, h⟩
  · exact Or.inr (not_lt.1 h)

/-! ### Decomposition into periods -/

theorem integral_Ico_succ (n : ℕ) :
    ∫ x in Ico (0 : ℝ) ((n : ℝ) + 1), g x =
      (∫ x in Ico (0 : ℝ) n, g x) + ∫ x in Ico (n : ℝ) (n + 1), g x := by
  have h := g_integrableOn_Ico (n + 1)
  push_cast at h
  rw [← Ico_union_Ico_eq_Ico (by positivity : (0 : ℝ) ≤ n) (by linarith : (n : ℝ) ≤ n + 1),
    setIntegral_union Ico_disjoint_Ico_same measurableSet_Ico (g_integrableOn_Ico n)
      (h.mono_set fun x hx => ⟨by linarith [hx.1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)], hx.2⟩)]

theorem integral_Ico_eq_sum (n : ℕ) :
    ∫ x in Ico (0 : ℝ) n, g x = ∑ k ∈ range n, ∫ x in Ico (k : ℝ) (k + 1), g x := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, integral_Ico_succ, Finset.sum_range_succ, ← ih]

theorem fract_eq_sub (k : ℕ) (x : ℝ) (hx : x ∈ Ico (k : ℝ) (k + 1)) : Int.fract x = x - k := by
  rw [← Int.self_sub_floor, show ⌊x⌋ = (k : ℤ) from
    Int.floor_eq_iff.2 ⟨by exact_mod_cast hx.1, by exact_mod_cast hx.2⟩]
  push_cast
  ring

theorem g_eq_sum (k : ℕ) (x : ℝ) (hx : x ∈ Ico (k : ℝ) (k + 1)) :
    g x = ∑ i ∈ range 94,
      (Ico ((k : ℝ) + cutR i) (k + cutR (i + 1))).indicator (fun y => hvR i / y ^ 2) x := by
  rw [g, G, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fract_eq_sub k x hx]
  by_cases h : x ∈ Ico ((k : ℝ) + cutR i) (k + cutR (i + 1))
  · rw [indicator_of_mem h, indicator_of_mem (show x - k ∈ Ico (cutR i) (cutR (i + 1)) from
      ⟨by linarith [h.1], by linarith [h.2]⟩), mul_one]
  · rw [indicator_of_notMem h, indicator_of_notMem (show x - k ∉ Ico (cutR i) (cutR (i + 1)) from
      fun h' => h ⟨by linarith [h'.1], by linarith [h'.2]⟩), mul_zero, zero_div]

theorem piece_subset (k i : ℕ) (hi : i < 94) :
    Ico ((k : ℝ) + cutR i) (k + cutR (i + 1)) ⊆ Ico (k : ℝ) (k + 1) := fun _ hx =>
  ⟨by linarith [hx.1, cutR_nonneg i hi.le], by linarith [hx.2, cutR_le_one (i + 1) hi]⟩

theorem piece_integrable (k i : ℕ) (hi : i < 94) :
    IntegrableOn (fun y : ℝ => hvR i / y ^ 2) (Ico ((k : ℝ) + cutR i) (k + cutR (i + 1))) := by
  by_cases h : hv i = 0
  · have : (fun y : ℝ => hvR i / y ^ 2) = fun _ => 0 := by
      funext y
      simp [hvR, h]
    rw [this]
    exact integrableOn_zero
  · have hc : (1 / 13 : ℝ) ≤ cutR i := by
      have := Rat.cast_le (K := ℝ).2 (hv_pos_cut i hi h)
      push_cast at this
      exact this
    have hsub : Ico ((k : ℝ) + cutR i) (k + cutR (i + 1)) ⊆ Ioi (1 / 14) := fun x hx => by
      rw [Set.mem_Ioi]
      linarith [hx.1, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    refine (IntegrableOn.mono_set (Integrable.const_mul (integrableOn_inv_sq (1 / 14) (by norm_num))
      (hvR i)) hsub).congr_fun (fun x _ => ?_) measurableSet_Ico
    simp only [div_eq_mul_inv]

theorem period_integral (k : ℕ) :
    ∫ x in Ico (k : ℝ) (k + 1), g x =
      ∑ i ∈ range 94, hvR i * ∫ x in Ico ((k : ℝ) + cutR i) (k + cutR (i + 1)), (x ^ 2)⁻¹ := by
  rw [setIntegral_congr_fun measurableSet_Ico (fun x hx => g_eq_sum k x hx),
    integral_finsetSum _ fun i hi =>
      ((piece_integrable k i (mem_range.1 hi)).integrable_indicator measurableSet_Ico).integrableOn]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [integral_indicator measurableSet_Ico, Measure.restrict_restrict measurableSet_Ico,
    inter_eq_left.2 (piece_subset k i (mem_range.1 hi)), ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ico fun x _ => ?_
  simp only [div_eq_mul_inv]

theorem J_eq (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) : ∫ x in Ico a b, (x ^ 2)⁻¹ = a⁻¹ - b⁻¹ := by
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have h : ∫ x in a..b, (x ^ 2)⁻¹ = ∫ x in a..b, x ^ (-2 : ℤ) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [zpow_neg, zpow_ofNat]
  rw [h, integral_zpow (Or.inr ⟨by norm_num, ?_⟩)]
  · norm_num
    ring
  · intro h0
    rw [uIcc_of_le hab] at h0
    linarith [h0.1]

def realTerm (k i : ℕ) : ℝ := hvR i * (((k : ℝ) + cutR i)⁻¹ - ((k : ℝ) + cutR (i + 1))⁻¹)

theorem period_eq (k : ℕ) : ∫ x in Ico (k : ℝ) (k + 1), g x = ∑ i ∈ range 94, realTerm k i := by
  rw [period_integral]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := mem_range.1 hi
  by_cases h : hv i = 0
  · simp [realTerm, hvR, h]
  · have hc : (1 / 13 : ℝ) ≤ cutR i := by
      have := Rat.cast_le (K := ℝ).2 (hv_pos_cut i hi' h)
      push_cast at this
      exact this
    rw [realTerm, J_eq _ _ (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
      (by linarith [cutR_lt i hi'])]

/-! ### Period bounds and the tail -/

theorem term_bounds (k a b : ℝ) (hk : 1 ≤ k) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (b - a) / (k + 1) ^ 2 ≤ (k + a)⁻¹ - (k + b)⁻¹ ∧
      (k + a)⁻¹ - (k + b)⁻¹ ≤ (b - a) / k ^ 2 := by
  have h1 : 0 < k + a := by linarith
  have h2 : 0 < k + b := by linarith
  have e : (k + a)⁻¹ - (k + b)⁻¹ = (b - a) / ((k + a) * (k + b)) := by
    field_simp
    ring
  rw [e]
  constructor
  · exact div_le_div_of_nonneg_left (by linarith) (by positivity) (by nlinarith)
  · exact div_le_div_of_nonneg_left (by linarith) (by positivity) (by nlinarith)

def M : ℝ := 3517 / 4095

theorem sum_cells : ∑ i ∈ range 94, hvR i * (cutR (i + 1) - cutR i) = M := by
  have h : ((∑ i ∈ range 94, hv i * (cut (i + 1) - cut i) : ℚ) : ℝ) = ((3517 / 4095 : ℚ) : ℝ) := by
    rw [mean_eq]
  push_cast at h
  exact h

theorem period_bounds (k : ℕ) (hk : 1 ≤ k) :
    M / ((k : ℝ) + 1) ^ 2 ≤ ∑ i ∈ range 94, realTerm k i ∧
      ∑ i ∈ range 94, realTerm k i ≤ M / (k : ℝ) ^ 2 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rw [← sum_cells, Finset.sum_div, Finset.sum_div]
  constructor
  · refine Finset.sum_le_sum fun i hi => ?_
    have hi' := mem_range.1 hi
    rw [realTerm, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (term_bounds k _ _ hk' (cutR_nonneg i hi'.le)
      (cutR_lt i hi').le (cutR_le_one (i + 1) hi')).1 (hvR_nonneg i hi')
  · refine Finset.sum_le_sum fun i hi => ?_
    have hi' := mem_range.1 hi
    rw [realTerm, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (term_bounds k _ _ hk' (cutR_nonneg i hi'.le)
      (cutR_lt i hi').le (cutR_le_one (i + 1) hi')).2 (hvR_nonneg i hi')

theorem tail_hasSum :
    HasSum (fun n : ℕ => ∑ i ∈ range 94, realTerm (2000 + n) i) (∫ x in Ici (2000 : ℝ), g x) := by
  have hm : ∀ n : ℕ, MeasurableSet (Ico ((2000 : ℝ) + n) ((2000 : ℝ) + n + 1)) := fun _ =>
    measurableSet_Ico
  have hd : Pairwise (Function.onFun Disjoint fun n : ℕ =>
      Ico ((2000 : ℝ) + n) ((2000 : ℝ) + n + 1)) := by
    intro m n hmn
    rcases lt_or_gt_of_ne hmn with h | h
    · have h' : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
      exact Ico_disjoint_Ico.2 ((min_le_left _ _).trans (le_max_of_le_right (by linarith)))
    · have h' : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
      exact Ico_disjoint_Ico.2 ((min_le_right _ _).trans (le_max_of_le_left (by linarith)))
  have hU : (⋃ n : ℕ, Ico ((2000 : ℝ) + n) ((2000 : ℝ) + n + 1)) = Ici (2000 : ℝ) := by
    ext x
    simp only [mem_iUnion, Set.mem_Ico, Set.mem_Ici]
    constructor
    · rintro ⟨n, h1, _⟩
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    · intro hx
      have hx0 : (0 : ℝ) ≤ x - 2000 := by linarith
      refine ⟨⌊x - 2000⌋₊, ?_, ?_⟩
      · have := Nat.floor_le hx0
        linarith
      · have := Nat.lt_floor_add_one (x - 2000)
        linarith
  have hint : IntegrableOn g (⋃ n : ℕ, Ico ((2000 : ℝ) + n) ((2000 : ℝ) + n + 1)) := by
    rw [hU]
    exact (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).2
      (g_integrableOn_Ioi _ (by norm_num))
  have h := hasSum_integral_iUnion hm hd hint
  rw [hU] at h
  convert h using 1
  funext n
  have := period_eq (2000 + n)
  push_cast at this
  exact this.symm

theorem telescope (c : ℝ) (hc : 0 < c) :
    HasSum (fun n : ℕ => 1 / (c + n) - 1 / (c + ((n + 1 : ℕ) : ℝ))) (1 / c) := by
  have hnn : ∀ n : ℕ, 0 ≤ 1 / (c + n) - 1 / (c + ((n + 1 : ℕ) : ℝ)) := fun n => by
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le (by positivity) (by push_cast; linarith)
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hs : ∀ N : ℕ, ∑ n ∈ range N, (1 / (c + n) - 1 / (c + ((n + 1 : ℕ) : ℝ))) =
      1 / (c + ((0 : ℕ) : ℝ)) - 1 / (c + N) := fun N =>
    Finset.sum_range_sub' (fun n : ℕ => 1 / (c + n)) N
  simp only [hs, Nat.cast_zero, add_zero]
  have h0 : Tendsto (fun N : ℕ => 1 / (c + N)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ c tendsto_natCast_atTop_atTop)
  simpa using tendsto_const_nhds.sub h0

theorem tail_lower : M / 2001 ≤ ∫ x in Ici (2000 : ℝ), g x := by
  have hT := (telescope 2001 (by norm_num)).mul_left M
  refine le_trans (le_of_eq ?_) (hasSum_le (fun n => ?_) hT tail_hasSum)
  · ring
  · have hb := (period_bounds (2000 + n) (by omega)).1
    push_cast at hb
    refine le_trans ?_ hb
    rw [div_eq_mul_one_div M]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num [M])
    push_cast
    have hm : (0 : ℝ) < 2001 + n := by positivity
    have e : 1 / (2001 + (n : ℝ)) - 1 / (2001 + (n + 1)) = 1 / ((2001 + n) * (2001 + n + 1)) := by
      field_simp
      ring
    rw [e, show (2000 : ℝ) + n + 1 = 2001 + n by ring]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

theorem tail_upper : ∫ x in Ici (2000 : ℝ), g x ≤ M / 1999 := by
  have hT := (telescope 1999 (by norm_num)).mul_left M
  refine le_trans (hasSum_le (fun n => ?_) tail_hasSum hT) (le_of_eq ?_)
  · have hb := (period_bounds (2000 + n) (by omega)).2
    push_cast at hb
    refine le_trans hb ?_
    rw [div_eq_mul_one_div M]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num [M])
    push_cast
    have hm : (0 : ℝ) < 1999 + n := by positivity
    have e : 1 / (1999 + (n : ℝ)) - 1 / (1999 + (n + 1)) = 1 / ((1999 + n) * (1999 + n + 1)) := by
      field_simp
      ring
    rw [e, show (1999 : ℝ) + n + 1 = 2000 + n by ring]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  · ring

/-! ### The main decomposition -/

theorem gamma_eq : gammaRate =
    (∑ k ∈ range 2000, ∑ i ∈ range 94, realTerm k i) + ∫ x in Ici (2000 : ℝ), g x := by
  have e1 : gammaRate = ∫ x in Ioi (1 / 13 : ℝ), f x := rfl
  have hsub : Ioi (1 / 13 : ℝ) ⊆ Ici 0 := fun x hx =>
    le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 1 / 13) hx)
  rw [e1, integral_f_eq_g _ hsub, ← Ioo_union_Ici_eq_Ioi (by norm_num : (1 / 13 : ℝ) < 2000),
    setIntegral_union
      (Set.disjoint_left.2 fun x hx hx' => absurd (Set.mem_Ici.1 hx') (not_le.2 hx.2))
      measurableSet_Ici ((g_integrableOn_Ioi _ (by norm_num)).mono_set Ioo_subset_Ioi_self)
      ((integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).2
        (g_integrableOn_Ioi _ (by norm_num))),
    ← integral_Ico_eq_integral_Ioo]
  refine congrArg (fun y => y + ∫ x in Ici (2000 : ℝ), g x) ?_
  have h2 : ∫ x in Ico (0 : ℝ) 2000, g x =
      (∫ x in Ico (0 : ℝ) (1 / 13), g x) + ∫ x in Ico (1 / 13 : ℝ) 2000, g x := by
    rw [← Ico_union_Ico_eq_Ico (by norm_num : (0 : ℝ) ≤ 1 / 13) (by norm_num : (1 / 13 : ℝ) ≤ 2000),
      setIntegral_union Ico_disjoint_Ico_same measurableSet_Ico
        ((g_integrableOn_Ico 2000).mono_set fun x hx => ⟨hx.1, by push_cast; linarith [hx.2]⟩)
        ((g_integrableOn_Ico 2000).mono_set fun x hx => ⟨by linarith [hx.1], by
          have := hx.2; push_cast; exact this⟩)]
  have h3 : ∫ x in Ico (0 : ℝ) (1 / 13), g x = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun x hx => g_zero_of_lt x hx.1 hx.2
  rw [h3, zero_add] at h2
  rw [← h2]
  have h4 := integral_Ico_eq_sum 2000
  push_cast at h4
  rw [h4]
  exact Finset.sum_congr rfl fun k _ => period_eq k

end Zeta2GammaInt
