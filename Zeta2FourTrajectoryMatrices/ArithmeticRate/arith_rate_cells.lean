import Zeta2FourTrajectoryMatrices.ArithmeticRate.blueprint_gamma_int
import Zeta2FourTrajectoryMatrices.FiniteReadout.blueprint_next_two

open Filter Topology Real Finset MeasureTheory Zeta2Blueprint Zeta2NextTwo Zeta2GammaTable
  Zeta2GammaInt Zeta2GammaCore

noncomputable section

namespace Zeta2ArithRateCells

def PNTWin : Prop := ∀ a b : ℝ, 0 ≤ a → a ≤ b → Tendsto (fun N : ℕ =>
    (∑ p ∈ (range (⌊b * N⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ a * N < p), log p) / N)
    atTop (𝓝 (b - a))

def cellIco (k i : ℕ) : Set ℝ := Set.Ico ((k : ℝ) + cutR i) (k + cutR (i + 1))

def SF (K N : ℕ) : Finset ℕ := (Sset N).filter (fun p : ℕ => N < K * p)

open Classical in
def Wsum (K N k i : ℕ) : ℝ :=
  ∑ p ∈ (SF K N).filter (fun p : ℕ => (N : ℝ) / p ∈ cellIco k i), log p

def Esum (K N : ℕ) : ℝ :=
  ∑ p ∈ SF K N, (((phi ((N : ℝ) / p)).toNat : ℝ) - Zeta2GammaInt.G ((N : ℝ) / p)) * log p

theorem G_inner (k : ℕ) (x : ℝ) (hx : x ∈ Set.Ico (k : ℝ) (k + 1)) :
    Zeta2GammaInt.G x =
      ∑ i ∈ range 94, hvR i * (cellIco k i).indicator (fun _ => (1 : ℝ)) x := by
  unfold Zeta2GammaInt.G
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fract_eq_sub k x hx]
  by_cases h : x ∈ cellIco k i
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem
      (show x - k ∈ Set.Ico (cutR i) (cutR (i + 1)) from
        ⟨le_sub_iff_add_le'.2 h.1, sub_lt_iff_lt_add'.2 h.2⟩)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem
      (show x - k ∉ Set.Ico (cutR i) (cutR (i + 1)) from
        fun h' => h ⟨le_sub_iff_add_le'.1 h'.1, sub_lt_iff_lt_add'.1 h'.2⟩)]

theorem G_double (K : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hxK : x < K) :
    Zeta2GammaInt.G x = ∑ k ∈ range K, ∑ i ∈ range 94,
      hvR i * (cellIco k i).indicator (fun _ => (1 : ℝ)) x := by
  have hk : x ∈ Set.Ico ((⌊x⌋₊ : ℕ) : ℝ) (⌊x⌋₊ + 1) := ⟨Nat.floor_le hx0, Nat.lt_floor_add_one x⟩
  rw [Finset.sum_eq_single ⌊x⌋₊ (fun k _ hk' => ?_)
    (fun h => absurd (mem_range.2 ((Nat.floor_lt hx0).2 hxK)) h)]
  · exact G_inner _ x hk
  · refine Finset.sum_eq_zero fun i hi => ?_
    rw [Set.indicator_of_notMem, mul_zero]
    intro hc
    exact hk' ((Nat.floor_eq_iff hx0).2 (piece_subset k i (mem_range.1 hi) hc)).symm

theorem mem_SF {K N p : ℕ} (h : p ∈ SF K N) :
    p.Prime ∧ 50 * N < p ^ 2 ∧ 1 ≤ p ∧ p ≤ 13 * N ∧ N < K * p := by
  obtain ⟨h1, h2⟩ := Finset.mem_filter.1 h
  exact ⟨(mem_Sset h1).1, (mem_Sset h1).2.1, (mem_Sset h1).2.2.1, (mem_Sset h1).2.2.2, h2⟩

theorem ratio_bounds {K N p : ℕ} (h : p ∈ SF K N) :
    (0 : ℝ) < p ∧ 0 ≤ (N : ℝ) / p ∧ (N : ℝ) / p < K := by
  obtain ⟨-, -, h1, -, h2⟩ := mem_SF h
  have hp : (0 : ℝ) < p := Nat.cast_pos.2 h1
  refine ⟨hp, div_nonneg (Nat.cast_nonneg N) hp.le, (div_lt_iff₀ hp).2 ?_⟩
  rw [← Nat.cast_mul]
  exact Nat.cast_lt.2 h2

open Classical in
theorem G_sum_eq (K N : ℕ) :
    ∑ p ∈ SF K N, Zeta2GammaInt.G ((N : ℝ) / p) * log p =
      ∑ k ∈ range K, ∑ i ∈ range 94, hvR i * Wsum K N k i := by
  have h1 : ∀ p ∈ SF K N, Zeta2GammaInt.G ((N : ℝ) / p) * log p = ∑ k ∈ range K,
      ∑ i ∈ range 94, hvR i * (if (N : ℝ) / p ∈ cellIco k i then log p else 0) := by
    intro p hp
    obtain ⟨-, h0, hK⟩ := ratio_bounds hp
    rw [G_double K _ h0 hK, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, Set.indicator_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, Wsum, Finset.sum_filter]

theorem cutR_ge (i : ℕ) (hi : i < 94) (h : hv i ≠ 0) : (1 / 13 : ℝ) ≤ cutR i := by
  have := Rat.cast_le (K := ℝ).2 (hv_pos_cut i hi h)
  rw [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at this
  exact this

theorem inv13_pos : (0 : ℝ) < 1 / 13 := one_div_pos.2 Nat.ofNat_pos

theorem inv13_le_one : (1 / 13 : ℝ) ≤ 1 := div_le_self zero_le_one Nat.one_le_ofNat

theorem cast13 (N : ℕ) : ((13 * N : ℕ) : ℝ) = 13 * (N : ℝ) := by
  rw [Nat.cast_mul, Nat.cast_ofNat]

theorem sq_gt (K N p : ℕ) (h50 : 50 * K * K < N) (h : N < K * p) : 50 * N < p ^ 2 := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) h50
  have h1 : K * K * (50 * N) < K * K * p ^ 2 := by
    calc K * K * (50 * N) = 50 * K * K * N := by ac_rfl
      _ < N * N := Nat.mul_lt_mul_of_pos_right h50 hN
      _ < K * p * (K * p) := Nat.mul_self_lt_mul_self h
      _ = K * K * p ^ 2 := by rw [sq]; ac_rfl
  exact Nat.lt_of_mul_lt_mul_left h1

open Classical in
theorem Wsum_eq (K N k i : ℕ) (hk : k < K) (hi : i < 94) (h : hv i ≠ 0)
    (hN : 50 * K * K < N) :
    Wsum K N k i = ∑ p ∈ (range (⌊((k : ℝ) + cutR i)⁻¹ * N⌋₊ + 1)).filter
      (fun p : ℕ => p.Prime ∧ ((k : ℝ) + cutR (i + 1))⁻¹ * N < p), log p := by
  have hα13 : (1 / 13 : ℝ) ≤ k + cutR i :=
    (cutR_ge i hi h).trans (le_add_of_nonneg_left (Nat.cast_nonneg k))
  have hα : (0 : ℝ) < k + cutR i := lt_of_lt_of_le inv13_pos hα13
  have hβ : (0 : ℝ) < k + cutR (i + 1) := hα.trans (add_lt_add_right (cutR_lt i hi) _)
  have hk1 : (k : ℝ) + 1 ≤ K := by
    rw [← Nat.cast_succ]
    exact Nat.cast_le.2 hk
  have hβK : (k : ℝ) + cutR (i + 1) ≤ K :=
    (add_le_add_right (cutR_le_one (i + 1) hi) _).trans hk1
  unfold Wsum
  refine Finset.sum_congr (Finset.ext fun p => ?_) fun _ _ => rfl
  rw [mem_filter, mem_filter, mem_range, Nat.lt_add_one_iff,
    Nat.le_floor_iff (mul_nonneg (inv_nonneg.2 hα.le) (Nat.cast_nonneg N)),
    le_inv_mul_iff₀ hα, inv_mul_lt_iff₀ hβ]
  constructor
  · rintro ⟨hp, h1, h2⟩
    have hp0 := (ratio_bounds hp).1
    exact ⟨(le_div_iff₀ hp0).1 h1, (mem_SF hp).1, (div_lt_iff₀ hp0).1 h2⟩
  · rintro ⟨h1, hpr, h2⟩
    have hp0 : (0 : ℝ) < p := Nat.cast_pos.2 hpr.pos
    have hNK : N < K * p := by
      have : (N : ℝ) < K * p := h2.trans_le (mul_le_mul_of_nonneg_right hβK hp0.le)
      rw [← Nat.cast_mul] at this
      exact Nat.cast_lt.1 this
    have h13 : p ≤ 13 * N := by
      have h3 := mul_le_mul_of_nonneg_right hα13 hp0.le
      rw [one_div_mul_eq_div] at h3
      have : (p : ℝ) ≤ 13 * N := (div_le_iff₀' Nat.ofNat_pos).1 (h3.trans h1)
      rw [← cast13] at this
      exact Nat.cast_le.1 this
    exact ⟨mem_filter.2 ⟨mem_filter.2 ⟨mem_Icc.2 ⟨hpr.one_lt.le, h13⟩, hpr, sq_gt K N p hN hNK⟩,
      hNK⟩, (le_div_iff₀ hp0).2 h1, (div_lt_iff₀ hp0).2 h2⟩

theorem cell_tendsto (hθ : PNTWin) (K k i : ℕ) (hk : k < K) (hi : i < 94) :
    Tendsto (fun N : ℕ => hvR i * Wsum K N k i / N) atTop (𝓝 (realTerm k i)) := by
  by_cases h : hv i = 0
  · have h0 : hvR i = 0 := by rw [hvR, h, Int.cast_zero]
    have e : (fun N : ℕ => hvR i * Wsum K N k i / N) = fun _ => 0 := by
      funext N
      rw [h0, zero_mul, zero_div]
    rw [e, realTerm, h0, zero_mul]
    exact tendsto_const_nhds
  · have hα : (0 : ℝ) < k + cutR i :=
      lt_of_lt_of_le inv13_pos ((cutR_ge i hi h).trans
        (le_add_of_nonneg_left (Nat.cast_nonneg k)))
    have hαβ : (k : ℝ) + cutR i ≤ k + cutR (i + 1) := add_le_add_right (cutR_lt i hi).le _
    have hl := (hθ ((k : ℝ) + cutR (i + 1))⁻¹ ((k : ℝ) + cutR i)⁻¹
      (inv_nonneg.2 (hα.le.trans hαβ)) (inv_anti₀ hα hαβ)).const_mul (hvR i)
    rw [realTerm]
    refine hl.congr' ?_
    filter_upwards [eventually_gt_atTop (50 * K * K)] with N hN
    rw [Wsum_eq K N k i hk hi h hN, mul_div_assoc]

theorem toNat_phi (x : ℝ) : (((phi x).toNat : ℕ) : ℝ) = (phi x : ℝ) := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (phi_nonneg x)]

theorem err_le (K N p : ℕ) (hp : p ∈ SF K N) :
    |((phi ((N : ℝ) / p)).toNat : ℝ) - Zeta2GammaInt.G ((N : ℝ) / p)| * log p ≤
      4 * ∑ k ∈ range K, ∑ i ∈ range 95,
        (if (N : ℝ) / p = k + cutR i then log p else 0) := by
  obtain ⟨-, h0, hK⟩ := ratio_bounds hp
  have hlog : 0 ≤ log (p : ℝ) := Real.log_natCast_nonneg p
  have hnn : ∀ k ∈ range K, ∀ i ∈ range 95,
      0 ≤ (if (N : ℝ) / p = k + cutR i then log p else 0) := fun k _ i _ => by
    split_ifs
    exacts [hlog, le_rfl]
  rw [toNat_phi]
  by_cases hc : (N : ℝ) / p ∈ cutpts
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hc
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 hk
    have hx' := Set.mem_singleton_iff.1 hx
    have hi' : i < 95 := mem_range.1 hi
    have hkK : k < K := by
      have h1 : (k : ℝ) ≤ (N : ℝ) / p := by
        rw [hx']
        exact le_add_of_nonneg_right (cutR_nonneg i (by omega))
      exact Nat.cast_lt.1 (h1.trans_lt hK)
    have hs : log p ≤ ∑ k ∈ range K, ∑ i ∈ range 95,
        (if (N : ℝ) / p = k + cutR i then log p else 0) := by
      refine le_trans ?_ (Finset.single_le_sum (fun k hk => Finset.sum_nonneg (hnn k hk))
        (mem_range.2 hkK))
      exact le_trans (le_of_eq (ite_eq_left hx').symm)
        (Finset.single_le_sum (hnn k (mem_range.2 hkK)) hi)
    have hG := G_bounds ((N : ℝ) / p)
    have hφ0 : (0 : ℝ) ≤ phi ((N : ℝ) / p) := Int.cast_nonneg (phi_nonneg _)
    have hφ4 : (phi ((N : ℝ) / p) : ℝ) ≤ 4 := by
      have := Int.cast_le (R := ℝ).2 (phi_le_four ((N : ℝ) / p))
      rwa [Int.cast_ofNat] at this
    have habs : |(phi ((N : ℝ) / p) : ℝ) - Zeta2GammaInt.G ((N : ℝ) / p)| ≤ 4 :=
      abs_sub_le_iff.2 ⟨(sub_le_self _ hG.1).trans hφ4,
        (sub_le_self _ hφ0).trans (hG.2.trans (Nat.ofNat_le.2 (by omega)))⟩
    exact mul_le_mul habs hs hlog zero_le_four
  · rw [phi_eq_G _ h0 hc, sub_self, abs_zero, zero_mul]
    exact mul_nonneg zero_le_four
      (Finset.sum_nonneg fun k hk => Finset.sum_nonneg (hnn k hk))

theorem point_sum_le (K N : ℕ) (hN : 1 ≤ N) (y : ℝ) :
    ∑ p ∈ (SF K N).filter (fun p : ℕ => (N : ℝ) / p = y), log p ≤ log (13 * (N : ℝ)) := by
  have hcard : ((SF K N).filter (fun p : ℕ => (N : ℝ) / p = y)).card ≤ 1 := by
    refine Finset.card_le_one.2 fun a ha b hb => ?_
    obtain ⟨ha1, ha2⟩ := mem_filter.1 ha
    obtain ⟨hb1, hb2⟩ := mem_filter.1 hb
    have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have e := (div_eq_div_iff (ratio_bounds ha1).1.ne' (ratio_bounds hb1).1.ne').1
      (ha2.trans hb2.symm)
    exact (Nat.cast_injective (mul_left_cancel₀ hN0 e)).symm
  have hle : ∀ p ∈ (SF K N).filter (fun p : ℕ => (N : ℝ) / p = y), log p ≤ log (13 * (N : ℝ)) := by
    intro p hp
    obtain ⟨-, -, h1, h2, -⟩ := mem_SF (mem_filter.1 hp).1
    exact Real.log_le_log (Nat.cast_pos.2 h1) (cast13 N ▸ Nat.cast_le.2 h2)
  have h0 : 0 ≤ log (13 * (N : ℝ)) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le Nat.one_le_ofNat (Nat.one_le_cast.2 hN))
  calc _ ≤ _ • log (13 * (N : ℝ)) := Finset.sum_le_card_nsmul _ _ _ hle
    _ ≤ 1 • log (13 * (N : ℝ)) := nsmul_le_nsmul_left h0 hcard
    _ = _ := one_nsmul _

theorem Esum_abs_le (K N : ℕ) (hN : 1 ≤ N) :
    |Esum K N| ≤ 4 * (K * 95) * log (13 * (N : ℝ)) := by
  have h1 : |Esum K N| ≤ ∑ p ∈ SF K N, 4 * ∑ k ∈ range K, ∑ i ∈ range 95,
      (if (N : ℝ) / p = k + cutR i then log p else 0) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
    rw [abs_mul, abs_of_nonneg (Real.log_natCast_nonneg p)]
    exact err_le K N p hp
  have h2 : ∑ p ∈ SF K N, 4 * ∑ k ∈ range K, ∑ i ∈ range 95,
      (if (N : ℝ) / p = k + cutR i then log p else 0) = 4 * ∑ k ∈ range K, ∑ i ∈ range 95,
        ∑ p ∈ (SF K N).filter (fun p : ℕ => (N : ℝ) / p = k + cutR i), log p := by
    rw [← Finset.mul_sum]
    exact congrArg (4 * ·) (Finset.sum_comm.trans (Finset.sum_congr rfl fun k _ =>
      Finset.sum_comm.trans (Finset.sum_congr rfl fun i _ => (Finset.sum_filter _ _).symm)))
  have h3 : ∑ k ∈ range K, ∑ i ∈ range 95,
      ∑ p ∈ (SF K N).filter (fun p : ℕ => (N : ℝ) / p = k + cutR i), log p ≤
        K * 95 * log (13 * (N : ℝ)) := by
    calc _ ≤ ∑ k ∈ range K, ∑ i ∈ range 95, log (13 * (N : ℝ)) :=
          Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun i _ => point_sum_le K N hN _
      _ = _ := by
        rw [Finset.sum_const, Finset.sum_const, card_range, card_range, nsmul_eq_mul,
          nsmul_eq_mul, Nat.cast_ofNat, mul_assoc]
  rw [mul_assoc]
  calc |Esum K N| ≤ _ := h1
    _ = _ := h2
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 zero_le_four

theorem log_div_tendsto : Tendsto (fun N : ℕ => log (13 * (N : ℝ)) / N) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop (1 / 13) 0 1 inv13_pos.ne').comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop (Nat.ofNat_pos : (0 : ℝ) < 13))
  refine h.congr fun N => ?_
  rw [Function.comp_apply, pow_one, add_zero, ← mul_assoc, one_div,
    inv_mul_cancel₀ (Nat.ofNat_pos : (0 : ℝ) < 13).ne', one_mul]

theorem Esum_tendsto (K : ℕ) : Tendsto (fun N : ℕ => Esum K N / N) atTop (𝓝 0) := by
  have h := log_div_tendsto.const_mul (4 * (K * 95 : ℝ))
  rw [mul_zero] at h
  refine squeeze_zero_norm' ?_ h
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [Real.norm_eq_abs, abs_div, Nat.abs_cast, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right (Esum_abs_le K N hN) (Nat.cast_nonneg N)

theorem S_split (K N : ℕ) : ∑ p ∈ SF K N, ((phi ((N : ℝ) / p)).toNat : ℝ) * log p =
    ∑ k ∈ range K, ∑ i ∈ range 94, hvR i * Wsum K N k i + Esum K N := by
  rw [← G_sum_eq, Esum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [sub_mul, add_sub_cancel]

theorem S_tendsto (hθ : PNTWin) (K : ℕ) :
    Tendsto (fun N : ℕ => (∑ p ∈ SF K N, ((phi ((N : ℝ) / p)).toNat : ℝ) * log p) / N) atTop
      (𝓝 (∑ k ∈ range K, ∑ i ∈ range 94, realTerm k i)) := by
  have hm : Tendsto (fun N : ℕ => ∑ k ∈ range K, ∑ i ∈ range 94, hvR i * Wsum K N k i / N)
      atTop (𝓝 (∑ k ∈ range K, ∑ i ∈ range 94, realTerm k i)) :=
    tendsto_finsetSum _ fun k hk => tendsto_finsetSum _ fun i hi =>
      cell_tendsto hθ K k i (mem_range.1 hk) (mem_range.1 hi)
  have h := hm.add (Esum_tendsto K)
  rw [add_zero] at h
  refine h.congr fun N => ?_
  rw [S_split, add_div, Finset.sum_div]
  refine congrArg (· + Esum K N / N) (Finset.sum_congr rfl fun k _ => ?_)
  rw [Finset.sum_div]

theorem integral_cells (K : ℕ) (hK : 1 ≤ K) :
    ∫ x in Set.Ioo (1 / 13 : ℝ) K, (phi x : ℝ) / x ^ 2 =
      ∑ k ∈ range K, ∑ i ∈ range 94, realTerm k i := by
  have hK1 : (1 : ℝ) ≤ K := Nat.one_le_cast.2 hK
  have hK' : (1 / 13 : ℝ) ≤ K := inv13_le_one.trans hK1
  have hsub : Set.Ioo (1 / 13 : ℝ) K ⊆ Set.Ici 0 := fun x hx =>
    (inv13_pos.trans hx.1).le
  have e1 := integral_f_eq_g _ hsub
  change ∫ x in Set.Ioo (1 / 13 : ℝ) K, Zeta2GammaInt.f x = _
  rw [e1, ← integral_Ico_eq_integral_Ioo]
  have h2 : ∫ x in Set.Ico (0 : ℝ) K, Zeta2GammaInt.g x =
      (∫ x in Set.Ico (0 : ℝ) (1 / 13), Zeta2GammaInt.g x) +
        ∫ x in Set.Ico (1 / 13 : ℝ) K, Zeta2GammaInt.g x := by
    rw [← Set.Ico_union_Ico_eq_Ico inv13_pos.le hK',
      setIntegral_union Set.Ico_disjoint_Ico_same measurableSet_Ico
        ((g_integrableOn_Ico K).mono_set (Set.Ico_subset_Ico_right hK'))
        ((g_integrableOn_Ico K).mono_set (Set.Ico_subset_Ico_left inv13_pos.le))]
  have h3 : ∫ x in Set.Ico (0 : ℝ) (1 / 13), Zeta2GammaInt.g x = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun x hx => g_zero_of_lt x hx.1 hx.2
  rw [h3, zero_add] at h2
  rw [← h2, integral_Ico_eq_sum K]
  exact Finset.sum_congr rfl fun k _ => period_eq k

theorem GN_sum_truncated_core
    (hθ : ∀ a b : ℝ, 0 ≤ a → a ≤ b → Tendsto (fun N : ℕ =>
      (∑ p ∈ (range (⌊b * N⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ a * N < p), log p) / N)
      atTop (𝓝 (b - a)))
    (K : ℕ) (hK : 1 ≤ K) :
    Tendsto (fun N : ℕ => (∑ p ∈ (Sset N).filter (fun p => N < K * p),
        ((phi ((N : ℝ) / p)).toNat : ℝ) * log p) / N) atTop
      (𝓝 (∫ x in Set.Ioo (1 / 13 : ℝ) K, (phi x : ℝ) / x ^ 2)) := by
  rw [integral_cells K hK]
  exact S_tendsto hθ K

end Zeta2ArithRateCells
