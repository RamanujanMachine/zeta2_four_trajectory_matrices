import Zeta2FourTrajectoryMatrices.Analytic.readout_rates_cone

open Polynomial Filter Topology Real Finset Zeta2Blueprint Zeta2BoundedGap
open scoped Matrix

noncomputable section

namespace Zeta2Cone

def enr (E : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := ∑ j, ∑ i, ‖E i j‖

theorem enr_nonneg (E : Matrix (Fin 3) (Fin 3) ℝ) : 0 ≤ enr E :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _

theorem vecMul_le (x : Fin 3 → ℝ) (E : Matrix (Fin 3) (Fin 3) ℝ) : ‖x ᵥ* E‖ ≤ enr E * ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (enr_nonneg E) (norm_nonneg _))).2 fun j => ?_
  calc ‖(x ᵥ* E) j‖ = ‖∑ i, x i * E i j‖ := rfl
    _ ≤ ∑ i, ‖x i * E i j‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖E i j‖ * ‖x‖ := sum_le_sum fun i _ => by
        rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x i) (norm_nonneg _)
    _ = (∑ i, ‖E i j‖) * ‖x‖ := (sum_mul _ _ _).symm
    _ ≤ enr E * ‖x‖ := mul_le_mul_of_nonneg_right (single_le_sum (f := fun j => ∑ i, ‖E i j‖)
        (fun _ _ => sum_nonneg fun _ _ => norm_nonneg _) (mem_univ j)) (norm_nonneg _)

theorem enr_tendsto : Tendsto (fun N => enr (A N - Ai)) atTop (𝓝 0) := by
  have h : Tendsto (fun N => A N - Ai) atTop (𝓝 0) := tendsto_sub_nhds_zero_iff.2 A_tendsto
  have hc : Continuous enr := continuous_finsetSum _ fun j _ =>
    continuous_finsetSum _ fun i _ => (continuous_id.matrix_elem i j).norm
  have h0 : enr 0 = 0 := sum_eq_zero fun _ _ => sum_eq_zero fun _ _ => by
    rw [Matrix.zero_apply, norm_zero]
  have := (hc.tendsto 0).comp h
  rwa [h0] at this

theorem lin_bd {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : (Fin 3 → ℝ) →ₗ[ℝ] F) : ∃ K, 0 ≤ K ∧ ∀ y, ‖f y‖ ≤ K * ‖y‖ :=
  ⟨‖LinearMap.toContinuousLinearMap f‖, norm_nonneg _,
    fun y => (LinearMap.toContinuousLinearMap f).le_opNorm y⟩

theorem step_full {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : (Fin 3 → ℝ) →ₗ[ℝ] F) (Kf K c K0 : ℝ) (hKf : 0 ≤ Kf) (hKK : Kf ≤ K)
    (hK : ∀ y, ‖f y‖ ≤ Kf * ‖y‖) (hc : ∀ y, ‖f (y ᵥ* Ai)‖ = c * ‖f y‖) (x : Fin 3 → ℝ)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) (hs : ‖x‖ ≤ K0 * s) :
    |‖f (x ᵥ* B)‖ - c * ‖f x‖| ≤ K * K0 * enr (B - Ai) * s := by
  have hB : x ᵥ* B = x ᵥ* Ai + x ᵥ* (B - Ai) := by rw [← Matrix.vecMul_add, add_sub_cancel]
  rw [hB, map_add, ← hc]
  calc |‖f (x ᵥ* Ai) + f (x ᵥ* (B - Ai))‖ - ‖f (x ᵥ* Ai)‖|
      ≤ ‖f (x ᵥ* Ai) + f (x ᵥ* (B - Ai)) - f (x ᵥ* Ai)‖ := abs_norm_sub_norm_le _ _
    _ = ‖f (x ᵥ* (B - Ai))‖ := by rw [add_sub_cancel_left]
    _ ≤ Kf * ‖x ᵥ* (B - Ai)‖ := hK _
    _ ≤ K * (enr (B - Ai) * (K0 * s)) := mul_le_mul hKK
        ((vecMul_le _ _).trans (mul_le_mul_of_nonneg_left hs (enr_nonneg _)))
        (norm_nonneg _) (hKf.trans hKK)
    _ = K * K0 * enr (B - Ai) * s := by ring

theorem geom_bd (s : ℕ → ℝ) (θ : ℝ) (hθ : 0 < θ) (h : ∀ᶠ N in atTop, s (N + 1) ≤ θ * s N) :
    ∃ C, ∀ᶠ N in atTop, s N ≤ C * θ ^ N := by
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 h
  refine ⟨s N0 / θ ^ N0, eventually_atTop.2 ⟨N0, fun N hN => ?_⟩⟩
  induction N, hN using Nat.le_induction with
  | base => exact (div_mul_cancel₀ _ (pow_ne_zero _ hθ.ne')).ge
  | succ n hn ih =>
    calc s (n + 1) ≤ θ * s n := hN0 n hn
      _ ≤ θ * (s N0 / θ ^ N0 * θ ^ n) := mul_le_mul_of_nonneg_left ih hθ.le
      _ = s N0 / θ ^ N0 * θ ^ (n + 1) := by rw [pow_succ]; ring

theorem rate_bd (x : ℕ → Fin 3 → ℝ) (s : ℕ → ℝ) (K θ L : ℝ) (hθ : 0 < θ) (hL : log θ < L)
    (hK : 0 ≤ K) (hxs : ∀ N, ‖x N‖ ≤ K * s N) (hs : ∃ C, ∀ᶠ N in atTop, s N ≤ C * θ ^ N) :
    ∀ᶠ N : ℕ in atTop, ‖x N‖ ≤ exp (L * N) := by
  obtain ⟨C, hC⟩ := hs
  have ht : Tendsto (fun N : ℕ => exp ((L - log θ) * N)) atTop atTop :=
    tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop (sub_pos.2 hL))
  filter_upwards [hC, ht.eventually_ge_atTop (K * C)] with N hN hE
  have hp : θ ^ N = exp (log θ * N) := by rw [mul_comm, Real.exp_nat_mul, exp_log hθ]
  calc ‖x N‖ ≤ K * s N := hxs N
    _ ≤ K * (C * θ ^ N) := mul_le_mul_of_nonneg_left hN hK
    _ = K * C * exp (log θ * N) := by rw [hp, mul_assoc]
    _ ≤ exp ((L - log θ) * N) * exp (log θ * N) := mul_le_mul_of_nonneg_right hE (exp_pos _).le
    _ = exp (L * N) := by rw [← exp_add, ← add_mul, sub_add_cancel]

theorem seq_all (Λ ρ : ℝ) (hρΛ : ρ ≤ Λ) (a b δ : ℕ → ℝ) (ha : ∀ N, 0 ≤ a N) (hb : ∀ N, 0 ≤ b N)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hA : ∀ᶠ N in atTop, |a (N + 1) - Λ * a N| ≤ δ N * (a N + b N))
    (hB : ∀ᶠ N in atTop, |b (N + 1) - ρ * b N| ≤ δ N * (a N + b N)) (θ : ℝ) (hθ : Λ < θ)
    (hθ0 : 0 < θ) : ∃ C, ∀ᶠ N in atTop, a N + b N ≤ C * θ ^ N := by
  refine geom_bd _ θ hθ0 ?_
  filter_upwards [hA, hB, (tendsto_order.1 hδ).2 ((θ - Λ) / 2) (half_pos (sub_pos.2 hθ))]
    with N h1 h2 h3
  have e1 := (abs_le.1 h1).2
  have e2 := (abs_le.1 h2).2
  have e3 : δ N * (a N + b N) ≤ (θ - Λ) / 2 * (a N + b N) :=
    mul_le_mul_of_nonneg_right h3.le (add_nonneg (ha N) (hb N))
  have e4 : ρ * b N ≤ Λ * b N := mul_le_mul_of_nonneg_right hρΛ (hb N)
  linarith

theorem cone_trap (Λ ρ η : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hη : 0 < η) (hη4 : 4 * η ≤ Λ - 1)
    (a b δ : ℕ → ℝ) (ha : ∀ N, 0 ≤ a N) (hb : ∀ N, 0 ≤ b N) (N1 : ℕ)
    (hN1 : ∀ N ≥ N1, |a (N + 1) - Λ * a N| ≤ δ N * (a N + b N) ∧
      |b (N + 1) - ρ * b N| ≤ δ N * (a N + b N) ∧ δ N < η)
    (N2 : ℕ) (hN2 : N1 ≤ N2) (hlt : b N2 < a N2) : ∀ N ≥ N2, b N < a N ∧ a N2 ≤ a N := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => exact ⟨hlt, le_rfl⟩
  | succ n hn ih =>
    obtain ⟨h1, h2, h3⟩ := hN1 n (hN2.trans hn)
    have e1 := (abs_le.1 h1).1
    have e2 := (abs_le.1 h2).2
    have hpos : 0 < a n := (hb n).trans_lt ih.1
    have e3 : δ n * (a n + b n) ≤ η * (2 * a n) :=
      (mul_le_mul_of_nonneg_right h3.le (add_nonneg (ha n) (hb n))).trans
        (mul_le_mul_of_nonneg_left (by linarith [ih.1]) hη.le)
    have e5 : ρ * b n ≤ ρ * a n := mul_le_mul_of_nonneg_left ih.1.le hρ0
    have e6 : ρ * a n < a n := mul_lt_of_lt_one_left hpos hρ1
    have e7 : 4 * η * a n ≤ (Λ - 1) * a n := mul_le_mul_of_nonneg_right hη4 (ha n)
    have e8 : 0 ≤ η * a n := mul_nonneg hη.le (ha n)
    exact ⟨by linarith, by linarith [ih.2]⟩

theorem seq_decay (Λ ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hΛ : 1 < Λ) (a b δ : ℕ → ℝ)
    (ha : ∀ N, 0 ≤ a N) (hb : ∀ N, 0 ≤ b N) (hδ : Tendsto δ atTop (𝓝 0))
    (ha0 : Tendsto a atTop (𝓝 0))
    (hA : ∀ᶠ N in atTop, |a (N + 1) - Λ * a N| ≤ δ N * (a N + b N))
    (hB : ∀ᶠ N in atTop, |b (N + 1) - ρ * b N| ≤ δ N * (a N + b N)) (θ : ℝ) (hθ : ρ < θ) :
    ∃ C, ∀ᶠ N in atTop, a N + b N ≤ C * θ ^ N := by
  have hη : 0 < min ((θ - ρ) / 2) ((Λ - 1) / 4) := lt_min (half_pos (sub_pos.2 hθ)) (by linarith)
  have hη1 : min ((θ - ρ) / 2) ((Λ - 1) / 4) ≤ (θ - ρ) / 2 := min_le_left _ _
  have hη4 : 4 * min ((θ - ρ) / 2) ((Λ - 1) / 4) ≤ Λ - 1 := by
    linarith [min_le_right ((θ - ρ) / 2) ((Λ - 1) / 4)]
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (hA.and (hB.and ((tendsto_order.1 hδ).2 _ hη)))
  have key : ∀ N ≥ N1, a N ≤ b N := by
    intro N2 hN2
    by_contra hc
    have tr := cone_trap Λ ρ _ hρ0 hρ1 hη hη4 a b δ ha hb N1 hN1 N2 hN2 (lt_of_not_ge hc)
    obtain ⟨M, hM⟩ := eventually_atTop.1
      ((tendsto_order.1 ha0).2 (a N2) ((hb N2).trans_lt (lt_of_not_ge hc)))
    exact lt_irrefl _ ((tr (max M N2) (le_max_right _ _)).2.trans_lt (hM _ (le_max_left _ _)))
  obtain ⟨C, hC⟩ := geom_bd b θ (hρ0.trans_lt hθ) (eventually_atTop.2 ⟨N1, fun N hN => by
    obtain ⟨_, h2, h3⟩ := hN1 N hN
    have e2 := (abs_le.1 h2).2
    have e3 : δ N * (a N + b N) ≤ min ((θ - ρ) / 2) ((Λ - 1) / 4) * (2 * b N) :=
      (mul_le_mul_of_nonneg_right h3.le (add_nonneg (ha N) (hb N))).trans
        (mul_le_mul_of_nonneg_left (by linarith [key N hN]) hη.le)
    have e4 : 2 * min ((θ - ρ) / 2) ((Λ - 1) / 4) * b N ≤ (θ - ρ) * b N :=
      mul_le_mul_of_nonneg_right (by linarith) (hb N)
    linarith⟩)
  refine ⟨2 * C, ?_⟩
  filter_upwards [hC, eventually_ge_atTop N1] with N hN hN'
  linarith [key N hN']

end Zeta2Cone
