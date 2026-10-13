import Zeta2FourTrajectoryMatrices.Analytic.readout_rates_cone2

open Polynomial Filter Topology Real Finset Zeta2Blueprint Zeta2BoundedGap
open scoped Matrix

noncomputable section

namespace Zeta2Cone

theorem rho_lt_one {Λ : ℝ} (h : HL Λ) : Real.sqrt (gm Λ) < 1 := by
  rw [← Real.sqrt_one]
  exact Real.sqrt_lt_sqrt (gm_pos h).le h.2.2.2

theorem seq_data {Λ : ℝ} (h : HL Λ) (x : ℕ → Fin 3 → ℝ)
    (hx : ∀ᶠ N in atTop, x (N + 1) = x N ᵥ* A N) : ∃ K1 : ℝ, ∃ δ : ℕ → ℝ,
    0 ≤ K1 ∧ (∀ y, ‖Tp Λ y‖ ≤ K1 * ‖y‖) ∧ Tendsto δ atTop (𝓝 0) ∧
    (∀ᶠ N in atTop, |‖Tp Λ (x (N + 1))‖ - Λ * ‖Tp Λ (x N)‖| ≤
      δ N * (‖Tp Λ (x N)‖ + ‖Tq Λ (x N)‖)) ∧
    (∀ᶠ N in atTop, |‖Tq Λ (x (N + 1))‖ - Real.sqrt (gm Λ) * ‖Tq Λ (x N)‖| ≤
      δ N * (‖Tp Λ (x N)‖ + ‖Tq Λ (x N)‖)) := by
  obtain ⟨K1, hK1, hT1⟩ := lin_bd (Tp Λ)
  obtain ⟨K2, hK2, hT2⟩ := lin_bd (Tq Λ)
  have hδ : Tendsto (fun N => max K1 K2 * (1 + (sc Λ)⁻¹) * enr (A N - Ai)) atTop (𝓝 0) := by
    have := enr_tendsto.const_mul (max K1 K2 * (1 + (sc Λ)⁻¹))
    rwa [mul_zero] at this
  refine ⟨K1, fun N => max K1 K2 * (1 + (sc Λ)⁻¹) * enr (A N - Ai),
    hK1, hT1, hδ, ?_, ?_⟩
  · filter_upwards [hx] with N hN
    rw [hN]
    exact step_full (Tp Λ) K1 _ Λ _ hK1 (le_max_left _ _) hT1 (Tp_scale h) (x N) (A N) _
      (norm_split h (x N))
  · filter_upwards [hx] with N hN
    rw [hN]
    exact step_full (Tq Λ) K2 _ _ _ hK2 (le_max_right _ _) hT2 (Tq_scale h) (x N) (A N) _
      (norm_split h (x N))

theorem cone_all_core (Λ : ℝ) (hΛ : 17400086428 < Λ ∧ Λ < 17400086429 ∧
    aeval (-Λ) Ainf.charpoly = 0 ∧ (Zeta2LimitSpectrum.c0 : ℝ) / Λ < 1)
    (x : ℕ → Fin 3 → ℝ) (hx : ∀ᶠ N in atTop, x (N + 1) = x N ᵥ* A N) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ‖x N‖ ≤ exp ((log Λ + ε) * N) := by
  intro ε hε
  have h : HL Λ := hΛ
  have hpos : 0 < Λ := zero_lt_one.trans (one_lt_lam h)
  obtain ⟨K1, δ, _, _, hδ, hA, hB⟩ := seq_data h x hx
  have hθ : Λ < exp (log Λ + ε / 2) := by
    calc Λ = exp (log Λ) := (exp_log hpos).symm
      _ < exp (log Λ + ε / 2) := exp_lt_exp.2 (lt_add_of_pos_right _ (half_pos hε))
  refine rate_bd x _ _ (exp (log Λ + ε / 2)) _ (exp_pos _)
    (by rw [log_exp]; exact (add_lt_add_iff_left _).2 (half_lt_self hε))
    (add_nonneg zero_le_one (inv_nonneg.2 (sc_pos h).le)) (fun N => norm_split h (x N)) ?_
  exact seq_all Λ (Real.sqrt (gm Λ)) ((rho_lt_one h).le.trans (one_lt_lam h).le)
    (fun N => ‖Tp Λ (x N)‖) (fun N => ‖Tq Λ (x N)‖) δ (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) hδ hA hB _ hθ (exp_pos _)

theorem cone_decay_core (Λ : ℝ) (hΛ : 17400086428 < Λ ∧ Λ < 17400086429 ∧
    aeval (-Λ) Ainf.charpoly = 0 ∧ (Zeta2LimitSpectrum.c0 : ℝ) / Λ < 1)
    (x : ℕ → Fin 3 → ℝ) (hx : ∀ᶠ N in atTop, x (N + 1) = x N ᵥ* A N)
    (h0 : Tendsto x atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      ‖x N‖ ≤ exp ((log (Real.sqrt ((Zeta2LimitSpectrum.c0 : ℝ) / Λ)) + ε) * N) := by
  intro ε hε
  have h : HL Λ := hΛ
  have hρ : 0 < Real.sqrt (gm Λ) := Real.sqrt_pos.2 (gm_pos h)
  obtain ⟨K1, δ, hK1, hT1, hδ, hA, hB⟩ := seq_data h x hx
  have ha0 : Tendsto (fun N => ‖Tp Λ (x N)‖) atTop (𝓝 0) := by
    have := (tendsto_zero_iff_norm_tendsto_zero.1 h0).const_mul K1
    rw [mul_zero] at this
    exact squeeze_zero (fun _ => norm_nonneg _) (fun N => hT1 (x N)) this
  have hθ : Real.sqrt (gm Λ) < exp (log (Real.sqrt (gm Λ)) + ε / 2) := by
    calc Real.sqrt (gm Λ) = exp (log (Real.sqrt (gm Λ))) := (exp_log hρ).symm
      _ < exp (log (Real.sqrt (gm Λ)) + ε / 2) :=
        exp_lt_exp.2 (lt_add_of_pos_right _ (half_pos hε))
  refine rate_bd x _ _ (exp (log (Real.sqrt (gm Λ)) + ε / 2)) _ (exp_pos _)
    (by rw [log_exp]; exact (add_lt_add_iff_left _).2 (half_lt_self hε))
    (add_nonneg zero_le_one (inv_nonneg.2 (sc_pos h).le)) (fun N => norm_split h (x N)) ?_
  exact seq_decay Λ (Real.sqrt (gm Λ)) hρ.le (rho_lt_one h) (one_lt_lam h)
    (fun N => ‖Tp Λ (x N)‖) (fun N => ‖Tq Λ (x N)‖) δ (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) hδ ha0 hA hB _ hθ

end Zeta2Cone
