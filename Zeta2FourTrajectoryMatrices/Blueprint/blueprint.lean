/-
# Blueprint: CMF conservation and an irrationality measure for `ζ(2)`

This file is a Lean blueprint of the article
  *"CMF conservation as an arithmetic tool — A proof of `μ(ζ(2)) < 4.62675` for the direction
  `(10,9,11,-11;2,1,3)`"* (10 October 2026),
  `results/zeta2_complete_proof/zeta2_complete_proof.tex`.

Main theorem (§6.6 of the article, `main_theorem` below):
  `μ(ζ(2)) ≤ 1 + σ/τ = 62636575/13537936 < 4.62675`.

Structure (following the sections of the article):

* §1  Conservation and the `2 × 2` toy field (`toy_conservation`).
* §3  The native `₄F₃(1)` field, the four-block route, the readout matrix `R` and the exact
      finite readout (Appendix A) (`route_independent`, `readout_formula`).
* §4  Arithmetic normalisation: baseline (Appendix B), the six prime shells via a finite-field
      polynomial (Appendix D) (`baseline_integrality`, `polyQ_factor`, `sum_eval_eq_zero`,
      `arithmetic_normalization`).
* §5  The exponential cost of the normalisation (Appendix E)
      (`shell_lengths`, `gamma_bounds`, `arith_rate`, `kN_rate`).
* §6  Analytic estimates: Barnes integral, coarse bound, limiting matrix, cone argument,
      bounded-gap independence (`barnes_identities`, `error_integral`, `error_coarse_bound`,
      `limit_spectrum`, `readout_rates`, `bounded_gap`).
* §6.6 The irrationality-measure deduction (`irrMeasure_criterion`, `zeta2_irrMeasureLE`,
      `main_theorem`).

There are exactly 20 `theorem`s (blueprint nodes). Nodes whose content is a genuine piece of the
article's mathematics are left as `sorry`; the elementary nodes (`toy_conservation`,
`sum_eval_eq_zero`, `shell_lengths`) and the logical glue (`kN_rate`, `zeta2_irrMeasureLE`,
`main_theorem`) are proved here from the other nodes.

Conventions. Row vectors are multiplied on the right. A vertex of the `pFq(4,3,1)` field is
`w = (x₀,x₁,x₂,x₃; y₀,y₁,y₂)` with `x₃ = -m`; we index the seven coordinates by
`Fin 4 ⊕ Fin 3`. Mathlib has no irrationality measure, so `IrrMeasureLE` and
`irrationalityMeasure` are defined below, following the definition at the end of §6.6.
-/
import Zeta2FourTrajectoryMatrices.Blueprint.defs
import Zeta2FourTrajectoryMatrices.FiniteReadout.blueprint_first_three
import Zeta2FourTrajectoryMatrices.FiniteReadout.blueprint_next_two
import Zeta2FourTrajectoryMatrices.ArithmeticNormalization.arithmetic_normalization
import Zeta2FourTrajectoryMatrices.ArithmeticRate.blueprint_gamma_bounds
import Zeta2FourTrajectoryMatrices.ArithmeticRate.arith_rate
import Zeta2FourTrajectoryMatrices.Analytic.barnes_identities
import Zeta2FourTrajectoryMatrices.Analytic.error_integral
import Zeta2FourTrajectoryMatrices.Analytic.error_coarse_bound
import Zeta2FourTrajectoryMatrices.Analytic.blueprint_limit_spectrum
import Zeta2FourTrajectoryMatrices.Analytic.readout_rates
import Zeta2FourTrajectoryMatrices.Analytic.blueprint_bounded_gap
import Zeta2FourTrajectoryMatrices.IrrationalityMeasure.blueprint_irr_criterion

open Polynomial Filter Topology Real Finset MeasureTheory
open scoped Matrix

noncomputable section

namespace Zeta2Blueprint

/-! ## §1. Conservation: an exact `2 × 2` toy field -/

/-- **Toy example (§1.2).** `A, B, C, D` are the edge matrices of the potential `F`
(`F(0,0) = I`, `F(1,0) = A`, `F(0,1) = B`, `F(1,0) C = F(0,1) D = F(1,1)`), the two paths
around the square have the same endpoint `W = AC = BD = 6 I₂`, and yet `AB ≠ BA`. -/
theorem toy_conservation :
    toyPot 0 0 = 1 ∧ toyPot 1 0 = toyA ∧ toyPot 0 1 = toyB ∧
    toyPot 1 0 * toyC = toyPot 1 1 ∧ toyPot 0 1 * toyD = toyPot 1 1 ∧
    toyPot 1 1 = (6 : ℚ) • 1 ∧ toyA * toyB ≠ toyB * toyA := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [toyPot]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [toyPot, toyA] <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [toyPot, toyB] <;> norm_num
  · rw [toyPot, toyC, Matrix.mul_fin_two, toyPot]; ext i j
    fin_cases i <;> fin_cases j <;> simp <;> norm_num
  · rw [toyPot, toyD, Matrix.mul_fin_two, toyPot]; ext i j
    fin_cases i <;> fin_cases j <;> simp <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [toyPot] <;> norm_num
  · rw [toyA, toyB, Matrix.mul_fin_two, Matrix.mul_fin_two]
    intro h
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ => M 0 0) h
    norm_num at this

/-! ## §3. The native field `pFq(4,3,1)` and the specified trajectory -/

/-- **Conservation along the two routes (§3.1, Appendix A.7).** The `t = 3` and `t = 4`
four-block routes are regular and have the same endpoint product. -/
theorem route_independent (N : ℕ) : walk w0 (route 3 N) = walk w0 (route 4 N) :=
  Zeta2FirstThree.route_independent N

/-! ### The exact finite readout (§3.2, Appendix A) -/

/-- **Exact native readout (1)** (§3.2, proved uniformly in Appendix A): for every admissible
shift `2N ≤ η ≤ 9N`,
`C_N R W(N) e_r = 2 (∑ j^r c_j H^{(2)}_{j+η} + J_η(S_r), ∑ j^r c_j)`.
Appendix A: the two identities for `J_η`, the shift `S_D(s) = S_A(s+1)`, the companion
relation `ℓ_η(Q) = 0`, independence of `η`, and induction over the three move types. -/
theorem readout_formula (N : ℕ) (r : Fin 3) (η : ℕ) (hη₁ : 2 * N ≤ η) (hη₂ : η ≤ 9 * N) :
    (CN N : ℚ) • (fun i => readout N i r) =
      ![2 * (∑ j ∈ range (11 * N + 1), (j : ℚ) ^ (r : ℕ) * cj N j * harm2 (j + η) +
          Jfun η (Spoly N r)),
        2 * ∑ j ∈ range (11 * N + 1), (j : ℚ) ^ (r : ℕ) * cj N j] :=
  Zeta2FirstThree.readout_formula N r η hη₁ hη₂

/-! ## §4. The arithmetic normalisation -/

/-- **Baseline arithmetic (3)** (Appendix B): `C_N d_{12N} d_{13N+r} / G_N · R W(N) e_r ∈ ℤ²`.
Denominators are cleared via integer-valued binomial bases and one harmonic carry; the common
divisor `p^{φ(N/p)}` is transferred through Newton coefficients. -/
theorem baseline_integrality (N : ℕ) (hN : 1 ≤ N) (r : Fin 3) :
    ∃ z : Fin 2 → ℤ, ∀ i,
      ((CN N * lcmUpTo (12 * N) * lcmUpTo (13 * N + r) : ℕ) / (GN N : ℚ)) * readout N i r =
        z i :=
  Zeta2NextTwo.baseline_integrality N hN r

/-- **The finite-field quotient (Q) and its degree** (Appendix D). For a shell prime `p`
(with `8N = ap + b`, `11N = Mp + d`, `h = φ(N/p)`), the polynomial
`𝒬 = ∏_{u=9}^{11} binom(X+uN, b) / ((X^p - X)^{h-1} ∏_{j=0}^{d} (X - j))` lies in `𝔽_p[X]`
(by the carry lower bound and root multiplicities; for `h = 0` read it as multiplication by
`X^p - X`), and `deg(X^r 𝒬) = 13N + r - (K-1)p - 1 < p - 1`. -/
theorem polyQ_factor (N r p : ℕ) [Fact p.Prime] (hN : 1 ≤ N) (hr : r < 3)
    (hp : 50 * N < p ^ 2) (hshell : InShell N r p) :
    let b := 8 * N % p
    let d := 11 * N % p
    let h := (phi ((N : ℝ) / p)).toNat
    let f : (ZMod p)[X] := binomPoly (ZMod p) ((9 * N : ℕ) : ZMod p) b *
      binomPoly (ZMod p) ((10 * N : ℕ) : ZMod p) b * binomPoly (ZMod p) ((11 * N : ℕ) : ZMod p) b
    let g : (ZMod p)[X] := ∏ j ∈ range (d + 1), (X - C (j : ZMod p))
    ∃ 𝒬 : (ZMod p)[X], f * (X ^ p - X) ^ (1 - h) = (X ^ p - X) ^ (h - 1) * g * 𝒬 ∧
      (X ^ r * 𝒬).natDegree < p - 1 :=
  Zeta2NextTwo.polyQ_factor N r p hN hr hp hshell

/-- **Vanishing sum (V)** (Appendix D). A polynomial over `𝔽_p` of degree `< p - 1` has
`∑_{k ∈ 𝔽_p} 𝒬(k) = 0`. -/
theorem sum_eval_eq_zero (p : ℕ) [Fact p.Prime] (𝒬 : (ZMod p)[X])
    (hdeg : 𝒬.natDegree < p - 1) : ∑ k : ZMod p, 𝒬.eval k = 0 := by
  simp_rw [eval_eq_sum_range]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [← Finset.mul_sum, FiniteField.sum_pow_lt_card_sub_one, mul_zero]
  rw [ZMod.card]
  have := Finset.mem_range.1 hi
  omega

/-- **Theorem 1 (Arithmetic of the native readouts)** (§4, Appendices B and D):
`C_N d_{12N} d_{13N+r} / (G_N H_{N,r}) · R W(N) e_r ∈ ℤ²`.
Proof: `baseline_integrality`, plus one extra factor of every shell prime: the local kernel
factorisation `p^{1-h} R(k + pV) ≡ κ 𝒬(k) U(V)` (floor-cell table (T)), the readout with
`η = p` or `2p`, `polyQ_factor` and `sum_eval_eq_zero`. -/
theorem arithmetic_normalization (N : ℕ) (hN : 1 ≤ N) (r : Fin 3) :
    ∃ z : Fin 2 → ℤ, ∀ i,
      ((CN N * lcmUpTo (12 * N) * lcmUpTo (13 * N + r) : ℕ) / (GN N * HN N r : ℕ) : ℚ) *
        readout N i r = z i :=
  Zeta2ArithmeticNormalization.arithmetic_normalization N hN r

/-! ## §5. The exponential cost of the arithmetic normalisation -/

/-- **Total shell length (§5)**: the six interval lengths, divided by `N`, sum to `233/120`. -/
theorem shell_lengths :
    (8 - 13 / 2 : ℚ) + (9 / 2 - 13 / 3) + (10 / 3 - 13 / 4) + (8 / 3 - 13 / 5) +
      (9 / 4 - 13 / 6) + (9 / 8 - 13 / 12) = 233 / 120 := by
  norm_num

/-- **Rational enclosure of `γ`** (Appendix E): a 94-cell partition of `[0,1]`,
`∫₀¹ φ = 3517/4095`, `K = 2000` periods summed with directed rounding, and a tail bound. -/
theorem gamma_bounds :
    (159010385641752609841 / 13110552000000000000 : ℝ) ≤ gammaRate ∧
      gammaRate ≤ 158851460347347083647 / 13097448000000000000 :=
  Zeta2GammaBounds.gamma_bounds

/-- **Arithmetic rate (§5)**: `log k_N / N → 25 - γ - 233/120`, by the prime number theorem on
the continuity intervals of `φ` and on the six shells. -/
theorem arith_rate :
    Tendsto (fun N : ℕ => Real.log (kN N) / N) atTop (𝓝 (25 - gammaRate - 233 / 120)) :=
  Zeta2ArithRate.arith_rate

/-- **(A10)**: `k_N > 0` and `limsup log k_N / N ≤ 25 - γ - 233/120 < 10.929906`. -/
theorem kN_rate :
    (∀ N, 0 < kN N) ∧ ∀ ε > 0, ∀ᶠ N : ℕ in atTop, kN N ≤ exp ((10.929906 + ε) * N) := by
  have hlcm : ∀ n, 0 < lcmUpTo n := fun n => Nat.pos_of_ne_zero fun h => by
    obtain ⟨x, hx, h0⟩ := Finset.lcm_eq_zero_iff.1 h
    simp only [Finset.mem_Icc, id_eq] at hx h0
    omega
  have hG : ∀ N, 0 < GN N := fun N =>
    Finset.prod_pos fun p hp => pow_pos (Finset.mem_filter.1 hp).2.1.pos _
  have hH : ∀ N r, 0 < HN N r := fun N r =>
    Finset.prod_pos fun p hp => (Finset.mem_filter.1 hp).2.1.pos
  have hpos : ∀ N, 0 < kN N := fun N =>
    div_pos (by exact_mod_cast Nat.mul_pos (hlcm _) (hlcm _))
      (by exact_mod_cast Nat.mul_pos (hG N) (hH N 0))
  refine ⟨hpos, fun ε hε => ?_⟩
  have hL : 25 - gammaRate - 233 / 120 < 10.929906 + ε := by
    have := gamma_bounds.1
    norm_num at this ⊢
    linarith
  filter_upwards [arith_rate.eventually (gt_mem_nhds hL), eventually_ge_atTop 1] with N h hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_lt_iff₀ hN'] at h
  rw [← Real.exp_log (hpos N)]
  exact Real.exp_le_exp.2 h.le

/-! ## §6. Analytic estimates and nonvanishing -/

/-- **The Barnes integral (§6.1)**: `𝓘_η(P) = J_η(P)` for every polynomial `P`, and
`𝓘_η(1/(s - j)) = H^{(2)}_{j+η} - ζ(2)` (residues `-(k-j)^{-2}` and `π²/3 = 2ζ(2)`). -/
theorem barnes_identities (η : ℕ) :
    (∀ P : ℚ[X], barnesI η (fun s => aeval s P) = (Jfun η P : ℂ)) ∧
      ∀ j : ℕ, barnesI η (fun s => 1 / (s - j)) = (harm2 (j + η) : ℂ) - (zeta2 : ℂ) :=
  Zeta2BarnesIdentities.barnes_identities η

/-- **(A1)**: `C_N 𝖤_{N,r} = -2 𝓘_η(s^r F_N L_m)`, from `readout_formula`, the
partial-fraction identity and `barnes_identities`. -/
theorem error_integral (N : ℕ) (r : Fin 3) (η : ℕ) (hη₁ : 2 * N ≤ η) (hη₂ : η ≤ 9 * N) :
    (((CN N : ℝ) * Err N r : ℝ) : ℂ) =
      -2 * barnesI η (fun s => s ^ (r : ℕ) * aeval s (Fpoly N) * Lker (11 * N) s) :=
  Zeta2ErrorIntegral.error_integral N r η hη₁ hη₂

/-- **Coarse bound (A3)–(A4)**: Gamma-integral rotation on `Re t = 6N` gives
`limsup (1/N) log |C_N 𝖤_{N,r}| ≤ h < -18`. -/
theorem error_coarse_bound (r : Fin 3) :
    ∀ᶠ N : ℕ in atTop, |(CN N : ℝ) * Err N r| ≤ exp (-18 * N) :=
  Zeta2ErrorCoarseBound.error_coarse_bound r

/-- **Spectrum of `A_∞` (A6) and observability (A9)**. The characteristic polynomial
`z³ + c₂z² + c₁z + c₀` has the displayed coefficients and negative discriminant; its real root
is `-Λ` with `17400086428 < Λ < 17400086429`, and `ρ² = c₀/Λ < 1` for the complex pair.
Moreover `det(e₀, A_∞ e₀, A_∞² e₀) ≠ 0`. -/
theorem limit_spectrum :
    let c₀ : ℚ := 1855425871872 / 895833302668638834554683750087890625
    let c₁ : ℚ := 6119917581009155345396562793851904 /
      32000061404626447809127858236889541015625
    let c₂ : ℚ := 266957778538934989798238376160038092809 / 15342324857928574809549553125
    Ainf.charpoly.coeff 0 = c₀ ∧ Ainf.charpoly.coeff 1 = c₁ ∧ Ainf.charpoly.coeff 2 = c₂ ∧
    18 * c₂ * c₁ * c₀ - 4 * c₂ ^ 3 * c₀ + c₂ ^ 2 * c₁ ^ 2 - 4 * c₁ ^ 3 - 27 * c₀ ^ 2 < 0 ∧
    (∃ Λ : ℝ, 17400086428 < Λ ∧ Λ < 17400086429 ∧ aeval (-Λ) Ainf.charpoly = 0 ∧
      (c₀ : ℝ) / Λ < 1) ∧
    (Matrix.of fun i j : Fin 3 => (Ainf ^ (j : ℕ)) i 0).det =
      72143259339220303025804927524593090645506084475442025307751136603648 /
        28469599455181793682074031322586982029718987334183867584429931640625 :=
  Zeta2LimitSpectrum.limit_spectrum

/-- **Sharp rates (A7)–(A8)**. The invariant-cone argument for `x_{N+1} = x_N A_N` gives
`limsup (1/N) log |𝖤_{N,r}| ≤ log ρ` (the error row decays by `error_coarse_bound`) and
`limsup (1/N) log |𝖰_{N,r}| ≤ log Λ`; with `log C_N / N → c_C` and exact log enclosures,
`c_C + log Λ < 38.168733` and `c_C + log ρ < -24.467842`. -/
theorem readout_rates (r : Fin 3) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      |(CN N : ℝ) * Qread N r| ≤ exp ((38.168733 + ε) * N) ∧
        |(CN N : ℝ) * Err N r| ≤ exp ((-24.467842 + ε) * N) :=
  Zeta2ReadoutRates.readout_rates r

/-- **Bounded gap of at most two (§6.5)**. From (A9), `(e₀, A_N e₀, A_N A_{N+1} e₀)` is
invertible for large `N`, so the nonzero row `(bR₀ - aR₁) W_N S_N` cannot annihilate all three
columns: uniformly in `a, b` (with `b > 0`) one of `b 𝖯_{N+i,0} - a 𝖰_{N+i,0}`, `i ≤ 2`, is
nonzero. -/
theorem bounded_gap :
    ∀ᶠ N : ℕ in atTop, ∀ (a : ℤ) (b : ℕ), 0 < b →
      ∃ i : Fin 3, (b : ℚ) * Pread (N + i) 0 - a * Qread (N + i) 0 ≠ 0 :=
  Zeta2BoundedGap.bounded_gap

/-! ## §6.6. The irrationality-measure conclusion -/

/-- **Irrationality criterion (§6.6)**. Integer `P_N, Q_N` with
`limsup log|Q_N|/N ≤ σ`, `limsup log|Q_N α - P_N|/N ≤ -τ` and a uniformly bounded gap of
nonvanishing linear forms give `μ(α) ≤ 1 + σ/τ`. -/
theorem irrMeasure_criterion (α σ τ : ℝ) (hσ : 0 ≤ σ) (hτ : 0 < τ) (P Q : ℕ → ℤ)
    (hQ : ∀ ε > 0, ∀ᶠ N : ℕ in atTop, |(Q N : ℝ)| ≤ exp ((σ + ε) * N))
    (hE : ∀ ε > 0, ∀ᶠ N : ℕ in atTop, |(Q N : ℝ) * α - P N| ≤ exp ((-τ + ε) * N))
    (hgap : ∀ᶠ N : ℕ in atTop, ∀ (a : ℤ) (b : ℕ), 0 < b →
      ∃ i : Fin 3, (b : ℤ) * P (N + i) - a * Q (N + i) ≠ 0) :
    IrrMeasureLE α (1 + σ / τ) :=
  Zeta2IrrCriterion.irrMeasure_criterion α σ τ hσ hτ P Q hQ hE hgap

/-- **`μ(ζ(2)) ≤ 62636575/13537936`**, with `P_N = C_N k_N 𝖯_{N,0}`, `Q_N = C_N k_N 𝖰_{N,0}`,
`σ = 38.168733 + 10.929906 = 49.098639`, `τ = 24.467842 - 10.929906 = 13.537936`. -/
theorem zeta2_irrMeasureLE : IrrMeasureLE zeta2 (62636575 / 13537936) := by
  have hZ : ∀ N : ℕ, ∃ z : Fin 2 → ℤ, 1 ≤ N → ∀ i,
      ((CN N * lcmUpTo (12 * N) * lcmUpTo (13 * N + ((0 : Fin 3) : ℕ)) : ℕ) /
        (GN N * HN N ((0 : Fin 3) : ℕ) : ℕ) : ℚ) * readout N i 0 = z i := by
    intro N
    by_cases hN : 1 ≤ N
    · obtain ⟨z, hz⟩ := arithmetic_normalization N hN 0
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun h => absurd h hN⟩
  choose Z hZ using hZ
  have hrel : ∀ N, 1 ≤ N → ∀ i,
      ((Z N i : ℤ) : ℝ) = kN N * ((CN N : ℝ) * (readout N i 0 : ℝ)) := by
    intro N hN i
    have h := congrArg (fun q : ℚ => (q : ℝ)) (hZ N hN i)
    simp only [Fin.val_zero, add_zero] at h
    push_cast at h
    rw [← h, kN]
    push_cast
    ring
  have hCN : ∀ N, (CN N : ℝ) ≠ 0 := fun N => Nat.cast_ne_zero.2
    (Nat.mul_pos (Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega)))
      (Nat.choose_pos (by omega))).ne'
  have h := irrMeasure_criterion zeta2 49.098639 13.537936 (by norm_num) (by norm_num)
    (fun N => Z N 0) (fun N => Z N 1) ?hQ ?hE ?hgap
  · rwa [show (1 : ℝ) + 49.098639 / 13.537936 = 62636575 / 13537936 by norm_num] at h
  case hQ =>
    intro ε hε
    filter_upwards [kN_rate.2 (ε / 2) (by positivity), readout_rates 0 (ε / 2) (by positivity),
      eventually_ge_atTop 1] with N hk hR hN
    rw [hrel N hN 1, abs_mul, abs_of_pos (kN_rate.1 N)]
    calc kN N * |(CN N : ℝ) * (readout N 1 0 : ℝ)|
        ≤ exp ((10.929906 + ε / 2) * N) * exp ((38.168733 + ε / 2) * N) :=
          mul_le_mul hk hR.1 (abs_nonneg _) (exp_pos _).le
      _ = exp ((49.098639 + ε) * N) := by
          rw [← Real.exp_add]; congr 1; ring
  case hE =>
    intro ε hε
    filter_upwards [kN_rate.2 (ε / 2) (by positivity), readout_rates 0 (ε / 2) (by positivity),
      eventually_ge_atTop 1] with N hk hR hN
    have : ((Z N 1 : ℤ) : ℝ) * zeta2 - (Z N 0 : ℝ) = kN N * ((CN N : ℝ) * Err N 0) := by
      rw [hrel N hN 1, hrel N hN 0, Err]; ring
    rw [this, abs_mul, abs_of_pos (kN_rate.1 N)]
    calc kN N * |(CN N : ℝ) * Err N 0|
        ≤ exp ((10.929906 + ε / 2) * N) * exp ((-24.467842 + ε / 2) * N) :=
          mul_le_mul hk hR.2 (abs_nonneg _) (exp_pos _).le
      _ = exp ((-13.537936 + ε) * N) := by
          rw [← Real.exp_add]; congr 1; ring
  case hgap =>
    filter_upwards [bounded_gap, eventually_ge_atTop 1] with N hg hN a b hb
    obtain ⟨i, hi⟩ := hg a b hb
    refine ⟨i, fun h0 => hi ?_⟩
    have hN' : 1 ≤ N + (i : ℕ) := by omega
    have h' : (((b : ℤ) * Z (N + i) 0 - a * Z (N + i) 1 : ℤ) : ℝ) = 0 := by exact_mod_cast h0
    rw [Int.cast_sub, Int.cast_mul, Int.cast_mul, hrel _ hN' 0, hrel _ hN' 1] at h'
    have h2 : kN (N + i) * (CN (N + i) : ℝ) *
        ((b : ℝ) * (Pread (N + i) 0 : ℝ) - a * (Qread (N + i) 0 : ℝ)) = 0 := by
      push_cast at h'
      linear_combination h'
    have h3 := (mul_eq_zero.1 h2).resolve_left (mul_ne_zero (kN_rate.1 _).ne' (hCN _))
    exact_mod_cast h3

/-- **Main theorem (§6.6)**: `μ(ζ(2)) ≤ 62636575/13537936 < 4.62675`. -/
theorem main_theorem :
    irrationalityMeasure zeta2 ≤ ((62636575 / 13537936 : ℝ) : EReal) ∧
      (62636575 / 13537936 : ℝ) < 4.62675 :=
  ⟨iInf₂_le _ zeta2_irrMeasureLE, by norm_num⟩

end Zeta2Blueprint
