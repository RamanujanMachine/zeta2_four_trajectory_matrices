/-
# Blueprint: `readout_rates` (equations (A5)–(A8), §6.3–§6.4 of the article)

Statement (`Zeta2Blueprint.readout_rates`, restated verbatim below): for every `ε > 0` and all
large `N`, `|C_N 𝖰_{N,r}| ≤ e^{(38.168733+ε)N}` and `|C_N 𝖤_{N,r}| ≤ e^{(-24.467842+ε)N}`.

Proof outline (article §6.3–§6.4).
* The rows `x_N = v W_N S_N`, `S_N = diag(1, N⁻¹, N⁻²)`, satisfy `x_{N+1} = x_N A_N` with
  `A_N = S_N⁻¹ M_N S_{N+1} → A_∞` (`rowSol_succ`; the limit is `Zeta2BoundedGap.A_tendsto`).
* `A_∞` has one real eigenvalue `-Λ`, `17400086428 < Λ < 17400086429`, and a complex pair of
  modulus `ρ = √(c₀/Λ) < 1` (`Zeta2LimitSpectrum.limit_spectrum`). The invariant-cone argument
  gives upper rate `log Λ` for every solution (`cone_rate_all`) and `log ρ` for every solution
  tending to `0` (`cone_rate_decay`).
* The error row `(ζ(2) R₁ - R₀) W_N S_N` tends to `0` by the coarse bound (A3)
  (`error_row_tendsto`, using `error_coarse_bound.lean`).
* Removing `S_N` costs only `N^r` (`rowSol_apply`, `Q_rate`, `E_rate`); Stirling gives
  `log C_N / N → c_C` (`CN_rate`); and the certified enclosures (A8) (`A8_bounds`) finish.

Python certificate: `results/zeta2_complete_proof/code/analytic/certify_analytic_rates.py`
(assertions `ab[1] < 38.168733` and `bb[1] < -24.467842`).
-/
import Zeta2FourTrajectoryMatrices.Analytic.error_coarse_bound
import Zeta2FourTrajectoryMatrices.Analytic.blueprint_bounded_gap
import Zeta2FourTrajectoryMatrices.Analytic.readout_rates_cone3

open Polynomial Filter Topology Real Finset Zeta2Blueprint Zeta2BoundedGap
open scoped Matrix

noncomputable section

namespace Zeta2ReadoutRates

/-- The real eigenvalue `-Λ` of `A_∞` (from `Zeta2LimitSpectrum.real_root`, which gives
`17400086428 < Λ < 17400086429` and `c₀/Λ < 1` via `Classical.choose_spec`). -/
def Lam : ℝ := Classical.choose Zeta2LimitSpectrum.real_root

/-- The common modulus `ρ = √(c₀/Λ)` of the complex pair of eigenvalues of `A_∞` (A6). -/
def rhoS : ℝ := Real.sqrt ((Zeta2LimitSpectrum.c0 : ℝ) / Lam)

/-- `c_C = lim log C_N / N = 10 log 10 + 9 log 9 + 11 log 11 - 2 log 2 - 3 log 3 - 24 log 8`. -/
def cC : ℝ := 10 * log 10 + 9 * log 9 + 11 * log 11 - 2 * log 2 - 3 * log 3 - 24 * log 8

/-- The scaled row solution `x_N = v W_N S_N` (`S_N = sg N = diag(1, N⁻¹, N⁻²)`). -/
def rowSol (v : Fin 3 → ℝ) (N : ℕ) : Fin 3 → ℝ := v ᵥ* (rc (W N) * sg N)

/-- The error row `ζ(2) R₁ - R₀`. -/
def errRow : Fin 3 → ℝ := fun k => zeta2 * (Rmat 1 k : ℝ) - (Rmat 0 k : ℝ)

/-- The `𝖰`-row `R₁`. -/
def qRow : Fin 3 → ℝ := fun k => (Rmat 1 k : ℝ)

/-- **Lemma 1 (the scaled recurrence).** `x_{N+1} = x_N A_N` for `N ≥ 2`, from
`W_{N+1} = W_N M_N` (`Zeta2BoundedGap.W_succ`) and `S_N S_N⁻¹ = 1`.

* Estimated length: 10 lines.
* Formalizable directly from the pdf: yes. -/
theorem rowSol_succ (v : Fin 3 → ℝ) (N : ℕ) (hN : 2 ≤ N) :
    rowSol v (N + 1) = rowSol v N ᵥ* A N := by
  rw [rowSol, rowSol, Matrix.vecMul_vecMul, W_succ N hN, map_mul, A]
  congr 1
  rw [show rc (W N) * sg N * (dg N * rc (MN N) * sg (N + 1)) =
      rc (W N) * (sg N * dg N) * rc (MN N) * sg (N + 1) by simp only [mul_assoc],
    sg_dg N (by omega), mul_one]

/-- **Lemma 2 (cone argument, all solutions).** Every solution of `x_{N+1} = x_N A_N` has upper
exponential rate `log Λ`: in a fixed eigenbasis of `A_∞` the perturbation `A_N - A_∞` is
eventually `≤ ε`, so the adapted operator norm of `A_N` is eventually `≤ Λ + 2ε`.

* Estimated length: 120 lines (complex diagonalisation of `A_∞` from three distinct roots of the
  characteristic polynomial — negative discriminant, `Zeta2LimitSpectrum.disc_neg` — an adapted
  norm, and the product estimate).
* Formalizable directly from the pdf: partially ("the ordinary operator-norm bound gives upper
  rate `log Λ`"; the eigen-decomposition and the adapted norm must be supplied). -/
theorem cone_rate_all (x : ℕ → Fin 3 → ℝ) (hx : ∀ᶠ N in atTop, x (N + 1) = x N ᵥ* A N) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ‖x N‖ ≤ exp ((log Lam + ε) * N) :=
  Zeta2Cone.cone_all_core Lam (Classical.choose_spec Zeta2LimitSpectrum.real_root) x hx

/-- **Lemma 3 (cone argument, decaying solutions).** A solution tending to `0` has upper
exponential rate `log ρ`: with `u_N` the dominant coordinate and `v_N` the complex pair, the cone
`|u_N| ≥ ‖v_N‖` is forward invariant and inside it `|u_N|` grows by `Λ - 2ε > 1`, so a decaying
solution stays outside it, where `‖v_{N+1}‖ ≤ (ρ + 2ε)‖v_N‖`.

* Estimated length: 180 lines (same eigenbasis as Lemma 2; the two cone inequalities;
  a decaying nonzero solution never enters the cone; geometric bound outside the cone).
* Formalizable directly from the pdf: yes, given the eigenbasis of Lemma 2 (§6.3 gives the
  complete elementary argument). -/
theorem cone_rate_decay (x : ℕ → Fin 3 → ℝ) (hx : ∀ᶠ N in atTop, x (N + 1) = x N ᵥ* A N)
    (h0 : Tendsto x atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ‖x N‖ ≤ exp ((log rhoS + ε) * N) :=
  Zeta2Cone.cone_decay_core Lam (Classical.choose_spec Zeta2LimitSpectrum.real_root) x hx h0

theorem rowSol_mul_pow (v : Fin 3 → ℝ) (N : ℕ) (hN : 1 ≤ N) (r : Fin 3) :
    rowSol v N r * (N : ℝ) ^ (r : ℕ) = ∑ k, v k * ((W N k r : ℚ) : ℝ) := by
  have hN0 : ((N : ℝ) ^ (r : ℕ)) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  rw [rowSol, ← Matrix.vecMul_vecMul, sg, Matrix.vecMul_diagonal, inv_mul_cancel_right₀ hN0]
  rfl

/-- **Lemma 4 (reading the readouts from the scaled rows).** For `N ≥ 1`,
`(R₁ W_N S_N)_r N^r = 𝖰_{N,r}` and `((ζ(2)R₁ - R₀) W_N S_N)_r N^r = 𝖤_{N,r}`.

* Estimated length: 20 lines (`Matrix.vecMul`, `Matrix.mul_apply`, `Matrix.diagonal`).
* Formalizable directly from the pdf: yes. -/
theorem rowSol_apply (N : ℕ) (hN : 1 ≤ N) (r : Fin 3) :
    rowSol qRow N r * (N : ℝ) ^ (r : ℕ) = Qread N r ∧
      rowSol errRow N r * (N : ℝ) ^ (r : ℕ) = Err N r := by
  refine ⟨?_, ?_⟩
  · rw [rowSol_mul_pow _ N hN r, Qread, readout, Matrix.mul_apply, Rat.cast_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [Rat.cast_mul]
    rfl
  · rw [rowSol_mul_pow _ N hN r, Err, Qread, Pread, readout, Matrix.mul_apply, Matrix.mul_apply,
      Rat.cast_sum, Rat.cast_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [Rat.cast_mul, Rat.cast_mul, errRow, sub_mul, mul_assoc]

theorem CN_one_le (N : ℕ) : (1 : ℝ) ≤ (CN N : ℝ) :=
  Nat.one_le_cast.2 (Nat.mul_pos (Nat.mul_pos (Nat.choose_pos (by omega))
    (Nat.choose_pos (by omega))) (Nat.choose_pos (by omega)))

/-- **Lemma 5 (the error row tends to zero).** By (A3) (`Zeta2ErrorCoarseBound.error_coarse_bound`)
and `C_N ≥ 1`, `|𝖤_{N,r}| ≤ e^{-18N}`, hence `(errRow W_N S_N)_r = 𝖤_{N,r} N^{-r} → 0`.

* Estimated length: 40 lines (`rowSol_apply`, `C_N ≥ 1` from `Nat.choose_pos`,
  `tendsto_pi_nhds`, `Real.tendsto_exp_neg_atTop_nhds_zero`).
* Formalizable directly from the pdf: yes. -/
theorem error_row_tendsto : Tendsto (rowSol errRow) atTop (𝓝 0) := by
  refine tendsto_pi_nhds.2 fun r => ?_
  have hexp : Tendsto (fun N : ℕ => exp (-18 * N)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (by norm_num : (-18 : ℝ) < 0))
  refine squeeze_zero_norm' ?_ hexp
  filter_upwards [Zeta2ErrorCoarseBound.error_coarse_bound r, eventually_ge_atTop 1] with N hE hN
  have hp : (1 : ℝ) ≤ (N : ℝ) ^ (r : ℕ) := one_le_pow₀ (Nat.one_le_cast.2 hN)
  calc ‖rowSol errRow N r‖ = |rowSol errRow N r| := Real.norm_eq_abs _
    _ ≤ |rowSol errRow N r| * (N : ℝ) ^ (r : ℕ) := le_mul_of_one_le_right (abs_nonneg _) hp
    _ = |Err N r| := by
        rw [← (rowSol_apply N hN r).2, abs_mul, abs_of_nonneg (zero_le_one.trans hp)]
    _ ≤ (CN N : ℝ) * |Err N r| := le_mul_of_one_le_left (abs_nonneg _) (CN_one_le N)
    _ = |(CN N : ℝ) * Err N r| := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (CN N))]
    _ ≤ exp (-18 * N) := hE

theorem pow_le_exp_eventually (k : ℕ) (b : ℝ) (hb : 0 < b) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ k ≤ exp (b * N) := by
  have h := ((isLittleO_pow_exp_pos_mul_atTop k hb).comp_tendsto
    tendsto_natCast_atTop_atTop).bound one_pos
  filter_upwards [h] with N hN
  have h1 : |(N : ℝ) ^ k| ≤ |exp (b * N)| := by
    simpa only [Function.comp_apply, Real.norm_eq_abs, one_mul] using hN
  rwa [abs_of_nonneg (pow_nonneg (Nat.cast_nonneg N) k), abs_of_pos (exp_pos _)] at h1

theorem abs_row_mul_pow_le (x : Fin 3 → ℝ) (N : ℕ) (r : Fin 3) (a ε : ℝ)
    (h1 : ‖x‖ ≤ exp ((a + ε / 2) * N)) (h2 : (N : ℝ) ^ (r : ℕ) ≤ exp (ε / 2 * N)) :
    |x r * (N : ℝ) ^ (r : ℕ)| ≤ exp ((a + ε) * N) := by
  have h3 : |x r| ≤ ‖x‖ := by
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm x r
  rw [abs_mul, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg (α := ℝ) N) (r : ℕ))]
  calc |x r| * (N : ℝ) ^ (r : ℕ) ≤ exp ((a + ε / 2) * N) * exp (ε / 2 * N) :=
        mul_le_mul (h3.trans h1) h2 (pow_nonneg (Nat.cast_nonneg N) _) (exp_pos _).le
    _ = exp ((a + ε) * N) := by rw [← exp_add, ← add_mul, add_assoc, add_halves]

/-- **Lemma 6 (the `𝖰` rate).** `limsup (1/N) log |𝖰_{N,r}| ≤ log Λ`: Lemmas 1, 2 and 4, and
`N^r = e^{o(N)}`.

* Estimated length: 40 lines.
* Formalizable directly from the pdf: yes, given Lemmas 1, 2, 4. -/
theorem Q_rate (r : Fin 3) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, |(Qread N r : ℝ)| ≤ exp ((log Lam + ε) * N) := by
  intro ε hε
  have hx : ∀ᶠ N in atTop, rowSol qRow (N + 1) = rowSol qRow N ᵥ* A N :=
    (eventually_ge_atTop 2).mono fun N hN => rowSol_succ qRow N hN
  filter_upwards [cone_rate_all _ hx (ε / 2) (half_pos hε),
    pow_le_exp_eventually r (ε / 2) (half_pos hε), eventually_ge_atTop 1] with N h1 h2 hN
  rw [← (rowSol_apply N hN r).1]
  exact abs_row_mul_pow_le _ _ _ _ _ h1 h2

/-- **Lemma 7 (the error rate (A7)).** `limsup (1/N) log |𝖤_{N,r}| ≤ log ρ`: Lemmas 1, 3, 4, 5 and
`N^r = e^{o(N)}`.

* Estimated length: 40 lines.
* Formalizable directly from the pdf: yes, given Lemmas 1, 3, 4, 5. -/
theorem E_rate (r : Fin 3) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, |Err N r| ≤ exp ((log rhoS + ε) * N) := by
  intro ε hε
  have hx : ∀ᶠ N in atTop, rowSol errRow (N + 1) = rowSol errRow N ᵥ* A N :=
    (eventually_ge_atTop 2).mono fun N hN => rowSol_succ errRow N hN
  filter_upwards [cone_rate_decay _ hx error_row_tendsto (ε / 2) (half_pos hε),
    pow_le_exp_eventually r (ε / 2) (half_pos hε), eventually_ge_atTop 1] with N h1 h2 hN
  rw [← (rowSol_apply N hN r).2]
  exact abs_row_mul_pow_le _ _ _ _ _ h1 h2

theorem choose_mul_pow_le (n k : ℕ) (h : k ≤ n) :
    n.choose k * (k ^ k * (n - k) ^ (n - k)) ≤ n ^ n := by
  have h1 := add_pow k (n - k) n
  rw [Nat.add_sub_cancel' h] at h1
  rw [h1, mul_comm]
  exact single_le_sum (f := fun m => k ^ m * (n - k) ^ (n - m) * n.choose m)
    (fun i _ => Nat.zero_le _) (mem_range.2 (Nat.lt_succ_of_le h))

theorem choose_le_ratio (a b c N : ℕ) (h : a + b = c) :
    (c * N).choose (a * N) * (a ^ a * b ^ b) ^ N ≤ (c ^ c) ^ N := by
  have hx : ∀ x : ℕ, (x * N) ^ (x * N) = (x ^ x) ^ N * (N ^ N) ^ x := fun x => by
    rw [mul_pow, pow_mul, pow_mul']
  have h1 := choose_mul_pow_le (c * N) (a * N)
    (by rw [← h]; exact Nat.mul_le_mul_right N (Nat.le_add_right a b))
  have h2 : c * N - a * N = b * N := by rw [← h, Nat.add_mul, Nat.add_sub_cancel_left]
  rw [h2, hx a, hx b, hx c, mul_mul_mul_comm ((a ^ a) ^ N) ((N ^ N) ^ a) ((b ^ b) ^ N)
    ((N ^ N) ^ b), ← mul_pow, ← pow_add, h, ← mul_assoc] at h1
  exact Nat.le_of_mul_le_mul_right h1 (pow_pos Nat.pow_self_pos c)

theorem exp_mul_log_nat (a : ℕ) (ha : 0 < a) : exp ((a : ℝ) * log a) = (a : ℝ) ^ a := by
  rw [Real.exp_nat_mul, Real.exp_log (Nat.cast_pos.2 ha)]

theorem choose_exp_le (a b c N : ℕ) (h : a + b = c) (ha : 0 < a) (hb : 0 < b) :
    (((c * N).choose (a * N) : ℕ) : ℝ) ≤
      exp (((c : ℝ) * log c - (a : ℝ) * log a - (b : ℝ) * log b) * N) := by
  have hc : 0 < c := by omega
  have h1 : (((c * N).choose (a * N) : ℕ) : ℝ) * ((a : ℝ) ^ a * (b : ℝ) ^ b) ^ N ≤
      ((c : ℝ) ^ c) ^ N := by
    exact_mod_cast choose_le_ratio a b c N h
  have hpos : 0 < ((a : ℝ) ^ a * (b : ℝ) ^ b) ^ N := by positivity
  rw [mul_comm _ (N : ℝ), Real.exp_nat_mul, sub_sub, exp_sub, exp_add, exp_mul_log_nat c hc,
    exp_mul_log_nat a ha, exp_mul_log_nat b hb, div_pow]
  exact (le_div_iff₀ hpos).2 h1

/-- **Lemma 8 (Stirling for `C_N`).** `log C_N / N → c_C`; in particular
`C_N ≤ e^{(c_C + ε)N}` eventually.

* Estimated length: 80 lines (`C_N = binom(10N,2N) binom(9N,N) binom(11N,3N)`, Stirling
  `Stirling.factorial_isEquivalent_stirling`, or the elementary bounds
  `log n! = n log n - n + O(log n)`).
* Formalizable directly from the pdf: yes ("Stirling's formula gives"). -/
theorem CN_rate : ∀ ε > 0, ∀ᶠ N : ℕ in atTop, (CN N : ℝ) ≤ exp ((cC + ε) * N) := by
  intro ε hε
  refine Eventually.of_forall fun N => ?_
  have h1 := choose_exp_le 2 8 10 N rfl two_pos (by norm_num)
  have h2 := choose_exp_le 1 8 9 N rfl one_pos (by norm_num)
  have h3 := choose_exp_le 3 8 11 N rfl three_pos (by norm_num)
  rw [one_mul] at h2
  calc (CN N : ℝ) = ((10 * N).choose (2 * N) : ℝ) * ((9 * N).choose N : ℝ) *
        ((11 * N).choose (3 * N) : ℝ) := by rw [CN, Nat.cast_mul, Nat.cast_mul]
    _ ≤ exp ((((10 : ℕ) : ℝ) * log ((10 : ℕ) : ℝ) - ((2 : ℕ) : ℝ) * log ((2 : ℕ) : ℝ) -
          ((8 : ℕ) : ℝ) * log ((8 : ℕ) : ℝ)) * N) *
        exp ((((9 : ℕ) : ℝ) * log ((9 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) * log ((1 : ℕ) : ℝ) -
          ((8 : ℕ) : ℝ) * log ((8 : ℕ) : ℝ)) * N) *
        exp ((((11 : ℕ) : ℝ) * log ((11 : ℕ) : ℝ) - ((3 : ℕ) : ℝ) * log ((3 : ℕ) : ℝ) -
          ((8 : ℕ) : ℝ) * log ((8 : ℕ) : ℝ)) * N) :=
        mul_le_mul (mul_le_mul h1 h2 (Nat.cast_nonneg _) (exp_pos _).le) h3 (Nat.cast_nonneg _)
          (mul_nonneg (exp_pos _).le (exp_pos _).le)
    _ = exp (cC * N) := by
        rw [← exp_add, ← exp_add, cC]
        push_cast
        rw [Real.log_one]
        congr 1
        ring
    _ ≤ exp ((cC + ε) * N) :=
        exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hε.le) (Nat.cast_nonneg N))

theorem cC_eq : cC = log ((10 : ℝ) ^ 10 * 9 ^ 9 * 11 ^ 11 / (2 ^ 2 * 3 ^ 3 * 8 ^ 24)) := by
  rw [cC, log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity),
    log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
    log_mul (by positivity) (by positivity), log_pow, log_pow, log_pow, log_pow, log_pow, log_pow]
  push_cast
  ring

theorem exp_lower (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) (hn : 0 < n) :
    ∑ m ∈ range n, x ^ m / m.factorial - x ^ n * (n.succ / (n.factorial * n)) ≤ exp x := by
  have h := Real.exp_bound (x := x) (by rwa [abs_of_nonneg hx0]) hn
  rw [abs_of_nonneg hx0] at h
  linarith [(abs_le.1 h).1]

theorem exp_upper (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) (hn : 0 < n) :
    exp x ≤ ∑ m ∈ range n, x ^ m / m.factorial + x ^ n * (n.succ / (n.factorial * n)) := by
  have h := Real.exp_bound (x := x) (by rwa [abs_of_nonneg hx0]) hn
  rw [abs_of_nonneg hx0] at h
  linarith [(abs_le.1 h).2]

theorem exp_A8_lower :
    (10 : ℝ) ^ 10 * 9 ^ 9 * 11 ^ 11 / (2 ^ 2 * 3 ^ 3 * 8 ^ 24) * 17400086429 < exp 38.168733 := by
  have h1 : (2.7182818283 : ℝ) ^ 38 < exp 1 ^ 38 :=
    pow_lt_pow_left₀ exp_one_gt_d9 (by norm_num) (by norm_num)
  have h2 := exp_lower 0.168733 (by norm_num) (by norm_num) 8 (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h2
  norm_num at h2
  rw [show (168733 / 1000000 : ℝ) = 0.168733 by norm_num] at h2
  have h3 : exp 38.168733 = exp 1 ^ 38 * exp 0.168733 := by
    rw [← exp_nat_mul, ← exp_add]
    norm_num
  rw [h3]
  refine lt_of_lt_of_le ?_ (mul_le_mul h1.le h2 (by norm_num) (by positivity))
  norm_num

theorem exp_A8_upper :
    ((10 : ℝ) ^ 10 * 9 ^ 9 * 11 ^ 11 / (2 ^ 2 * 3 ^ 3 * 8 ^ 24)) ^ 2 *
      (Zeta2LimitSpectrum.c0 : ℝ) * exp 48.935684 < 17400086428 := by
  have h1 : exp 1 ^ 48 < (2.7182818286 : ℝ) ^ 48 :=
    pow_lt_pow_left₀ exp_one_lt_d9 (exp_pos 1).le (by norm_num)
  have h2 := exp_upper 0.935684 (by norm_num) (by norm_num) 14 (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h2
  norm_num at h2
  rw [show (233921 / 250000 : ℝ) = 0.935684 by norm_num] at h2
  have h3 : exp 48.935684 = exp 1 ^ 48 * exp 0.935684 := by
    rw [← exp_nat_mul, ← exp_add]
    norm_num
  rw [h3, Zeta2LimitSpectrum.c0]
  refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left
    (mul_le_mul h1.le h2 (exp_pos _).le (by norm_num)) (by positivity)) ?_
  norm_num

/-- **Lemma 9 (certified numerical rates (A8)).** `c_C + log Λ < 38.168733` and
`c_C + log ρ < -24.467842`, with `log ρ = (log c₀ - log Λ)/2`.

* Estimated length: 80 lines (rational enclosures of `log 2, log 3, log 5, log 11` and of `log Λ`
  on `17400086428 < Λ < 17400086429`, `log c₀` for the explicit rational `c₀`; `norm_num`).
* Formalizable directly from the pdf: no — the pdf states only the two inequalities and the
  method (§6.4: series `log x = 2 ∑ z^{2k+1}/(2k+1)` with explicit tail, `K = 32`); the numbers are
  certified by `code/analytic/certify_analytic_rates.py`, which a Lean proof would replay. -/
theorem A8_bounds : cC + log Lam < 38.168733 ∧ cC + log rhoS < -24.467842 := by
  obtain ⟨hL, hU, -, -⟩ := Classical.choose_spec Zeta2LimitSpectrum.real_root
  have hL' : 17400086428 < Lam := hL
  have hU' : Lam < 17400086429 := hU
  have hLpos : 0 < Lam := lt_trans (by norm_num) hL'
  have hc0 : (0 : ℝ) < Zeta2LimitSpectrum.c0 := by
    rw [Zeta2LimitSpectrum.c0]
    norm_num
  have hR : (0 : ℝ) < 10 ^ 10 * 9 ^ 9 * 11 ^ 11 / (2 ^ 2 * 3 ^ 3 * 8 ^ 24) := by positivity
  rw [cC_eq]
  constructor
  · rw [← log_mul hR.ne' hLpos.ne', log_lt_iff_lt_exp (mul_pos hR hLpos)]
    exact lt_trans (mul_lt_mul_of_pos_left hU' hR) exp_A8_lower
  · have h1 : ((10 : ℝ) ^ 10 * 9 ^ 9 * 11 ^ 11 / (2 ^ 2 * 3 ^ 3 * 8 ^ 24)) ^ 2 *
        (Zeta2LimitSpectrum.c0 : ℝ) < Lam * exp (-48.935684) := by
      rw [exp_neg, ← div_eq_mul_inv, lt_div_iff₀ (exp_pos _)]
      exact lt_trans exp_A8_upper hL'
    have h2 := log_lt_log (mul_pos (pow_pos hR 2) hc0) h1
    rw [log_mul (pow_pos hR 2).ne' hc0.ne', log_pow, log_mul hLpos.ne' (exp_pos _).ne',
      log_exp] at h2
    rw [rhoS, log_sqrt (div_nonneg hc0.le hLpos.le), log_div hc0.ne' hLpos.ne']
    push_cast at h2
    linarith

/-- **Sharp rates (A7)–(A8)** — restatement of `Zeta2Blueprint.readout_rates`, proved from
Lemmas 6–9 (Lemmas 1–5 are the ingredients of Lemmas 6–7). -/
theorem readout_rates (r : Fin 3) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      |(CN N : ℝ) * Qread N r| ≤ exp ((38.168733 + ε) * N) ∧
        |(CN N : ℝ) * Err N r| ≤ exp ((-24.467842 + ε) * N) := by
  intro ε hε
  obtain ⟨hA, hB⟩ := A8_bounds
  filter_upwards [Q_rate r (ε / 2) (by positivity), E_rate r (ε / 2) (by positivity),
    CN_rate (ε / 2) (by positivity)] with N hQ hE hC
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (CN N))]
  constructor
  · calc (CN N : ℝ) * |(Qread N r : ℝ)|
        ≤ exp ((cC + ε / 2) * N) * exp ((log Lam + ε / 2) * N) :=
          mul_le_mul hC hQ (abs_nonneg _) (exp_pos _).le
      _ = exp ((cC + log Lam + ε) * N) := by rw [← exp_add]; ring_nf
      _ ≤ exp ((38.168733 + ε) * N) :=
          exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith) hN)
  · calc (CN N : ℝ) * |Err N r|
        ≤ exp ((cC + ε / 2) * N) * exp ((log rhoS + ε / 2) * N) :=
          mul_le_mul hC hE (abs_nonneg _) (exp_pos _).le
      _ = exp ((cC + log rhoS + ε) * N) := by rw [← exp_add]; ring_nf
      _ ≤ exp ((-24.467842 + ε) * N) :=
          exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith) hN)

end Zeta2ReadoutRates
