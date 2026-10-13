/-
# Blueprint: `arith_rate` (§5 of the article)

Statement (`Zeta2Blueprint.arith_rate`, restated verbatim below):
`log k_N / N → 25 - γ - 233/120`, where `k_N = d_{12N} d_{13N} / (G_N H_{N,0})` and
`γ = ∫_{1/13}^∞ φ(x)/x² dx`.

Proof outline (article §5).
* `log k_N = log d_{12N} + log d_{13N} - ∑_{p ∈ S_N} φ(N/p) log p - ∑_{p ∈ shells} log p`
  (`log_kN_eq`).
* Prime number theorem: `log d_n / n → 1` (`log_lcm_tendsto`), so the first two terms give
  `12 + 13 = 25`; and `ϑ(bN) - ϑ(aN) ~ (b - a) N` (`theta_window`).
* The six shells are disjoint intervals of total length `233N/120` (`Zeta2Blueprint.shell_lengths`),
  so their primes contribute `233/120` (`shell_sum_tendsto`).
* `φ` is one-periodic, bounded by `3`, vanishes on `(0, 1/13)` and is constant on the `94` cells
  of `[0, 1)` (`Zeta2GammaInt.phi_eq_G`, already proved). Primes `p > N/K` lie in finitely many
  cell windows, which gives `∫_{1/13}^{K} φ/x²` (`GN_sum_truncated`); primes `p ≤ N/K` contribute
  at most `3 log 4 · N/K` by Chebyshev (`theta_le`, `GN_sum_tail`), and the integral tail is
  `≤ 3/K` (`gamma_tail`). Letting `K → ∞` gives `(1/N) log G_N → γ` (`GN_sum_tendsto`).

Python certificate: `results/zeta2_complete_proof/code/rate_certificate.py` (the 94-cell carry
profile; its content is already formalised in the `blueprint_gamma_*` files).
-/
import Zeta2FourTrajectoryMatrices.FiniteReadout.blueprint_next_two
import Zeta2FourTrajectoryMatrices.ArithmeticRate.blueprint_gamma_int
import Zeta2FourTrajectoryMatrices.ArithmeticRate.arith_rate_cells

open Filter Topology Real Finset MeasureTheory Zeta2Blueprint Zeta2NextTwo

noncomputable section

namespace Zeta2ArithRate

/-- `∑_{p ∈ S_N} φ(N/p) log p = log G_N`, `S_N = {√(50N) < p ≤ 13N prime}`. -/
def GNsum (N : ℕ) : ℝ := ∑ p ∈ Sset N, ((phi ((N : ℝ) / p)).toNat : ℝ) * log p

/-- The primes of `H_{N,0}` (the six shells for column `r = 0`, above `√(50N)`). -/
def shellSet (N : ℕ) : Finset ℕ :=
  (range (8 * N)).filter (fun p => p.Prime ∧ 50 * N < p ^ 2 ∧ InShell N 0 p)

/-- `ϑ`-sum over the primes in the window `(aN, bN]`. -/
def thetaWin (a b : ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ (range (⌊b * N⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ a * N < p), log p

/-- **Lemma 1 (logarithm of `k_N`).** For `N ≥ 1`,
`log k_N = log d_{12N} + log d_{13N} - log G_N - log H_{N,0}` with `log G_N = GNsum N` and
`log H_{N,0} = ∑_{p ∈ shells} log p`.

* Estimated length: 25 lines (`Real.log_div`, `Real.log_mul`, `Real.log_prod`, `Real.log_pow`;
  positivity from `Zeta2NextTwo.lcmUpTo_pos` and primality).
* Formalizable directly from the pdf: yes. -/
theorem log_kN_eq (N : ℕ) (hN : 1 ≤ N) :
    log (kN N) = log (lcmUpTo (12 * N)) + log (lcmUpTo (13 * N)) - GNsum N -
      ∑ p ∈ shellSet N, log p := by
  have _h := hN
  have hG : (GN N : ℝ) = ∏ p ∈ Sset N, ((p : ℝ) ^ (phi ((N : ℝ) / p)).toNat) := by
    rw [show GN N = ∏ p ∈ Sset N, p ^ (phi ((N : ℝ) / p)).toNat from rfl, Nat.cast_prod]
    exact Finset.prod_congr rfl fun p _ => Nat.cast_pow p _
  have hH : (HN N 0 : ℝ) = ∏ p ∈ shellSet N, (p : ℝ) := by
    rw [show HN N 0 = ∏ p ∈ shellSet N, p from rfl, Nat.cast_prod]
  have hG0 : (GN N : ℝ) ≠ 0 := by
    rw [hG]
    exact prod_ne_zero_iff.2 fun p hp =>
      pow_ne_zero _ (Nat.cast_ne_zero.2 (mem_Sset hp).1.ne_zero)
  have hH0 : (HN N 0 : ℝ) ≠ 0 := by
    rw [hH]
    exact prod_ne_zero_iff.2 fun p hp => Nat.cast_ne_zero.2 (mem_filter.1 hp).2.1.ne_zero
  have hl1 : (lcmUpTo (12 * N) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (lcmUpTo_pos _).ne'
  have hl2 : (lcmUpTo (13 * N) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (lcmUpTo_pos _).ne'
  have hGs : log (GN N : ℝ) = GNsum N := by
    rw [hG, Real.log_prod (fun p hp => pow_ne_zero _ (Nat.cast_ne_zero.2 (mem_Sset hp).1.ne_zero))]
    exact Finset.sum_congr rfl fun p _ => Real.log_pow _ _
  have hHs : log (HN N 0 : ℝ) = ∑ p ∈ shellSet N, log p := by
    rw [hH, Real.log_prod (fun p hp => Nat.cast_ne_zero.2 (mem_filter.1 hp).2.1.ne_zero)]
  rw [kN, Nat.cast_mul, Nat.cast_mul, Real.log_div (mul_ne_zero hl1 hl2) (mul_ne_zero hG0 hH0),
    Real.log_mul hl1 hl2, Real.log_mul hG0 hH0, hGs, hHs, sub_add_eq_sub_sub]

axiom prime_number_theorem :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1)

/-- **Lemma 2 (`log d_n ~ n`).** `log d_n = ψ(n)` (the exponent of `p` in `d_n` is `⌊log_p n⌋`)
and the prime number theorem `ψ(n) ~ n`.

* Estimated length: 60 lines given the prime number theorem (`Nat.factorization` of
  `Finset.lcm`), and the PNT itself.
* Formalizable directly from the pdf: no — the pdf invokes the prime number theorem, which is not
  in Mathlib (it is available in the PrimeNumberTheoremAnd project). -/
theorem log_lcm_tendsto : Tendsto (fun n : ℕ => log (lcmUpTo n) / n) atTop (𝓝 1) := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hθ : Tendsto (fun n : ℕ => Chebyshev.theta n / n) atTop (𝓝 1) :=
    prime_number_theorem.comp tendsto_natCast_atTop_atTop
  have hs : Tendsto (fun n : ℕ => C * (√(n : ℝ))⁻¹) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)).const_mul C
    rwa [mul_zero] at h
  have hd : Tendsto (fun n : ℕ => (Chebyshev.psi n - Chebyshev.theta n) / n) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hs ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact div_nonneg (sub_nonneg.2 (Chebyshev.theta_le_psi _)) (Nat.cast_nonneg n)
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
      rw [div_le_iff₀ hn', mul_assoc, inv_mul_eq_div, Real.div_sqrt]
      exact hC n
  have h := hθ.add hd
  rw [add_zero] at h
  refine h.congr fun n => ?_
  rw [← add_div, add_sub_cancel, Chebyshev.psi_eq_log_lcmUpto]
  rfl

/-- **Lemma 3 (primes in a linear window).** For `0 ≤ a ≤ b`,
`(ϑ(bN) - ϑ(aN)) / N → b - a`, by the prime number theorem `ϑ(x) ~ x`.

* Estimated length: 40 lines given the prime number theorem.
* Formalizable directly from the pdf: no (prime number theorem, as in Lemma 2). -/
theorem theta_mul_tendsto (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun N : ℕ => Chebyshev.theta (c * N) / N) atTop (𝓝 c) := by
  rcases hc.eq_or_lt with h0 | hpos
  · subst h0
    refine tendsto_const_nhds.congr fun N => ?_
    rw [zero_mul, Chebyshev.theta_zero, zero_div]
  · have h := (prime_number_theorem.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hpos)).mul_const c
    rw [one_mul] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [Function.comp_apply, div_mul_eq_mul_div, mul_comm (Chebyshev.theta (c * N)) c,
      mul_div_mul_left _ _ hpos.ne']

theorem thetaWin_eq (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (N : ℕ) :
    thetaWin a b N = Chebyshev.theta (b * N) - Chebyshev.theta (a * N) := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hA : ⌊a * N⌋₊ ≤ ⌊b * N⌋₊ := Nat.floor_le_floor (mul_le_mul_of_nonneg_right hab hN)
  have hs : (Nat.primesLE ⌊b * N⌋₊).filter (fun p : ℕ => ¬ a * N < p) = Nat.primesLE ⌊a * N⌋₊ := by
    ext p
    rw [mem_filter, Nat.mem_primesLE, Nat.mem_primesLE, not_lt,
      ← Nat.le_floor_iff (mul_nonneg ha hN)]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.trans hA, h.2⟩, h.1⟩⟩
  rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE, ← hs,
    ← sum_filter_add_sum_filter_not (Nat.primesLE ⌊b * N⌋₊) (fun p : ℕ => a * N < p),
    add_sub_cancel_right, thetaWin, ← filter_filter]
  rfl

theorem theta_window (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    Tendsto (fun N : ℕ => thetaWin a b N / N) atTop (𝓝 (b - a)) := by
  refine ((theta_mul_tendsto b (ha.trans hab)).sub (theta_mul_tendsto a ha)).congr fun N => ?_
  rw [thetaWin_eq a b ha hab, sub_div]

/-- **Lemma 4 (Chebyshev's bound).** `ϑ(n) ≤ n log 4`.

* Estimated length: 15 lines (`primorial_le_4_pow`, `Real.log_prod`).
* Formalizable directly from the pdf: yes (used for the omitted part `‖φ‖_∞ ϑ(N/K)/N`). -/
theorem theta_le (n : ℕ) :
    ∑ p ∈ (range (n + 1)).filter Nat.Prime, log p ≤ n * log 4 := by
  rw [← Real.log_prod (fun p hp => Nat.cast_ne_zero.2 (mem_filter.1 hp).2.ne_zero),
    ← Nat.cast_prod, ← Real.log_pow]
  have h : primorial n ≤ 4 ^ n := primorial_le_four_pow n
  exact Real.log_le_log (Nat.cast_pos.2 (prod_pos fun p hp => (mem_filter.1 hp).2.pos))
    (by exact_mod_cast h)

theorem log_div_tendsto : Tendsto (fun N : ℕ => (log 8 + log N) / N) atTop (𝓝 0) := by
  have h := (tendsto_const_div_atTop_nhds_zero_nat (log 8)).add
    ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop)
  rw [add_zero] at h
  refine h.congr fun N => ?_
  simp only [Function.comp_apply, pow_one, one_mul, add_zero, add_div]

theorem win_lt_iff (a K N p : ℕ) (hK : 0 < K) :
    (a : ℝ) / K * N < p ↔ a * N < K * p := by
  rw [div_mul_eq_mul_div, div_lt_iff₀ (Nat.cast_pos.2 hK), ← Nat.cast_mul, ← Nat.cast_mul,
    Nat.cast_lt, Nat.mul_comm p K]

theorem win_le_iff (n m N p : ℕ) (hm : 0 < m) :
    (p : ℝ) ≤ (n : ℝ) / m * N ↔ m * p ≤ n * N := by
  rw [div_mul_eq_mul_div, le_div_iff₀ (Nat.cast_pos.2 hm), ← Nat.cast_mul, ← Nat.cast_mul,
    Nat.cast_le, Nat.mul_comm p m]

theorem le_eight (m n N p : ℕ) (hm : 0 < m) (hn : n ≤ 8 * m) (h : m * p ≤ n * N) :
    p ≤ 8 * N :=
  Nat.le_of_mul_le_mul_left (h.trans (by
    rw [← Nat.mul_assoc, Nat.mul_comm m 8]
    exact Nat.mul_le_mul_right N hn)) hm

theorem closed_window_eq (K m n N : ℕ) (hK : 0 < K) (hm : 0 < m) (hn : n ≤ 8 * m) :
    thetaWin (13 / K) ((n : ℝ) / m) N =
      ∑ p ∈ (range (8 * N + 1)).filter
        (fun p => p.Prime ∧ 13 * N < K * p ∧ m * p ≤ n * N), log p := by
  refine Finset.sum_congr (Finset.ext fun p => ?_) fun _ _ => rfl
  have h1 := win_lt_iff 13 K N p hK
  rw [Nat.cast_ofNat] at h1
  have h0 : (0 : ℝ) ≤ (n : ℝ) / m * N :=
    mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  rw [mem_filter, mem_filter, mem_range, mem_range, Nat.lt_add_one_iff, Nat.lt_add_one_iff,
    Nat.le_floor_iff h0, h1, win_le_iff n m N p hm]
  constructor
  · rintro ⟨hp, hpr, h13⟩
    exact ⟨le_eight m n N p hm hn hp, hpr, h13, hp⟩
  · rintro ⟨-, hpr, h13, hp⟩
    exact ⟨hp, hpr, h13⟩

theorem window_split (K m n N : ℕ) (hm : 0 < m) (hN : 1 ≤ N) :
    ∃ D : ℝ, 0 ≤ D ∧ D ≤ log 8 + log N ∧
      ∑ p ∈ (range (8 * N + 1)).filter
        (fun p => p.Prime ∧ 13 * N < K * p ∧ m * p ≤ n * N), log p =
      D + ∑ p ∈ (range (8 * N + 1)).filter
        (fun p => p.Prime ∧ 13 * N < K * p ∧ m * p < n * N), log p := by
  have hsub : (range (8 * N + 1)).filter (fun p => p.Prime ∧ 13 * N < K * p ∧ m * p < n * N) ⊆
      (range (8 * N + 1)).filter (fun p => p.Prime ∧ 13 * N < K * p ∧ m * p ≤ n * N) :=
    fun p hp => by
      rw [mem_filter] at hp ⊢
      exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.le⟩
  have hc : 0 ≤ log 8 + log N :=
    add_nonneg (Real.log_natCast_nonneg 8) (Real.log_natCast_nonneg N)
  have heq : ∀ p ∈ (range (8 * N + 1)).filter
      (fun p => p.Prime ∧ 13 * N < K * p ∧ m * p ≤ n * N) \
      (range (8 * N + 1)).filter (fun p => p.Prime ∧ 13 * N < K * p ∧ m * p < n * N),
      m * p = n * N := fun p hp => by
    obtain ⟨h1, h2⟩ := mem_sdiff.1 hp
    rw [mem_filter] at h1 h2
    exact le_antisymm h1.2.2.2 (not_lt.1 fun h => h2 ⟨h1.1, h1.2.1, h1.2.2.1, h⟩)
  refine ⟨_, sum_nonneg fun p _ => Real.log_natCast_nonneg p, ?_, (sum_sdiff hsub).symm⟩
  refine (sum_le_card_nsmul _ _ (log 8 + log N) fun p hp => ?_).trans ?_
  · have hp' := (mem_filter.1 (mem_sdiff.1 hp).1)
    rw [← Real.log_mul (by norm_num) (Nat.cast_ne_zero.2 (by omega))]
    refine Real.log_le_log (Nat.cast_pos.2 hp'.2.1.pos) ?_
    rw [← Nat.cast_ofNat, ← Nat.cast_mul, Nat.cast_le]
    exact Nat.lt_add_one_iff.1 (mem_range.1 hp'.1)
  · rw [nsmul_eq_mul]
    refine mul_le_of_le_one_left hc (Nat.cast_le_one.2 (card_le_one.2 fun a ha b hb => ?_))
    exact Nat.eq_of_mul_eq_mul_left hm ((heq a ha).trans (heq b hb).symm)

theorem open_window_tendsto (K m n : ℕ) (hK : 0 < K) (hm : 0 < m) (hn : n ≤ 8 * m)
    (hab : 13 * m ≤ n * K) :
    Tendsto (fun N : ℕ => (∑ p ∈ (range (8 * N + 1)).filter
      (fun p => p.Prime ∧ 13 * N < K * p ∧ m * p < n * N), log p) / N) atTop
      (𝓝 ((n : ℝ) / m - 13 / K)) := by
  have hab' : (13 : ℝ) / K ≤ (n : ℝ) / m := by
    rw [div_le_div_iff₀ (Nat.cast_pos.2 hK) (Nat.cast_pos.2 hm)]
    exact_mod_cast hab
  have hT := theta_window (13 / K) ((n : ℝ) / m) (div_nonneg (by norm_num) (Nat.cast_nonneg K))
    hab'
  have hD : Tendsto (fun N : ℕ => (thetaWin (13 / K) ((n : ℝ) / m) N -
      ∑ p ∈ (range (8 * N + 1)).filter
        (fun p => p.Prime ∧ 13 * N < K * p ∧ m * p < n * N), log p) / N) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds log_div_tendsto ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with N hN
      obtain ⟨D, h0, -, h2⟩ := window_split K m n N hm hN
      rw [closed_window_eq K m n N hK hm hn, h2, add_sub_cancel_right]
      exact div_nonneg h0 (Nat.cast_nonneg N)
    · filter_upwards [eventually_ge_atTop 1] with N hN
      obtain ⟨D, -, h1, h2⟩ := window_split K m n N hm hN
      rw [closed_window_eq K m n N hK hm hn, h2, add_sub_cancel_right]
      exact div_le_div_of_nonneg_right h1 (Nat.cast_nonneg N)
  have h := hT.sub hD
  rw [sub_zero] at h
  refine h.congr fun N => ?_
  rw [← sub_div, sub_sub_cancel]

theorem sq_gt (N p : ℕ) (hN : 43 ≤ N) (h : 13 * N < 12 * p) : 50 * N < p ^ 2 := by
  have h1 : 13 * 13 * (N * N) < 12 * 12 * (p * p) := by
    rw [Nat.mul_mul_mul_comm, Nat.mul_mul_mul_comm 12]
    exact Nat.mul_lt_mul'' h h
  have h2 := Nat.mul_le_mul_right N hN
  rw [sq]
  omega

theorem sum_prime_or (s : Finset ℕ) (A B : ℕ → Prop) [DecidablePred A] [DecidablePred B]
    (h : ∀ p, A p → ¬ B p) :
    ∑ p ∈ s.filter (fun p => p.Prime ∧ (A p ∨ B p)), log p =
      ∑ p ∈ s.filter (fun p => p.Prime ∧ A p), log p +
        ∑ p ∈ s.filter (fun p => p.Prime ∧ B p), log p := by
  rw [filter_congr (fun p _ => and_or_left), filter_or,
    sum_union (disjoint_filter.2 fun p _ ha hb => h p ha.2 hb.2)]

theorem shellSet_eq (N : ℕ) (hN : 43 ≤ N) : shellSet N = (range (8 * N + 1)).filter (fun p =>
    p.Prime ∧ ((13 * N < 2 * p ∧ 1 * p < 8 * N) ∨ ((13 * N < 3 * p ∧ 2 * p < 9 * N) ∨
      ((13 * N < 4 * p ∧ 3 * p < 10 * N) ∨ ((13 * N < 5 * p ∧ 3 * p < 8 * N) ∨
        ((13 * N < 6 * p ∧ 4 * p < 9 * N) ∨ (13 * N < 12 * p ∧ 8 * p < 9 * N))))))) := by
  ext p
  rw [shellSet, mem_filter, mem_filter, mem_range, mem_range]
  constructor
  · rintro ⟨hp8, hpr, -, hs⟩
    exact ⟨by omega, hpr, by omega⟩
  · rintro ⟨-, hpr, hs⟩
    exact ⟨by omega, hpr, sq_gt N p hN (by omega), by omega⟩

/-- **Lemma 5 (the six shells).** `(1/N) ∑_{p ∈ shells} log p → 233/120`: the six open intervals
`((13N)/K, u_K N)` are disjoint, each contributes its length by Lemma 3 (open endpoints change at
most one prime, `O(log N)`), the cutoff `p² > 50N` removes nothing for large `N`, and the lengths
add up to `233/120` (`Zeta2Blueprint.shell_lengths`).

* Estimated length: 80 lines.
* Formalizable directly from the pdf: yes, given Lemma 3. -/
theorem shell_sum_tendsto :
    Tendsto (fun N : ℕ => (∑ p ∈ shellSet N, log p) / N) atTop (𝓝 (233 / 120)) := by
  have h := (open_window_tendsto 2 1 8 (by omega) (by omega) (by omega) (by omega)).add
    ((open_window_tendsto 3 2 9 (by omega) (by omega) (by omega) (by omega)).add
    ((open_window_tendsto 4 3 10 (by omega) (by omega) (by omega) (by omega)).add
    ((open_window_tendsto 5 3 8 (by omega) (by omega) (by omega) (by omega)).add
    ((open_window_tendsto 6 4 9 (by omega) (by omega) (by omega) (by omega)).add
    (open_window_tendsto 12 8 9 (by omega) (by omega) (by omega) (by omega))))))
  have hv : ((8 : ℕ) : ℝ) / (1 : ℕ) - 13 / (2 : ℕ) + (((9 : ℕ) : ℝ) / (2 : ℕ) - 13 / (3 : ℕ) +
      (((10 : ℕ) : ℝ) / (3 : ℕ) - 13 / (4 : ℕ) + (((8 : ℕ) : ℝ) / (3 : ℕ) - 13 / (5 : ℕ) +
      (((9 : ℕ) : ℝ) / (4 : ℕ) - 13 / (6 : ℕ) + (((9 : ℕ) : ℝ) / (8 : ℕ) - 13 / (12 : ℕ)))))) =
      233 / 120 := by
    norm_num
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 43] with N hN
  rw [shellSet_eq N hN, sum_prime_or _ _ _ (fun p _ _ => by omega),
    sum_prime_or _ _ _ (fun p _ _ => by omega), sum_prime_or _ _ _ (fun p _ _ => by omega),
    sum_prime_or _ _ _ (fun p _ _ => by omega), sum_prime_or _ _ _ (fun p _ _ => by omega)]
  simp only [add_div]

/-- **Lemma 6 (the cell windows).** For every `K ≥ 1`, the primes `N/K < p ≤ 13N` contribute
`(1/N) ∑ φ(N/p) log p → ∫_{1/13}^{K} φ(x)/x² dx`: the range `x = N/p ∈ [1/13, K)` is covered by the
`94 K` cells `(k + a_i, k + b_i)`, on which `φ = h_i` (`Zeta2GammaInt.phi_eq_G`); the primes with
`x` in a cell form the window `(N/(k+b_i), N/(k+a_i))`, contributing
`h_i (1/(k+a_i) - 1/(k+b_i))` by Lemma 3 (= the cell integral, `Zeta2GammaInt.J_eq`); cut points
carry at most one prime each and the cutoff `p ≤ √(50N)` contributes `O(√N log N)`.

* Estimated length: 150 lines.
* Formalizable directly from the pdf: yes, given Lemma 3 and the proved cell table
  (`Zeta2GammaTable`, `Zeta2GammaInt`). -/
theorem GN_sum_truncated (K : ℕ) (hK : 1 ≤ K) :
    Tendsto (fun N : ℕ => (∑ p ∈ (Sset N).filter (fun p => N < K * p),
        ((phi ((N : ℝ) / p)).toNat : ℝ) * log p) / N) atTop
      (𝓝 (∫ x in Set.Ioo (1 / 13 : ℝ) K, (phi x : ℝ) / x ^ 2)) :=
  Zeta2ArithRateCells.GN_sum_truncated_core (fun a b ha hab => theta_window a b ha hab) K hK

theorem toNat_phi_le_three (N p : ℕ) (hp : 0 < p) : (phi ((N : ℝ) / p)).toNat ≤ 3 := by
  have h := hp_le_chi N p hp 0
  have h0 := chi_nat N p 0 hp (Nat.zero_le _)
  rw [Nat.cast_zero] at h0
  rw [h0] at h
  have e1 := Nat.add_div_le_div_add_div_add_one (8 * N) (2 * N) p
  have e2 := Nat.add_div_le_div_add_div_add_one (8 * N) N p
  have e3 := Nat.add_div_le_div_add_div_add_one (8 * N) (3 * N) p
  rw [show 8 * N + 2 * N = 0 + 10 * N by omega] at e1
  rw [show 8 * N + N = 0 + 9 * N by omega] at e2
  rw [show 8 * N + 3 * N = 0 + 11 * N by omega] at e3
  rw [Nat.sub_zero, Nat.add_zero, Nat.add_zero, Nat.add_zero, Nat.zero_div] at h
  omega

/-- **Lemma 7 (the omitted small primes).** Since `0 ≤ φ ≤ 3` (three binomial carries),
the primes `p ≤ N/K` contribute at most `3 ϑ(N/K) ≤ 3 log 4 · N/K` (Lemma 4).

* Estimated length: 30 lines (`φ(x) ≤ ρ(x, 0) ≤ 3`).
* Formalizable directly from the pdf: yes ("bound the omitted part by `‖φ‖_∞ ϑ(N/K)/N`"). -/
theorem GN_sum_tail (K N : ℕ) :
    K * ∑ p ∈ (Sset N).filter (fun p => K * p ≤ N), ((phi ((N : ℝ) / p)).toNat : ℝ) * log p ≤
      3 * log 4 * N := by
  have h4 : 0 ≤ 3 * log 4 := mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · rw [Nat.cast_zero, zero_mul]
    exact mul_nonneg h4 (Nat.cast_nonneg N)
  have h1 : ∑ p ∈ (Sset N).filter (fun p => K * p ≤ N), ((phi ((N : ℝ) / p)).toNat : ℝ) * log p ≤
      ∑ p ∈ (Sset N).filter (fun p => K * p ≤ N), 3 * log p :=
    sum_le_sum fun p hp => mul_le_mul_of_nonneg_right
      (by exact_mod_cast toNat_phi_le_three N p (mem_Sset (mem_filter.1 hp).1).2.2.1)
      (Real.log_natCast_nonneg p)
  have h2 : ∑ p ∈ (Sset N).filter (fun p => K * p ≤ N), log p ≤
      ∑ p ∈ (range (N / K + 1)).filter Nat.Prime, log p :=
    sum_le_sum_of_subset_of_nonneg (fun p hp => mem_filter.2 ⟨mem_range.2 (Nat.lt_add_one_iff.2
      ((Nat.le_div_iff_mul_le hK).2 (by rw [Nat.mul_comm]; exact (mem_filter.1 hp).2))),
      (mem_Sset (mem_filter.1 hp).1).1⟩) (fun p _ _ => Real.log_natCast_nonneg p)
  have h5 : (K : ℝ) * ((N / K : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.mul_div_le N K
  rw [← mul_sum] at h1
  calc (K : ℝ) * ∑ p ∈ (Sset N).filter (fun p => K * p ≤ N),
        ((phi ((N : ℝ) / p)).toNat : ℝ) * log p
      ≤ K * (3 * ((N / K : ℕ) * log 4)) := mul_le_mul_of_nonneg_left (h1.trans
        (mul_le_mul_of_nonneg_left (h2.trans (theta_le (N / K))) (by norm_num)))
        (Nat.cast_nonneg K)
    _ = 3 * log 4 * (K * (N / K : ℕ)) := by ring
    _ ≤ 3 * log 4 * N := mul_le_mul_of_nonneg_left h5 h4

theorem integral_inv_sq_Ioi (c : ℝ) (hc : 0 < c) : ∫ x in Set.Ioi c, (x ^ 2)⁻¹ = c⁻¹ := by
  have h := integral_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) hc
  rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one, neg_div_neg_eq, div_one] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [Real.rpow_neg (le_of_lt (hc.trans hx)), Real.rpow_two]

/-- **Lemma 8 (the tail of `γ`).** `0 ≤ γ - ∫_{1/13}^{K} φ/x² = ∫_K^∞ φ/x² ≤ 3/K`.

* Estimated length: 25 lines (`Zeta2GammaInt.integral_f_eq_g`, `Zeta2GammaInt.G_bounds`,
  `integral_Ioi_rpow`-type evaluation of `∫_K^∞ x⁻²`).
* Formalizable directly from the pdf: yes. -/
theorem gamma_tail (K : ℕ) (hK : 1 ≤ K) :
    |gammaRate - ∫ x in Set.Ioo (1 / 13 : ℝ) K, (phi x : ℝ) / x ^ 2| ≤ 3 / K := by
  have hK0 : (0 : ℝ) < K := Nat.cast_pos.2 hK
  have h13 : (1 / 13 : ℝ) < K := lt_of_lt_of_le (by norm_num) (Nat.one_le_cast.2 hK)
  have hsub : Set.Ioi (1 / 13 : ℝ) ⊆ Set.Ici 0 := fun x hx =>
    le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 1 / 13) hx)
  have e1 : gammaRate = ∫ x in Set.Ioi (1 / 13 : ℝ), Zeta2GammaInt.g x :=
    Zeta2GammaInt.integral_f_eq_g _ hsub
  have e2 : ∫ x in Set.Ioo (1 / 13 : ℝ) K, (phi x : ℝ) / x ^ 2 =
      ∫ x in Set.Ioo (1 / 13 : ℝ) K, Zeta2GammaInt.g x :=
    Zeta2GammaInt.integral_f_eq_g _ (Set.Ioo_subset_Ioi_self.trans hsub)
  have hint := Zeta2GammaInt.g_integrableOn_Ioi (1 / 13) (by norm_num)
  have e3 : ∫ x in Set.Ioi (1 / 13 : ℝ), Zeta2GammaInt.g x =
      (∫ x in Set.Ioo (1 / 13 : ℝ) K, Zeta2GammaInt.g x) +
        ∫ x in Set.Ici (K : ℝ), Zeta2GammaInt.g x := by
    rw [← Set.Ioo_union_Ici_eq_Ioi h13, setIntegral_union
      (Set.disjoint_left.2 fun x hx hx' => absurd (Set.mem_Ici.1 hx') (not_le.2 hx.2))
      measurableSet_Ici (hint.mono_set Set.Ioo_subset_Ioi_self)
      (hint.mono_set (Set.Ici_subset_Ioi.2 h13))]
  have hb : ∫ x in Set.Ioi (K : ℝ), Zeta2GammaInt.g x ≤ ∫ x in Set.Ioi (K : ℝ), 3 * (x ^ 2)⁻¹ :=
    setIntegral_mono_on (hint.mono_set (Set.Ioi_subset_Ioi h13.le))
      ((Zeta2GammaInt.integrableOn_inv_sq K hK0).const_mul 3) measurableSet_Ioi fun x _ => by
        rw [Zeta2GammaInt.g, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (Zeta2GammaInt.G_bounds x).2 (inv_nonneg.2 (sq_nonneg x))
  rw [integral_const_mul, integral_inv_sq_Ioi K hK0] at hb
  have hnn : 0 ≤ ∫ x in Set.Ioi (K : ℝ), Zeta2GammaInt.g x := setIntegral_nonneg
    measurableSet_Ioi fun x _ => div_nonneg (Zeta2GammaInt.G_bounds x).1 (sq_nonneg x)
  rw [e1, e2, e3, add_sub_cancel_left, integral_Ici_eq_integral_Ioi, abs_of_nonneg hnn,
    div_eq_mul_inv]
  exact hb

theorem GN_split (K N : ℕ) : GNsum N =
    ∑ p ∈ (Sset N).filter (fun p => N < K * p), ((phi ((N : ℝ) / p)).toNat : ℝ) * log p +
      ∑ p ∈ (Sset N).filter (fun p => K * p ≤ N), ((phi ((N : ℝ) / p)).toNat : ℝ) * log p := by
  rw [GNsum, ← sum_filter_add_sum_filter_not (Sset N) (fun p => N < K * p)]
  exact congrArg _ (sum_congr (filter_congr fun p _ => not_lt) fun _ _ => rfl)

/-- **Lemma 9 (`log G_N / N → γ`).** Combine Lemmas 6–8: for every `K`,
`limsup |GNsum N / N - γ| ≤ 3 log 4 / K + 3/K`, and let `K → ∞`.

* Estimated length: 60 lines (an `ε/3` argument with `Metric.tendsto_atTop`).
* Formalizable directly from the pdf: yes, given Lemmas 6–8. -/
theorem GN_sum_tendsto : Tendsto (fun N : ℕ => GNsum N / N) atTop (𝓝 gammaRate) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hc : 0 < 3 * log 4 + 3 :=
    add_pos (mul_pos (by norm_num) (Real.log_pos (by norm_num))) (by norm_num)
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * (3 * log 4 + 3) / ε)
  have hK0 : (0 : ℝ) < K := lt_trans (div_pos (mul_pos two_pos hc) hε) hK
  have hK1 : 1 ≤ K := Nat.cast_pos.1 hK0
  have hKε : 3 * log 4 / K + 3 / K < ε / 2 := by
    rw [div_lt_iff₀ hε] at hK
    rw [← add_div, div_lt_iff₀ hK0]
    linarith
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.1 (GN_sum_truncated K hK1) (ε / 2) (half_pos hε)
  refine ⟨max N0 1, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (le_trans (le_max_right _ _) hN)
  have hA := hN0 N (le_trans (le_max_left _ _) hN)
  have hB := GN_sum_tail K N
  have hγ := gamma_tail K hK1
  have hB0 : 0 ≤ ∑ p ∈ (Sset N).filter (fun p => K * p ≤ N),
      ((phi ((N : ℝ) / p)).toNat : ℝ) * log p :=
    sum_nonneg fun p _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)
  have hB' : (∑ p ∈ (Sset N).filter (fun p => K * p ≤ N),
      ((phi ((N : ℝ) / p)).toNat : ℝ) * log p) / N ≤ 3 * log 4 / K := by
    rw [div_le_div_iff₀ hNpos hK0, mul_comm]
    exact hB
  have hB0' := div_nonneg hB0 hNpos.le
  rw [Real.dist_eq, abs_lt] at hA
  rw [abs_le] at hγ
  rw [GN_split K N, add_div, Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- **Arithmetic rate (§5)** — restatement of `Zeta2Blueprint.arith_rate`, proved from
Lemmas 1, 2, 5, 9 (Lemmas 3, 4, 6–8 are the ingredients of Lemmas 5 and 9). -/
theorem arith_rate :
    Tendsto (fun N : ℕ => Real.log (kN N) / N) atTop (𝓝 (25 - gammaRate - 233 / 120)) := by
  have hmul : ∀ c : ℕ, 0 < c → Tendsto (fun N : ℕ => log (lcmUpTo (c * N)) / N) atTop
      (𝓝 (c : ℝ)) := by
    intro c hc
    have hc' : Tendsto (fun N : ℕ => c * N) atTop atTop :=
      tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_left N hc) tendsto_id
    have h := (log_lcm_tendsto.comp hc').const_mul (c : ℝ)
    rw [mul_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (N : ℝ) ≠ 0 := by positivity
    have hc0 : (c : ℝ) ≠ 0 := by positivity
    simp only [Function.comp_apply, Nat.cast_mul]
    field_simp
  have h := (((hmul 12 (by norm_num)).add (hmul 13 (by norm_num))).sub GN_sum_tendsto).sub
    shell_sum_tendsto
  have hlim : (((12 : ℕ) : ℝ) + ((13 : ℕ) : ℝ) - gammaRate - 233 / 120) =
      25 - gammaRate - 233 / 120 := by norm_num
  rw [hlim] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [log_kN_eq N hN]
  ring

end Zeta2ArithRate
