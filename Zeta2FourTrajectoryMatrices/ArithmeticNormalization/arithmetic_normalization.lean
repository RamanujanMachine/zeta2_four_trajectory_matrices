/-
# Blueprint: `arithmetic_normalization` (Theorem 1, §4 and Appendix D of the article)

Statement (`Zeta2Blueprint.arithmetic_normalization`, restated verbatim below):
`C_N d_{12N} d_{13N+r} / (G_N H_{N,r}) · R W(N) e_r ∈ ℤ²` for `N ≥ 1`, `r = 0, 1, 2`.

Proof outline.
* Baseline (`Zeta2NextTwo.baseline_integrality`, already proved):
  `z := C_N d_{12N} d_{13N+r} / G_N · R W(N) e_r ∈ ℤ²`.
* It remains to show that every shell prime `p` (a prime `p > √(50N)` in one of the six open
  intervals (2)) divides both entries of `z`; since `H_{N,r}` is the product of these distinct
  primes, `H_{N,r} ∣ z`.
* Fix such `p`, with `h = φ(N/p)`. Read the matrix with the admissible shift `η = p` (if
  `p ≥ 2N`) or `η = 2p` (`shell_eta`; `Zeta2FirstThree.readout_formula`). Since
  `v_p(d_{12N} d_{13N+r}) = 2` and `v_p(G_N) = h` (`lcm_GN_split`), it suffices that
  `v_p(p² · harmonic part) ≥ h + 1` (`harm_val`), `v_p(p² · J_η(S_r)) ≥ h + 1` (`J_val`), and
  `v_p(∑ j^r c_j) ≥ h` (from `Zeta2NextTwo.cZ_dvd`, already proved).
* `harm_val` and `J_val` are Appendix D: the finite-field quotient `𝒬` (Q) has
  `∑_{k ∈ 𝔽_p} k^r 𝒬(k) = 0` (V) (`Qpoly_sum_zero`, from the proved `polyQ_factor` and
  `sum_eval_eq_zero`); the chamber table (T) (`chamber_table`) makes the local data constant on
  the minimal-carry residues; this gives the residue congruence (C') (`kernel_residue`) and the
  divided-difference congruence (S') (`kernel_divided`); with the reduction of `p² H^{(2)}_n`
  (`harm2_reduce`) and Lucas's theorem every leading residue becomes a multiple of the vanishing
  sum (V).

Python checks (finite certificates / diagnostics for the steps above, in
`results/zeta2_complete_proof/code/`): `chamber_certificate.py` (the 390 floor cells behind
`chamber_table`), `check_local_kernel.py` (the local congruences (R), (C'), (S')),
`check_main_shell.py`, `check_fifth_shell.py`, `check_shell_independent.py` (end-to-end shell
divisibility at finite depths).
-/
import Zeta2FourTrajectoryMatrices.FiniteReadout.blueprint_next_two
import Zeta2FourTrajectoryMatrices.ArithmeticNormalization.arithmetic_normalization_chamber
import Zeta2FourTrajectoryMatrices.ArithmeticNormalization.arithmetic_normalization_jval
import Zeta2FourTrajectoryMatrices.ArithmeticNormalization.arithmetic_normalization_kernel3
import Zeta2FourTrajectoryMatrices.ArithmeticNormalization.arithmetic_normalization_sprime2

open Polynomial Finset Zeta2Blueprint Zeta2NextTwo

noncomputable section

namespace Zeta2ArithmeticNormalization

/-- `p` is one of the primes multiplied in `H_{N,r}` (the index set of `HN N r`). -/
abbrev ShellPrime (N r p : ℕ) : Prop := p < 8 * N ∧ p.Prime ∧ 50 * N < p ^ 2 ∧ InShell N r p

/-- The minimal carry `h = φ(N/p)`, as a natural number. -/
def hexp (N p : ℕ) : ℕ := (phi ((N : ℝ) / p)).toNat

/-- The prime-dependent admissible shift `η = p` if `p ≥ 2N`, and `η = 2p` otherwise. -/
def etaP (N p : ℕ) : ℕ := if 2 * N ≤ p then p else 2 * p

/-- The finite-field quotient (Q):
`𝒬 = ∏_{u=9}^{11} binom(X+uN, b) · (X^p - X)^{1-h} / ((X^p - X)^{h-1} ∏_{j=0}^{d} (X - j))`
in `𝔽_p[X]`, where `b = 8N mod p`, `d = 11N mod p` (truncated subtraction encodes both cases
`h = 0` and `h ≥ 1`, exactly as in `polyQ_factor`). -/
def Qpoly (N p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  (binomPoly (ZMod p) ((9 * N : ℕ) : ZMod p) (8 * N % p) *
      binomPoly (ZMod p) ((10 * N : ℕ) : ZMod p) (8 * N % p) *
      binomPoly (ZMod p) ((11 * N : ℕ) : ZMod p) (8 * N % p) * (X ^ p - X) ^ (1 - hexp N p)) /ₘ
    ((X ^ p - X) ^ (hexp N p - 1) * ∏ j ∈ range (11 * N % p + 1), (X - C (j : ZMod p)))

/-- `q ∈ ℤ_(p)` and its reduction modulo `p` is `x`. -/
def Reduces (p : ℕ) (q : ℚ) (x : ZMod p) : Prop :=
  ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q * b = a ∧ (a : ZMod p) = x * b

/-- **Lemma 1 (an admissible prime-dependent shift).** Every shell prime satisfies
`2N ≤ η ≤ 9N` for `η = p` (if `p ≥ 2N`) or `η = 2p` (otherwise; only the shell `K = 12`).

* Estimated length: 15 lines (`omega` on the six shell inequalities).
* Formalizable directly from the pdf: yes (Appendix D, "An admissible prime-dependent
  readout"). -/
theorem shell_eta (N r p : ℕ) (hr : r < 3) (hs : ShellPrime N r p) :
    2 * N ≤ etaP N p ∧ etaP N p ≤ 9 * N := by
  obtain ⟨hp8, -, -, hsh⟩ := hs
  unfold etaP
  split_ifs with h <;> omega

theorem lcm_p_split (n p : ℕ) (pp : p.Prime) (h1 : p ≤ n) (h2 : n < p ^ 2) :
    ∃ U : ℕ, ¬ p ∣ U ∧ lcmUpTo n = p * U := by
  have hf : (lcmUpTo n).factorization p = 1 := by
    rw [show lcmUpTo n = Nat.lcmUpto n from rfl, Nat.factorization_lcmUpto n pp]
    exact Nat.log_eq_one_iff'.2 ⟨h1, by rw [← pow_two]; exact h2⟩
  refine ⟨ordCompl[p] (lcmUpTo n), Nat.not_dvd_ordCompl pp (lcmUpTo_pos n).ne', ?_⟩
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self (lcmUpTo n) p]
  rw [hf, pow_one]

theorem GN_split (N p : ℕ) (pp : p.Prime) (hp1 : p ≤ 13 * N) (hp2 : 50 * N < p ^ 2) :
    ∃ G : ℕ, ¬ p ∣ G ∧ GN N = p ^ hexp N p * G := by
  have hmem : p ∈ Sset N := Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨pp.one_lt.le, hp1⟩, pp, hp2⟩
  refine ⟨∏ q ∈ (Sset N).erase p, q ^ (phi ((N : ℝ) / q)).toNat, fun hd => ?_, ?_⟩
  · obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff pp.prime _).1 hd
    have hq' := Finset.mem_erase.1 hq
    exact hq'.1 ((Nat.prime_dvd_prime_iff_eq pp (mem_Sset hq'.2).1).1 (pp.dvd_of_dvd_pow hpq)).symm
  · exact (Finset.mul_prod_erase (Sset N) (fun q => q ^ (phi ((N : ℝ) / q)).toNat) hmem).symm

/-- **Lemma 2 (`p`-parts of the normalisation).** For a shell prime,
`v_p(d_{12N} d_{13N+r}) = 2` (as `p ≤ 12N < 13N + r < p²`) and `v_p(G_N) = h`
(`p` occurs in `G_N` exactly with exponent `φ(N/p)`).

* Estimated length: 50 lines (`Nat.factorization` of `lcmUpTo`, or `Finset.lcm` with
  `p ∣ k ≤ n < p² ⇒ v_p(k) ≤ 1`; splitting the product `GN` at `p`).
* Formalizable directly from the pdf: yes ("Since `v_p(d_{12N}d_{13N+r}) = 2` and
  `v_p(G_N) = h`"). -/
theorem lcm_GN_split (N r p : ℕ) (hN : 1 ≤ N) (hr : r < 3) (hs : ShellPrime N r p) :
    ∃ U G : ℕ, ¬ p ∣ U ∧ ¬ p ∣ G ∧
      lcmUpTo (12 * N) * lcmUpTo (13 * N + r) = p ^ 2 * U ∧ GN N = p ^ hexp N p * G := by
  obtain ⟨hp8, pp, hp2, -⟩ := hs
  obtain ⟨U1, hU1, e1⟩ := lcm_p_split (12 * N) p pp (by omega) (by omega)
  obtain ⟨U2, hU2, e2⟩ := lcm_p_split (13 * N + r) p pp (by omega) (by omega)
  obtain ⟨G, hG, eG⟩ := GN_split N p pp (by omega) hp2
  refine ⟨U1 * U2, G, fun h => (pp.dvd_mul.1 h).elim hU1 hU2, hG, ?_, eG⟩
  rw [e1, e2, pow_two]
  exact mul_mul_mul_comm p U1 p U2

theorem Qpoly_spec (N r p : ℕ) [Fact p.Prime] (hN : 1 ≤ N) (hr : r < 3)
    (hs : ShellPrime N r p) :
    binomPoly (ZMod p) ((9 * N : ℕ) : ZMod p) (8 * N % p) *
      binomPoly (ZMod p) ((10 * N : ℕ) : ZMod p) (8 * N % p) *
      binomPoly (ZMod p) ((11 * N : ℕ) : ZMod p) (8 * N % p) * (X ^ p - X) ^ (1 - hexp N p) =
      (X ^ p - X) ^ (hexp N p - 1) * (∏ j ∈ range (11 * N % p + 1), (X - C (j : ZMod p))) *
        Qpoly N p ∧ (X ^ r * Qpoly N p).natDegree < p - 1 := by
  obtain ⟨Q, hQ, hdeg⟩ := Zeta2NextTwo.polyQ_factor N r p hN hr hs.2.2.1 hs.2.2.2
  have hm : ((X ^ p - X) ^ (hexp N p - 1) *
      ∏ j ∈ range (11 * N % p + 1), (X - C (j : ZMod p))).Monic :=
    ((monic_X_pow_sub (by rw [degree_X]; exact_mod_cast (Fact.out : p.Prime).one_lt)).pow _).mul
      (monic_prod_of_monic _ _ fun j _ => monic_X_sub_C _)
  have e : Qpoly N p = Q := by
    rw [Qpoly]
    exact (congrArg (· /ₘ _) hQ).trans (mul_divByMonic_cancel_left Q hm)
  rw [e]
  exact ⟨hQ, hdeg⟩

theorem sum_eval_eq_zero (p : ℕ) [Fact p.Prime] (𝒬 : (ZMod p)[X])
    (hdeg : 𝒬.natDegree < p - 1) : ∑ k : ZMod p, 𝒬.eval k = 0 := by
  simp_rw [eval_eq_sum_range]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [← Finset.mul_sum, FiniteField.sum_pow_lt_card_sub_one, mul_zero]
  rw [ZMod.card]
  have := Finset.mem_range.1 hi
  omega

/-- **Lemma 3 (vanishing sum (V)).** `∑_{k ∈ 𝔽_p} k^r 𝒬(k) = 0`, since
`deg(X^r 𝒬) = 13N + r - (K-1)p - 1 < p - 1`.

* Estimated length: 25 lines (`Zeta2NextTwo.polyQ_factor` gives a quotient of the right degree,
  which equals `Qpoly` by uniqueness of division by the monic divisor
  (`Polynomial.mul_divByMonic_cancel_left`); then `Zeta2Blueprint.sum_eval_eq_zero` applied to
  `X^r 𝒬`).
* Formalizable directly from the pdf: yes (all ingredients are already formalised). -/
theorem Qpoly_sum_zero (N r p : ℕ) [Fact p.Prime] (hN : 1 ≤ N) (hr : r < 3)
    (hs : ShellPrime N r p) :
    ∑ k : ZMod p, k ^ r * (Qpoly N p).eval k = 0 := by
  rw [← sum_eval_eq_zero p _ (Qpoly_spec N r p hN hr hs).2]
  exact Finset.sum_congr rfl fun k _ => by rw [eval_mul, eval_pow, eval_X]

/-- **Lemma 4 (the chamber table (T)).** For a shell prime (so `x = N/p` lies in one of the eight
open intervals of (T), the splitting values `5/11`, `10/11` being excluded by `p² > 50N`), all
residues `k ∈ [0, p)` with minimal carry `χ(k) = h` have the same data
`e = 1_{k > d}`, `λ_u = ⌊(k+uN)/p⌋`, `δ_u = 1_{(k+uN) mod p < b}` (`u = 9, 10, 11`).

* Estimated length: 300 lines (eight chambers; in each, the 11 floors of `χ` take one of two
  values (`Zeta2NextTwo.qcase`) and `omega` decides the constancy, as in
  `Zeta2NextTwo.chi_S3`–`chi_S12`; the boundary cases `x = 5/11, 10/11` are excluded by
  `p² > 50N`).
* Formalizable directly from the pdf: yes, but the pdf only lists the table; the case analysis is
  the content of the Python certificate `code/chamber_certificate.py` (390 floor cells), which a
  Lean proof would reproduce chamber by chamber. -/
theorem chamber_table (N r p : ℕ) (hN : 1 ≤ N) (hr : r < 3) (hs : ShellPrime N r p)
    (k k' : ℕ) (hk : k < p) (hk' : k' < p) (hχ : chi N p k = hexp N p)
    (hχ' : chi N p k' = hexp N p) :
    (11 * N % p < k ↔ 11 * N % p < k') ∧
      ∀ u ∈ ({9, 10, 11} : Finset ℕ), (k + u * N) / p = (k' + u * N) / p ∧
        ((k + u * N) % p < 8 * N % p ↔ (k' + u * N) % p < 8 * N % p) :=
  Zeta2ANChamber.chamber_table_core N r p hN hr hs k k' hk hk' hχ hχ'

/-- **Lemma 5 (residues of the whole kernel (C')).** There are `κ ∈ 𝔽_p` and residues
`A_l = res_{V=l} U(V) ∈ 𝔽_p` (of the rational function `U = P/D_e` built from the table data)
such that `p^{-h} c_{k+lp} ≡ κ 𝒬(k) A_l (mod p)` for every `j = k + lp ≤ 11N`.
Proof: the local factorisation (R) `p^{1-h} R(k+pV) ≡ κ 𝒬(k) U(V)` of `R = F · L_{11N}`
(separating the factors divisible by `p` in each binomial and in `L`, with the case `e = 1`;
Lucas's congruence for the first nonzero level; Lemma 4 for independence of `k`), then residues at
`V = l`. Residues outside the minimal-carry support vanish on both sides (`𝒬(k) = 0` there).

* Estimated length: 300 lines (factor count in `binom(j+uN, 8N)` and `binom(11N, j)` at the first
  `p`-level via `Zeta2NextTwo.IP_val`/`choose_pInt`; `Choose.choose_modEq_choose_mod_mul_choose_div`
  (Lucas); evaluation of `𝒬(k)` from (Q)).
* Formalizable directly from the pdf: partially — Appendix D gives the factor count; the
  congruence of rational functions "away from `V = 0, …, M-e`" has to be recast as the
  integer statement below. Diagnostic: `code/check_local_kernel.py`. -/
theorem kernel_residue (N r p : ℕ) [Fact p.Prime] (hN : 1 ≤ N) (hr : r < 3)
    (hs : ShellPrime N r p) :
    ∃ (κ : ZMod p) (Acoef : ℕ → ZMod p), ∀ j ≤ 11 * N,
      ((cZ N j / (p : ℤ) ^ hexp N p : ℤ) : ZMod p) =
        κ * (Qpoly N p).eval ((j % p : ℕ) : ZMod p) * Acoef (j / p) :=
  Zeta2ANKernel.kernel_residue_core N r p hN hr hs (Qpoly N p) (Qpoly_spec N r p hN hr hs).1

/-- **Lemma 6 (the divided-difference kernel (S')).** With `T_r = p^{1-h} S_r`, there are
`κ ∈ 𝔽_p` and `B ∈ 𝔽_p[V]` (the polynomial part of `U`) such that for every integer
`s = k + pV`, `T_r(s) ∈ ℤ_(p)` and `T_r(k + pV) ≡ κ k^r 𝒬(k) B(V) (mod p)`.
Proof: `S_r(s) = s^r R(s) - ∑_j j^r c_j/(s-j)`; subtract the congruent-residue terms using (R) and
Lemma 5; noncongruent terms vanish since `p^h ∣ c_j`; `T_r` is `ℤ_(p)`-valued with degree `< p²`
(baseline interpolation, `Zeta2NextTwo.P_IntVal_p`), so its Newton expansion in `V` has
`ℤ_(p)` coefficients and the congruence also holds at the derivative nodes.

* Estimated length: 250 lines.
* Formalizable directly from the pdf: partially (as Lemma 5; the pdf stresses that the whole
  kernel, not termwise divided differences, is needed in the `e = 1` chambers).
  Diagnostic: `code/check_local_kernel.py`. -/
theorem kernel_divided (N r p : ℕ) [Fact p.Prime] (hN : 1 ≤ N) (hr : r < 3)
    (hs : ShellPrime N r p) :
    ∃ (κ : ZMod p) (B : (ZMod p)[X]), ∀ s : ℤ,
      Reduces p ((p : ℚ) ^ ((1 : ℤ) - hexp N p) * (Spoly N r).eval (s : ℚ))
        (κ * (s : ZMod p) ^ r * (Qpoly N p).eval (s : ZMod p) * B.eval ((s / p : ℤ) : ZMod p)) :=
  Zeta2ANSprime.kernel_divided_core N r p hN hr hs (Qpoly N p) (kernel_residue N r p hN hr hs)
    (Zeta2ANKernel.R_pt_core N r p hN hr hs (Qpoly N p) (Qpoly_spec N r p hN hr hs).1)

theorem Reduces_zero {p : ℕ} (pp : p.Prime) : Reduces p 0 0 :=
  ⟨0, 1, not_dvd_one' pp, by rw [zero_mul, Int.cast_zero], by rw [Int.cast_zero, zero_mul]⟩

theorem Reduces_add {p : ℕ} (pp : p.Prime) {q1 q2 : ℚ} {x1 x2 : ZMod p} (h1 : Reduces p q1 x1)
    (h2 : Reduces p q2 x2) : Reduces p (q1 + q2) (x1 + x2) := by
  obtain ⟨a1, b1, hb1, e1, f1⟩ := h1
  obtain ⟨a2, b2, hb2, e2, f2⟩ := h2
  refine ⟨a1 * b2 + a2 * b1, b1 * b2, fun h => ((pz_prime pp).dvd_or_dvd h).elim hb1 hb2, ?_, ?_⟩
  · rw [Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_mul, ← e1, ← e2]
    ring
  · rw [Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_mul, f1, f2]
    ring

theorem Reduces_sum {p : ℕ} (pp : p.Prime) {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (x : ι → ZMod p) (H : ∀ i ∈ s, Reduces p (f i) (x i)) :
    Reduces p (∑ i ∈ s, f i) (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [sum_empty, sum_empty]; exact Reduces_zero pp
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact Reduces_add pp (H a (mem_insert_self a s)) (ih fun i hi => H i (mem_insert_of_mem hi))

theorem Reduces_zmul {p : ℕ} (z : ℤ) {q : ℚ} {x : ZMod p} (h : Reduces p q x) :
    Reduces p ((z : ℚ) * q) ((z : ZMod p) * x) := by
  obtain ⟨a, b, hb, e, f⟩ := h
  exact ⟨z * a, b, hb, by rw [Int.cast_mul, ← e, mul_assoc], by rw [Int.cast_mul, f, mul_assoc]⟩

theorem pInt_of_Reduces {p : ℕ} {q : ℚ} (h : Reduces p q 0) : pInt p 1 q := by
  obtain ⟨a, b, hb, e, f⟩ := h
  rw [zero_mul, ZMod.intCast_zmod_eq_zero_iff_dvd] at f
  obtain ⟨c, rfl⟩ := f
  exact ⟨c, b, hb, by rw [e, pow_one, Int.cast_mul, Int.cast_natCast]⟩

theorem red_term {p : ℕ} [Fact p.Prime] (k : ℕ) (h1 : 0 < k) (h2 : k < p ^ 2) :
    Reduces p ((p : ℚ) ^ 2 * (1 / (k : ℚ) ^ 2))
      (if p ∣ k then (((k / p : ℕ) : ZMod p) ^ 2)⁻¹ else 0) := by
  have pp : p.Prime := Fact.out
  by_cases hd : p ∣ k
  · rw [ite_eq_left hd]
    obtain ⟨t, rfl⟩ := hd
    have ht : t < p := by
      rw [pow_two] at h2
      exact Nat.lt_of_mul_lt_mul_left h2
    have ht0 : 0 < t := Nat.pos_of_mul_pos_left h1
    have hpt : ¬ p ∣ t := Nat.not_dvd_of_pos_of_lt ht0 ht
    have htz : (t : ZMod p) ≠ 0 := fun h => hpt ((ZMod.natCast_eq_zero_iff t p).1 h)
    have hq : (t : ℚ) ≠ 0 := Nat.cast_ne_zero.2 ht0.ne'
    have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 pp.ne_zero
    refine ⟨1, (t : ℤ) ^ 2,
      fun h => hpt (Int.natCast_dvd_natCast.1 ((pz_prime pp).dvd_of_dvd_pow h)), ?_, ?_⟩
    · rw [Nat.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_one, mul_pow, one_div, mul_inv,
        ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hpq), one_mul,
        inv_mul_cancel₀ (pow_ne_zero 2 hq)]
    · rw [Nat.mul_div_cancel_left t pp.pos, Int.cast_pow, Int.cast_natCast, Int.cast_one,
        inv_mul_cancel₀ (pow_ne_zero 2 htz)]
  · rw [ite_eq_right hd]
    have hq : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.2 h1.ne'
    refine ⟨(p : ℤ) ^ 2, (k : ℤ) ^ 2,
      fun h => hd (Int.natCast_dvd_natCast.1 ((pz_prime pp).dvd_of_dvd_pow h)), ?_, ?_⟩
    · rw [Int.cast_pow, Int.cast_pow, Int.cast_natCast, Int.cast_natCast, mul_assoc, one_div,
        inv_mul_cancel₀ (pow_ne_zero 2 hq), mul_one]
    · rw [Int.cast_pow, Int.cast_natCast, ZMod.natCast_self, zero_pow two_ne_zero, zero_mul]

/-- **Lemma 7 (reduction of the harmonic numbers).** For `n < p²`,
`p² H^{(2)}_n ∈ ℤ_(p)` and `p² H^{(2)}_n ≡ ∑_{t=1}^{⌊n/p⌋} t^{-2} (mod p)`: the terms with
`p ∤ k` have valuation `≥ 2`, and `k = pt` with `t ≤ ⌊n/p⌋ < p` gives the units `t^{-2}`.

* Estimated length: 40 lines (`Finset.sum_filter_add_sum_filter_not`, reindexing the multiples
  of `p`, `Reduces` is closed under sums).
* Formalizable directly from the pdf: yes ("the multiples of `p` not exceeding `j + η` are
  exactly `p, …, (l+A)p`"). -/
theorem harm2_reduce (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : n < p ^ 2) :
    Reduces p ((p : ℚ) ^ 2 * harm2 n) (∑ t ∈ Icc 1 (n / p), ((t : ZMod p) ^ 2)⁻¹) := by
  have pp : p.Prime := Fact.out
  induction n with
  | zero =>
    rw [Nat.zero_div, harm2, Finset.Icc_eq_empty (by omega), sum_empty, sum_empty, mul_zero]
    exact Reduces_zero pp
  | succ n ih =>
    have H := Reduces_add pp (ih (by omega)) (red_term (p := p) (n + 1) (Nat.succ_pos n) hn)
    rw [harm2, Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), mul_add]
    by_cases hd : p ∣ n + 1
    · rw [ite_eq_left hd, Nat.succ_div, ite_eq_left hd] at H
      rw [Nat.succ_div, ite_eq_left hd, Finset.sum_Icc_succ_top (Nat.le_add_left 1 (n / p))]
      exact H
    · rw [ite_eq_right hd, add_zero] at H
      rw [Nat.succ_div, ite_eq_right hd, add_zero]
      exact H

theorem hexp_le_chi (N p : ℕ) (hp0 : 0 < p) (j : ℤ) : (hexp N p : ℤ) ≤ chi N p j :=
  hp_le_chi N p hp0 j

theorem chi_min (N p : ℕ) (hp0 : 0 < p) : ∃ k : ℕ, k < p ∧ chi N p k = hexp N p := by
  by_contra hne
  have H : ∀ k : ℤ, 0 ≤ k → k < p → (hexp N p : ℤ) + 1 ≤ chi N p k := fun k hk0 hk => by
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
    have h1 := hexp_le_chi N p hp0 m
    have h2 : chi N p m ≠ hexp N p := fun he => hne ⟨m, by omega, he⟩
    omega
  have h3 := phi_ge N p hp0 _ H
  have h4 : (hexp N p : ℤ) = phi ((N : ℝ) / p) := Int.toNat_of_nonneg (phi_nonneg N p hp0)
  omega

theorem Q_root (N r p : ℕ) [Fact p.Prime] (hN : 1 ≤ N) (hr : r < 3) (hs : ShellPrime N r p)
    (k : ℕ) (hk : k < p) (hχ : (hexp N p : ℤ) < chi N p k) :
    (Qpoly N p).eval (k : ZMod p) = 0 := by
  have pp : p.Prime := Fact.out
  have hp0 := pp.pos
  have hb : 8 * N % p < p := Nat.mod_lt _ hp0
  have hd : 11 * N % p < p := Nat.mod_lt _ hp0
  have hXp0 : (X ^ p - X : (ZMod p)[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero _ pp.one_lt
  have hb9 := binom_ne_zero ((9 * N : ℕ) : ZMod p) hb
  have hb10 := binom_ne_zero ((10 * N : ℕ) : ZMod p) hb
  have hb11 := binom_ne_zero ((11 * N : ℕ) : ZMod p) hb
  have hf0 := mul_ne_zero (mul_ne_zero hb9 hb10) hb11
  have hR0 := mul_ne_zero hf0 (pow_ne_zero (1 - hexp N p) hXp0)
  have hQ := (Qpoly_spec N r p hN hr hs).1
  have hRHS : (X ^ p - X) ^ (hexp N p - 1) * (∏ j ∈ range (11 * N % p + 1), (X - C (j : ZMod p))) *
      Qpoly N p ≠ 0 := by
    rw [← hQ]
    exact hR0
  have hr0 := FiniteField.roots_X_pow_card_sub_X (ZMod p)
  rw [ZMod.card] at hr0
  have hgp : (∏ j ∈ range (11 * N % p + 1), (X - C (j : ZMod p))) =
      (((Multiset.range (11 * N % p + 1)).map fun j : ℕ => (j : ZMod p)).map
        fun c => X - C c).prod := by
    rw [Multiset.map_map]
    exact Finset.prod_eq_multiset_prod _ _
  have e := congrArg (fun P => Multiset.count (k : ZMod p) P.roots) hQ
  rw [roots_mul hR0, roots_pow, roots_mul hf0, roots_mul (mul_ne_zero hb9 hb10), binom_roots _ hb,
    binom_roots _ hb, binom_roots _ hb, hr0, roots_mul hRHS, roots_mul (left_ne_zero_of_mul hRHS),
    roots_pow, hr0, hgp, roots_multiset_prod_X_sub_C] at e
  simp only [Multiset.count_add, Multiset.count_nsmul, Multiset.count_univ, count_S hb.le,
    count_G hd, val_add_cast, ZMod.val_cast_of_lt hk] at e
  have hc := chi_id N p k hp0 hk
  have hpos : 0 < Multiset.count (k : ZMod p) (Qpoly N p).roots := by
    split_ifs at e hc <;> omega
  exact (mem_roots'.1 (Multiset.count_pos.1 hpos)).2

theorem Qsum_range (N r p : ℕ) [Fact p.Prime] (hN : 1 ≤ N) (hr : r < 3) (hs : ShellPrime N r p) :
    ∑ k ∈ range p, ((k : ℕ) : ZMod p) ^ r * (Qpoly N p).eval (k : ZMod p) = 0 := by
  rw [← Qpoly_sum_zero N r p hN hr hs]
  exact Finset.sum_nbij' (fun k => (k : ZMod p)) ZMod.val (fun a _ => mem_univ _)
    (fun a _ => mem_range.2 (ZMod.val_lt a)) (fun a ha => ZMod.val_cast_of_lt (mem_range.1 ha))
    (fun a _ => ZMod.natCast_zmod_val a) (fun a _ => rfl)

theorem Q_partial (N r p : ℕ) [Fact p.Prime] (hN : 1 ≤ N) (hr : r < 3) (hs : ShellPrime N r p) :
    ∑ k ∈ range (11 * N % p + 1), ((k : ℕ) : ZMod p) ^ r * (Qpoly N p).eval (k : ZMod p) = 0 := by
  have pp : p.Prime := Fact.out
  have hp0 := pp.pos
  have hd : 11 * N % p < p := Nat.mod_lt _ hp0
  obtain ⟨k0, hk0, hχ0⟩ := chi_min N p hp0
  have hz : ∀ k, k < p → (11 * N % p < k0 ↔ ¬ 11 * N % p < k) →
      ((k : ℕ) : ZMod p) ^ r * (Qpoly N p).eval (k : ZMod p) = 0 := fun k hk hne => by
    rw [Q_root N r p hN hr hs k hk ?_, mul_zero]
    have h1 := hexp_le_chi N p hp0 k
    have h2 : chi N p k ≠ hexp N p := fun he => by
      have hc := (chamber_table N r p hN hr hs k0 k hk0 hk hχ0 he).1
      by_cases hdk : 11 * N % p < k
      · exact hne.1 (hc.2 hdk) hdk
      · exact hdk (hc.1 (hne.2 hdk))
    omega
  by_cases hk0d : 11 * N % p < k0
  · exact Finset.sum_eq_zero fun k hk => by
      have := mem_range.1 hk
      exact hz k (by omega) ⟨fun _ => by omega, fun _ => hk0d⟩
  · rw [Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun k hk hk' => hz k
      (mem_range.1 hk) ⟨fun h => absurd h hk0d, fun h => absurd (show 11 * N % p < k by
        rw [mem_range] at hk'; omega) h⟩]
    exact Qsum_range N r p hN hr hs

theorem block_sum {R : Type*} [CommRing R] (F G : ℕ → R) (p M d : ℕ) (hd : d < p)
    (hF : ∑ k ∈ range p, F k = 0) (hFd : ∑ k ∈ range (d + 1), F k = 0) :
    ∑ j ∈ range (p * M + (d + 1)), F (j % p) * G (j / p) = 0 := by
  have hp0 : 0 < p := by omega
  have key : ∀ m n, n ≤ p → ∑ k ∈ range n, F ((p * m + k) % p) * G ((p * m + k) / p) =
      (∑ k ∈ range n, F k) * G m := fun m n hn => by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k hk => by
      have := mem_range.1 hk
      rw [Nat.mul_add_mod, Nat.mul_add_div hp0, Nat.mod_eq_of_lt (by omega),
        Nat.div_eq_of_lt (by omega), add_zero]
  have full : ∀ m, ∑ j ∈ range (p * m), F (j % p) * G (j / p) = 0 := fun m => by
    induction m with
    | zero => rw [mul_zero, sum_range_zero]
    | succ m ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, key m p le_rfl, hF, zero_mul, zero_add]
  rw [Finset.sum_range_add, full M, key M (d + 1) (by omega), hFd, zero_mul, zero_add]

theorem zsum_zero (N r p : ℕ) [Fact p.Prime] (hN : 1 ≤ N) (hr : r < 3) (hs : ShellPrime N r p)
    (κ : ZMod p) (Acoef : ℕ → ZMod p) (hA : ∀ j ≤ 11 * N,
      ((cZ N j / (p : ℤ) ^ hexp N p : ℤ) : ZMod p) =
        κ * (Qpoly N p).eval ((j % p : ℕ) : ZMod p) * Acoef (j / p))
    (A0 : ℕ) (hA0 : etaP N p = A0 * p) :
    ∑ j ∈ range (11 * N + 1), ((((j : ℤ) ^ r * (cZ N j / (p : ℤ) ^ hexp N p) : ℤ) : ZMod p) *
      ∑ t ∈ Icc 1 ((j + etaP N p) / p), ((t : ZMod p) ^ 2)⁻¹) = 0 := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have e : ∀ j ∈ range (11 * N + 1),
      ((((j : ℤ) ^ r * (cZ N j / (p : ℤ) ^ hexp N p) : ℤ) : ZMod p) *
        ∑ t ∈ Icc 1 ((j + etaP N p) / p), ((t : ZMod p) ^ 2)⁻¹) =
      κ * ((((j % p : ℕ) : ZMod p) ^ r * (Qpoly N p).eval ((j % p : ℕ) : ZMod p)) *
        (Acoef (j / p) * ∑ t ∈ Icc 1 (j / p + A0), ((t : ZMod p) ^ 2)⁻¹)) := fun j hj => by
    rw [Int.cast_mul, Int.cast_pow, Int.cast_natCast, hA j (by have := mem_range.1 hj; omega), hA0,
      Nat.add_mul_div_right _ _ hp0, ← ZMod.natCast_mod j p]
    ring
  rw [sum_congr rfl e, show 11 * N + 1 = p * (11 * N / p) + (11 * N % p + 1) by
    rw [← add_assoc, Nat.div_add_mod], ← mul_sum]
  exact (congrArg (κ * ·) (block_sum
    (fun k => ((k : ℕ) : ZMod p) ^ r * (Qpoly N p).eval (k : ZMod p))
    (fun l => Acoef l * ∑ t ∈ Icc 1 (l + A0), ((t : ZMod p) ^ 2)⁻¹) p (11 * N / p) (11 * N % p)
    (Nat.mod_lt _ hp0) (Qsum_range N r p hN hr hs) (Q_partial N r p hN hr hs))).trans (mul_zero κ)

/-- **Lemma 8 (the harmonic part gains a factor `p`).**
`v_p(p² ∑_j j^r c_j H^{(2)}_{j+η}) ≥ h + 1` for `η = etaP N p`.
Proof: write `j = k + lp`; by Lemmas 5 and 7 the residue of `p^{2-h}` times the sum is
`κ (∑_l A_l ∑_{t=1}^{l+A} t^{-2}) ∑_{k ∈ 𝔽_p} k^r 𝒬(k)`, which is `0` by Lemma 3.

* Estimated length: 80 lines.
* Formalizable directly from the pdf: yes, given Lemmas 3, 5, 7. -/
theorem harm_val (N r p : ℕ) [Fact p.Prime] (hN : 1 ≤ N) (hr : r < 3) (hs : ShellPrime N r p) :
    pInt p (hexp N p + 1) ((p : ℚ) ^ 2 *
      ∑ j ∈ range (11 * N + 1), (j : ℚ) ^ r * cj N j * harm2 (j + etaP N p)) := by
  have pp : p.Prime := Fact.out
  have hp2 := hs.2.2.1
  have hη := shell_eta N r p hr hs
  obtain ⟨A0, hA0⟩ : ∃ A0, etaP N p = A0 * p := by
    unfold etaP
    split_ifs
    · exact ⟨1, (one_mul p).symm⟩
    · exact ⟨2, rfl⟩
  obtain ⟨κ, Acoef, hA⟩ := kernel_residue N r p hN hr hs
  have hmain : (p : ℚ) ^ 2 * ∑ j ∈ range (11 * N + 1), (j : ℚ) ^ r * cj N j * harm2 (j + etaP N p) =
      (p : ℚ) ^ hexp N p * ∑ j ∈ range (11 * N + 1),
        (((j : ℤ) ^ r * (cZ N j / (p : ℤ) ^ hexp N p) : ℤ) : ℚ) *
          ((p : ℚ) ^ 2 * harm2 (j + etaP N p)) := by
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun j hj => ?_
    obtain ⟨w, hw⟩ : ∃ w : ℤ, cZ N j = (p : ℤ) ^ hexp N p * w :=
      cZ_dvd N p j pp hp2 (by have := mem_range.1 hj; omega)
    rw [cj_eq, hw, Int.mul_ediv_cancel_left _ (pow_ne_zero _ (by exact_mod_cast pp.ne_zero))]
    push_cast
    ring
  have hred := Reduces_sum pp (range (11 * N + 1)) _ _ fun j hj =>
    Reduces_zmul ((j : ℤ) ^ r * (cZ N j / (p : ℤ) ^ hexp N p))
      (harm2_reduce p (j + etaP N p) (by have := mem_range.1 hj; omega))
  rw [zsum_zero N r p hN hr hs κ Acoef hA A0 hA0] at hred
  have h1 := pInt_mul pp (pInt_of_dvd pp ((p : ℤ) ^ hexp N p) dvd_rfl) (pInt_of_Reduces hred)
  rw [Int.cast_pow, Int.cast_natCast] at h1
  rw [hmain]
  exact h1

/-- **Lemma 9 (the polynomial part gains a factor `p`).** `v_p(p² J_η(S_r)) ≥ h + 1`, i.e.
`J_η(T_r) ∈ ℤ_(p)`. Only the weights `1/(tp)` (index `tp - 1`) can be divisible by `p` since
`deg S_r + 1 ≤ 13N + r < p²`; for those, Lucas's congruence
`(-1)^{tp-1-(up+k)} binom(tp-1, up+k) ≡ (-1)^{t-1-u} binom(t-1, u)` and Lemma 6 at the nodes
`-Ap + up + k` show `Δ^{tp-1} T_r(-Ap)` is a multiple of `∑_k k^r 𝒬(k) = 0` (Lemma 3).

* Estimated length: 200 lines (`Zeta2FirstThree.Jfun_eq` with the bound `13N + r`,
  `Zeta2NextTwo.P_deg`, `Choose.choose_modEq_choose_mod_mul_choose_div`, splitting the inner sum by
  residues of the node index).
* Formalizable directly from the pdf: yes, given Lemmas 3 and 6. -/
theorem J_val (N r p : ℕ) [Fact p.Prime] (hN : 1 ≤ N) (hr : r < 3) (hs : ShellPrime N r p) :
    pInt p (hexp N p + 1) ((p : ℚ) ^ 2 * Jfun (etaP N p) (Spoly N r)) := by
  obtain ⟨κ, B, hB⟩ := kernel_divided N r p hN hr hs
  have hQ := Qpoly_sum_zero N r p hN hr hs
  unfold etaP
  split_ifs
  · have h := Zeta2ANJval.J_val_core N r p hN hr hs.1 hs.2.2.1 (hexp N p) 1 (Or.inl rfl)
      (Qpoly N p) hQ ⟨κ, B, hB⟩
    rwa [one_mul] at h
  · exact Zeta2ANJval.J_val_core N r p hN hr hs.1 hs.2.2.1 (hexp N p) 2 (Or.inr rfl)
      (Qpoly N p) hQ ⟨κ, B, hB⟩

/-- **Theorem 1 (Arithmetic of the native readouts)** — restatement of
`Zeta2Blueprint.arithmetic_normalization`, proved from Lemmas 1, 2, 8, 9 (Lemmas 3–7 are the
ingredients of Lemmas 8–9), `baseline_integrality`, `readout_formula` and `cZ_dvd`. -/
theorem arithmetic_normalization (N : ℕ) (hN : 1 ≤ N) (r : Fin 3) :
    ∃ z : Fin 2 → ℤ, ∀ i,
      ((CN N * lcmUpTo (12 * N) * lcmUpTo (13 * N + r) : ℕ) / (GN N * HN N r : ℕ) : ℚ) *
        readout N i r = z i := by
  obtain ⟨z, hz⟩ := Zeta2NextTwo.baseline_integrality N hN r
  have hGq : (GN N : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.2 (prod_ne_zero_iff.2 fun p hp => pow_ne_zero _ (mem_Sset hp).1.ne_zero)
  -- every shell prime divides both entries of the baseline integer vector `z`
  have hdvd : ∀ i, ∀ p ∈ (range (8 * N)).filter
      (fun p => p.Prime ∧ 50 * N < p ^ 2 ∧ InShell N r p), (p : ℤ) ∣ z i := by
    intro i p hp
    obtain ⟨hp8, pp, hp2, hsh⟩ : p < 8 * N ∧ p.Prime ∧ 50 * N < p ^ 2 ∧ InShell N r p :=
      ⟨mem_range.1 (mem_filter.1 hp).1, (mem_filter.1 hp).2⟩
    have hs : ShellPrime N r p := ⟨hp8, pp, hp2, hsh⟩
    have : Fact p.Prime := ⟨pp⟩
    obtain ⟨hη₁, hη₂⟩ := shell_eta N r p r.2 hs
    have hR := Zeta2FirstThree.readout_formula N r (etaP N p) hη₁ hη₂
    -- `C_N · (R W(N) e_r)_i = 2 X` with `v_p(p² X) ≥ h + 1`
    have hX : ∃ X : ℚ, (CN N : ℚ) * readout N i r = 2 * X ∧
        pInt p (hexp N p + 1) ((p : ℚ) ^ 2 * X) := by
      fin_cases i
      · refine ⟨_, congrFun hR 0, ?_⟩
        rw [mul_add]
        exact pInt_add pp (harm_val N r p hN r.2 hs) (J_val N r p hN r.2 hs)
      · refine ⟨_, congrFun hR 1, ?_⟩
        have hsum : pInt p (hexp N p)
            (∑ j ∈ range (11 * N + 1), (j : ℚ) ^ (r : ℕ) * cj N j) :=
          pInt_sum pp _ _ fun j hj => by
            have e : (j : ℚ) ^ (r : ℕ) * cj N j = (((j : ℤ) ^ (r : ℕ) * cZ N j : ℤ) : ℚ) := by
              rw [cj_eq]; push_cast; ring
            rw [e]
            exact pInt_of_dvd pp _ (Dvd.dvd.mul_left
              (cZ_dvd N p j pp hp2 (by have := mem_range.1 hj; omega)) _)
        have hp2' : pInt p 2 ((p : ℚ) ^ 2) := by
          have := pInt_of_dvd pp ((p : ℤ) ^ 2) dvd_rfl
          push_cast at this
          exact this
        exact pInt_mono (by omega) (pInt_mul pp hp2' hsum)
    obtain ⟨X, hXe, hXp⟩ := hX
    obtain ⟨U, G, hU, hG, hUe, hGe⟩ := lcm_GN_split N r p hN r.2 hs
    -- `z_i · p^h G = 2U · p² X`
    have e1 : (z i : ℚ) * (GN N : ℚ) =
        ((CN N : ℚ) * readout N i r) * ((lcmUpTo (12 * N) * lcmUpTo (13 * N + r) : ℕ) : ℚ) := by
      rw [← hz i]
      field_simp
      push_cast
      ring
    rw [hXe, hUe, hGe] at e1
    push_cast at e1
    have hZ : pInt p (hexp N p + 1) (((z i * ((p : ℤ) ^ hexp N p * G)) : ℤ) : ℚ) := by
      have e2 : (((z i * ((p : ℤ) ^ hexp N p * G)) : ℤ) : ℚ) =
          (((2 * U : ℕ) : ℤ) : ℚ) * ((p : ℚ) ^ 2 * X) := by
        push_cast
        linear_combination e1
      rw [e2]
      have := pInt_mul pp (pInt_int pp ((2 * U : ℕ) : ℤ)) hXp
      rwa [zero_add] at this
    have h3 : (p : ℤ) ^ hexp N p * p ∣ (p : ℤ) ^ hexp N p * (z i * G) := by
      rw [← pow_succ]
      convert dvd_of_pInt pp _ hZ using 1
      ring
    have h4 := (mul_dvd_mul_iff_left (pow_ne_zero _ (by exact_mod_cast pp.ne_zero))).1 h3
    rcases (pz_prime pp).dvd_or_dvd h4 with h5 | h5
    · exact h5
    · exact absurd (Int.natCast_dvd_natCast.1 h5) hG
  -- hence the product `H_{N,r}` of these distinct primes divides `z`
  have hH : ∀ i, (HN N r : ℤ) ∣ z i := fun i => by
    rw [HN, Nat.cast_prod]
    refine Finset.prod_dvd_of_coprime (fun p hp q hq hpq => ?_) (hdvd i)
    exact (Nat.coprime_primes (mem_filter.1 hp).2.1 (mem_filter.1 hq).2.1).2 hpq |>.isCoprime
  have hHq : (HN N r : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.2 (prod_ne_zero_iff.2 fun p hp => (mem_filter.1 hp).2.1.ne_zero)
  choose w hw using hH
  refine ⟨w, fun i => ?_⟩
  have e : ((CN N * lcmUpTo (12 * N) * lcmUpTo (13 * N + r) : ℕ) / (GN N * HN N r : ℕ) : ℚ) *
      readout N i r =
      ((CN N * lcmUpTo (12 * N) * lcmUpTo (13 * N + r) : ℕ) / (GN N : ℚ) * readout N i r) /
        (HN N r : ℚ) := by
    push_cast
    field_simp
  rw [e, hz i, hw i]
  push_cast
  field_simp

end Zeta2ArithmeticNormalization
