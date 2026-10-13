/-
# Definitions for the blueprint of `μ(ζ(2)) < 4.62675`

All definitions of `blueprint.lean` (namespace `Zeta2Blueprint`), shared by the blueprint and the
files proving its nodes.
-/
import Mathlib

open Polynomial Filter Topology Real Finset MeasureTheory
open scoped Matrix

noncomputable section

namespace Zeta2Blueprint

/-! ## §1. Conservation: an exact `2 × 2` toy field -/

/-- The rational potential `F(x,y)` of §1.2; the field is `M_i(w) = F(w)⁻¹ F(w + e_i)`. -/
def toyPot (x y : ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1 + x + 2 * y + 2 * x * y, 3 * y * (1 - x); 3 * x * (1 - y), 1 + 2 * x + y + 2 * x * y]

/-- `A = M_x(0,0)`. -/
def toyA : Matrix (Fin 2) (Fin 2) ℚ := !![2, 0; 3, 3]
/-- `B = M_y(0,0)`. -/
def toyB : Matrix (Fin 2) (Fin 2) ℚ := !![3, 3; 0, 2]
/-- `C = M_y(1,0)`. -/
def toyC : Matrix (Fin 2) (Fin 2) ℚ := !![3, 0; -3, 2]
/-- `D = M_x(0,1)`. -/
def toyD : Matrix (Fin 2) (Fin 2) ℚ := !![2, -3; 0, 3]

/-! ## §3. The native field `pFq(4,3,1)` and the specified trajectory -/

/-- The seven coordinates `x₀,x₁,x₂,x₃` (upper) and `y₀,y₁,y₂` (lower). -/
abbrev Coord := Fin 4 ⊕ Fin 3

/-- A vertex `w = (x₀,x₁,x₂,x₃; y₀,y₁,y₂)`, with `x₃ = -m`. -/
abbrev Vertex := Coord → ℤ

/-- `Q_w(s) = s ∏ᵢ (s + yᵢ - 1) - (s - m) ∏ᵢ (s + xᵢ)` (with `x₃ = -m`), a cubic. -/
def Qw (w : Vertex) : ℚ[X] :=
  X * ∏ i : Fin 3, (X + C ((w (.inr i) : ℚ) - 1)) - ∏ i : Fin 4, (X + C (w (.inl i) : ℚ))

/-- The companion matrix `T_w` of `Q_w = a₀ + a₁ s + a₂ s² + a₃ s³`. -/
def Tw (w : Vertex) : Matrix (Fin 3) (Fin 3) ℚ :=
  let a := fun j => (Qw w).coeff j
  !![0, 0, -a 0 / a 3; 1, 0, -a 1 / a 3; 0, 1, -a 2 / a 3]

/-- The parameter dividing `T_w` in a forward move: `xᵢ` for an upper coordinate and `yᵢ - 1`
for a lower one. -/
def shiftParam (w : Vertex) : Coord → ℚ
  | .inl i => (w (.inl i) : ℚ)
  | .inr i => (w (.inr i) : ℚ) - 1

/-- Forward moves are upper increases and lower decreases; their matrix is `I + T_w / param`.
The other moves are the inverse of the forward move, evaluated at the target. -/
def isForward : Coord → Bool → Bool
  | .inl _, up => up
  | .inr _, up => !up

/-- The vertex after moving coordinate `c` by `+1` (`up = true`) or `-1`. -/
def move (w : Vertex) (c : Coord) (up : Bool) : Vertex :=
  Function.update w c (if up then w c + 1 else w c - 1)

/-- The native generator of one unit move at the current vertex `w` (§3). -/
def stepMat (w : Vertex) (c : Coord) (up : Bool) : Matrix (Fin 3) (Fin 3) ℚ :=
  if isForward c up then 1 + (shiftParam w c)⁻¹ • Tw w
  else (1 + (shiftParam (move w c up) c)⁻¹ • Tw (move w c up))⁻¹

/-- The ordered matrix product along a list of unit moves, starting at `w`. -/
def walk : Vertex → List (Coord × Bool) → Matrix (Fin 3) (Fin 3) ℚ
  | _, [] => 1
  | w, (c, up) :: l => stepMat w c up * walk (move w c up) l

/-- Assemble a direction/vertex from its upper and lower parts. -/
def dir (x : Fin 4 → ℤ) (y : Fin 3 → ℤ) : Vertex := Sum.elim x y

/-- The coordinate order inside one block step: left to right. -/
def coordOrder : List Coord := [.inl 0, .inl 1, .inl 2, .inl 3, .inr 0, .inr 1, .inr 2]

/-- One block step in direction `d`, its coordinate moves made from left to right. -/
def blockStep (d : Vertex) : List (Coord × Bool) :=
  coordOrder.flatMap fun c => List.replicate (d c).natAbs (c, decide (0 ≤ d c))

/-- The four-block route of §3.1 (for `t = 3` or `4`):
`A = (1,1,1,0;0,0,0)^{tN}`, `B = (0,0,0,0;2,1,3)^N`, `C = (10-t,9-t,11-t,0;0,0,0)^N`,
`D = (0,0,0,-1;0,0,0)^{11N}`. -/
def route (t N : ℕ) : List (Coord × Bool) :=
  (List.replicate (t * N) (blockStep (dir ![1, 1, 1, 0] ![0, 0, 0]))).flatten ++
  (List.replicate N (blockStep (dir ![0, 0, 0, 0] ![2, 1, 3]))).flatten ++
  (List.replicate N
    (blockStep (dir ![(10 : ℤ) - t, (9 : ℤ) - t, (11 : ℤ) - t, 0] ![0, 0, 0]))).flatten ++
  (List.replicate (11 * N) (blockStep (dir ![0, 0, 0, -1] ![0, 0, 0]))).flatten

/-- The initial vertex `w₀ = (1,1,1,0;1,1,1)`. -/
def w0 : Vertex := dir ![1, 1, 1, 0] ![1, 1, 1]

/-- The unscaled endpoint product `W(N)` (computed along the `t = 3` route). -/
def W (N : ℕ) : Matrix (Fin 3) (Fin 3) ℚ := walk w0 (route 3 N)

/-- The two initial rows `R`. -/
def Rmat : Matrix (Fin 2) (Fin 3) ℚ := !![0, 2, -1; 2, 0, 0]

/-- The readout `R W(N)`; its column `r` is `(p_{N,r}^{raw}, q_{N,r}^{raw})`. -/
def readout (N : ℕ) : Matrix (Fin 2) (Fin 3) ℚ := Rmat * W N

/-- `𝖯_{N,r} = (R W_N)_{0r}`. -/
abbrev Pread (N : ℕ) (r : Fin 3) : ℚ := readout N 0 r
/-- `𝖰_{N,r} = (R W_N)_{1r}`. -/
abbrev Qread (N : ℕ) (r : Fin 3) : ℚ := readout N 1 r

/-! ### The exact finite readout (§3.2, Appendix A) -/

/-- The binomial polynomial `binom(X + a, b) = (X + a)(X + a - 1)⋯(X + a - b + 1) / b!`. -/
def binomPoly (K : Type*) [Field K] (a : K) (b : ℕ) : K[X] :=
  C ((b.factorial : K)⁻¹) * (descPochhammer K b).comp (X + C a)

/-- `F(s) = binom(s+10N, 8N) binom(s+9N, 8N) binom(s+11N, 8N)`. -/
def Fpoly (N : ℕ) : ℚ[X] :=
  binomPoly ℚ ((10 * N : ℕ) : ℚ) (8 * N) * binomPoly ℚ ((9 * N : ℕ) : ℚ) (8 * N) *
    binomPoly ℚ ((11 * N : ℕ) : ℚ) (8 * N)

/-- `C_N = binom(10N,2N) binom(9N,N) binom(11N,3N) = F(0)`. -/
def CN (N : ℕ) : ℕ := (10 * N).choose (2 * N) * (9 * N).choose N * (11 * N).choose (3 * N)

/-- `c_j = (-1)^j binom(m, j) F(j)`, `m = 11N`. -/
def cj (N j : ℕ) : ℚ := (-1) ^ j * ((11 * N).choose j : ℚ) * (Fpoly N).eval (j : ℚ)

/-- `S_r(s) = ∑_{j=0}^m (-1)^j binom(m,j) (s^r F(s) - j^r F(j)) / (s - j)` (a polynomial). -/
def Spoly (N r : ℕ) : ℚ[X] :=
  ∑ j ∈ range (11 * N + 1), ((-1) ^ j * ((11 * N).choose j : ℚ)) •
    ((X ^ r * Fpoly N - C ((X ^ r * Fpoly N).eval (j : ℚ))) /ₘ (X - C (j : ℚ)))

/-- `H_n^{(2)} = ∑_{k=1}^n k^{-2}`. -/
def harm2 (n : ℕ) : ℚ := ∑ k ∈ Icc 1 n, 1 / (k : ℚ) ^ 2

/-- `J_η(P) = ∑_{h=0}^{deg P} (-1)^h/(h+1) Δ^h P(-η)`, with `Δ^h` expanded. -/
def Jfun (η : ℕ) (P : ℚ[X]) : ℚ :=
  ∑ h ∈ range (P.natDegree + 1), (-1) ^ h / ((h : ℚ) + 1) *
    ∑ i ∈ range (h + 1), (-1) ^ (h - i) * (h.choose i : ℚ) * P.eval ((i : ℚ) - η)

/-! ## §4. The arithmetic normalisation -/

/-- `d_n = lcm(1, …, n)`, `d₀ = 1`. -/
def lcmUpTo (n : ℕ) : ℕ := (Icc 1 n).lcm id

/-- The carry function `ρ(x,y)`. -/
def rho (x y : ℝ) : ℤ :=
  ⌊11 * x⌋ - ⌊y⌋ - ⌊11 * x - y⌋ + ⌊10 * x + y⌋ + ⌊9 * x + y⌋ + ⌊11 * x + y⌋ - 3 * ⌊8 * x⌋ -
    ⌊2 * x + y⌋ - ⌊x + y⌋ - ⌊3 * x + y⌋

/-- `φ(x) = min_{0 ≤ y < 1} ρ(x,y)`. -/
def phi (x : ℝ) : ℤ := ⨅ y : Set.Ico (0 : ℝ) 1, rho x y

/-- `G_N = ∏_{√(50N) < p ≤ 13N} p^{φ(N/p)}`. -/
def GN (N : ℕ) : ℕ :=
  ∏ p ∈ (Icc 1 (13 * N)).filter (fun p => p.Prime ∧ 50 * N < p ^ 2),
    p ^ (phi ((N : ℝ) / p)).toNat

/-- `p` lies in one of the six open prime shells (2) for column `r`:
`((13N+r)/K, u_K N)` for `(K, u_K) = (2,8), (3,9/2), (4,10/3), (5,8/3), (6,9/4), (12,9/8)`. -/
abbrev InShell (N r p : ℕ) : Prop :=
  (13 * N + r < 2 * p ∧ p < 8 * N) ∨ (13 * N + r < 3 * p ∧ 2 * p < 9 * N) ∨
  (13 * N + r < 4 * p ∧ 3 * p < 10 * N) ∨ (13 * N + r < 5 * p ∧ 3 * p < 8 * N) ∨
  (13 * N + r < 6 * p ∧ 4 * p < 9 * N) ∨ (13 * N + r < 12 * p ∧ 8 * p < 9 * N)

/-- `H_{N,r}`: the product of the primes `p > √(50N)` in the six shells. -/
def HN (N r : ℕ) : ℕ :=
  ∏ p ∈ (range (8 * N)).filter (fun p => p.Prime ∧ 50 * N < p ^ 2 ∧ InShell N r p), p

/-! ## §5. The exponential cost of the arithmetic normalisation -/

/-- `k_N = d_{12N} d_{13N} / (G_N H_{N,0})`. -/
def kN (N : ℕ) : ℝ := (lcmUpTo (12 * N) * lcmUpTo (13 * N) : ℕ) / (GN N * HN N 0 : ℕ)

/-- The arithmetic rate `γ = ∫_{1/13}^∞ φ(x) / x² dx`. -/
def gammaRate : ℝ := ∫ x in Set.Ioi (1 / 13 : ℝ), (phi x : ℝ) / x ^ 2

/-! ## §6. Analytic estimates and nonvanishing -/

/-- `ζ(2)`, as a real number (Mathlib: `riemannZeta_two : riemannZeta 2 = π² / 6`). -/
def zeta2 : ℝ := (riemannZeta 2).re

/-- The rational error `𝖤_{N,r} = ζ(2) 𝖰_{N,r} - 𝖯_{N,r}`. -/
def Err (N : ℕ) (r : Fin 3) : ℝ := zeta2 * Qread N r - Pread N r

/-- The point `-η - 1/2 + i y` of the Barnes contour. -/
def barnesLine (η : ℕ) (y : ℝ) : ℂ := -(η : ℂ) - 1 / 2 + y * Complex.I

/-- `𝓘_η(g) = (2πi)⁻¹ ∫_{Re s = -η-1/2} (π / sin πs)² g(s) ds`. -/
def barnesI (η : ℕ) (g : ℂ → ℂ) : ℂ :=
  (1 / (2 * π)) * ∫ y : ℝ,
    ((π : ℂ) / Complex.sin ((π : ℂ) * barnesLine η y)) ^ 2 * g (barnesLine η y)

/-- `L_m(s) = (-1)^m m! / (s (s-1) ⋯ (s-m))`. -/
def Lker (m : ℕ) (s : ℂ) : ℂ := (-1) ^ m * (m.factorial : ℂ) / ∏ j ∈ range (m + 1), (s - j)

/-- The limiting companion matrix `T`. -/
def Tinf : Matrix (Fin 3) (Fin 3) ℚ := !![0, 0, 10890 / 13; 1, 0, 2305 / 13; 0, 1, 42 / 13]

/-- **(A5)**: `A_∞ = ∏_{u ∈ {10,9,11}} (I + T/u)^u (I - T/11)^{-11} ∏_{v ∈ {2,1,3}} (I + T/v)^{-v}`,
the limit of `A_N = S_N⁻¹ M_N S_{N+1}`, `S_N = diag(1, N⁻¹, N⁻²)`. -/
def Ainf : Matrix (Fin 3) (Fin 3) ℚ :=
  (1 + (10 : ℚ)⁻¹ • Tinf) ^ 10 * (1 + (9 : ℚ)⁻¹ • Tinf) ^ 9 * (1 + (11 : ℚ)⁻¹ • Tinf) ^ 11 *
    (1 - (11 : ℚ)⁻¹ • Tinf)⁻¹ ^ 11 * (1 + (2 : ℚ)⁻¹ • Tinf)⁻¹ ^ 2 * (1 + Tinf)⁻¹ *
    (1 + (3 : ℚ)⁻¹ • Tinf)⁻¹ ^ 3

/-! ## §6.6. The irrationality-measure conclusion -/

/-- `μ(α) ≤ μ`: for every `ε > 0` only finitely many `a/b` satisfy `|α - a/b| < b^{-μ-ε}`. -/
def IrrMeasureLE (α μ : ℝ) : Prop :=
  -- ∀ ε > 0, {q : ℤ × ℕ | 0 < q.2 ∧ |α - q.1 / q.2| < (q.2 : ℝ) ^ (-(μ + ε))}.Finite -- this does not cover the reduced case
    ∀ ε > 0, {q : ℚ | |α - q| < (q.den : ℝ) ^ (-(μ + ε))}.Finite

/-- The irrationality measure `μ(α) = inf {μ | μ(α) ≤ μ}`, valued in `EReal`. -/
def irrationalityMeasure (α : ℝ) : EReal := ⨅ (μ : ℝ) (_ : IrrMeasureLE α μ), (μ : EReal)

end Zeta2Blueprint
