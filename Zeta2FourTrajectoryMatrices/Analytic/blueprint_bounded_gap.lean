import Zeta2FourTrajectoryMatrices.FiniteReadout.blueprint_first_three
import Zeta2FourTrajectoryMatrices.Analytic.blueprint_limit_spectrum

open Polynomial Finset Filter Topology Zeta2Blueprint Zeta2FirstThree Zeta2LimitSpectrum
open scoped Matrix

noncomputable section

namespace Zeta2BoundedGap

def dAll : Vertex := dir ![10, 9, 11, -11] ![2, 1, 3]

def blk : List (Coord × Bool) := (List.replicate 1 (blockStep dAll)).flatten

def MN (N : ℕ) : Matrix (Fin 3) (Fin 3) ℚ := walk (eN N) blk

theorem eN_succ (N : ℕ) : eN (N + 1) = vtx (10 * N + 11) (9 * N + 10) (11 * N + 12)
    (-(11 * N) - 11) (2 * N + 3) (N + 2) (3 * N + 4) := by
  rw [eN]
  apply vtx_eq <;> simp only [vtx, dir, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val] <;>
    push_cast <;> ring

theorem endpt_blk (N : ℕ) : endpt (eN N) blk = eN (N + 1) := by
  rw [blk, endpt_block, eN_succ, eN]
  apply vtx_eq <;>
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, vtx, dir, dAll, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val, Nat.cast_one, one_mul] <;> omega

theorem allGood_blk (N : ℕ) (hN : 2 ≤ N) : AllGood (eN N) blk := by
  refine allGood_box _ _ (mono_block _ _ (by decide)) fun v c hb h1 h2 => ?_
  rw [endpt_blk, eN_succ] at hb h1 h2
  rw [eN] at hb
  obtain ⟨⟨a0, e0⟩, ⟨a1, e1⟩, ⟨a2, e2⟩, ⟨a3', e3⟩, ⟨b0, f0⟩, ⟨b1, f1⟩, ⟨b2, f2⟩⟩ := box_vtx hb
  have hN' : (2 : ℤ) ≤ N := by exact_mod_cast hN
  have ha : a3Z v + 1 < 0 := by rw [a3Z_expand]; omega
  rcases c with i | i <;> fin_cases i
  · exact goodR_up v 0 (by decide) (by omega) (by omega)
  · exact goodR_up v 1 (by decide) (by omega) (by omega)
  · exact goodR_up v 2 (by decide) (by omega) (by omega)
  · exact goodR_x3 v (by omega) (forall_fin3 _ (by omega) (by omega) (by omega)) ha
  · have s : v (.inr 0) < 2 * N + 3 := h1 rfl
    exact goodR_low v 0 (by omega) (forall_fin4 _ (by omega) (by omega) (by omega) (by omega)) ha
  · have s : v (.inr 1) < N + 2 := h1 rfl
    exact goodR_low v 1 (by omega) (forall_fin4 _ (by omega) (by omega) (by omega) (by omega)) ha
  · have s : v (.inr 2) < 3 * N + 4 := h1 rfl
    exact goodR_low v 2 (by omega) (forall_fin4 _ (by omega) (by omega) (by omega) (by omega)) ha

theorem W_succ (N : ℕ) (hN : 2 ≤ N) : W (N + 1) = W N * MN N := by
  have hall : AllGood w0 (route 3 N ++ blk) :=
    allGood_append _ _ _ (allGood_route 3 N (Or.inl rfl))
      (by rw [endpt_route]; exact allGood_blk N hN)
  have hrep := rep_walk _ _ hall
  obtain ⟨hT, hP⟩ := pot_walk _ _ hall
  have he : endpt w0 (route 3 N ++ blk) = eN (N + 1) := by
    rw [endpt_append, endpt_route, endpt_blk]
  rw [he] at hrep hT hP
  rw [Th_w0, one_mul] at hT
  rw [Pp_w0, one_mul] at hP
  rw [← hT, ← hP, walk_append, endpt_route] at hrep
  have h2 := rep_route 3 (N + 1) (Or.inl rfl)
  change walk w0 (route 3 (N + 1)) = walk w0 (route 3 N) * walk (eN N) blk
  refine mat_eq_of_mulVec _ _ fun z => ?_
  obtain ⟨g, rfl⟩ := surj_eN (N + 1) z
  rw [h2 g, hrep g]

/-! ### Invertibility of `W N` -/

def AllInv : Vertex → List (Coord × Bool) → Prop
  | _, [] => True
  | w, (c, up) :: l => IsUnit (stepMat w c up).det ∧ AllInv (move w c up) l

theorem det_walk_inv : ∀ (l : List (Coord × Bool)) (w : Vertex), AllInv w l →
    IsUnit (walk w l).det
  | [], _, _ => by simp only [walk, Matrix.det_one, isUnit_one]
  | (c, up) :: l, w, h => by
    simp only [walk]
    rw [Matrix.det_mul]
    exact h.1.mul (det_walk_inv l _ h.2)

theorem allInv_append : ∀ (l1 l2 : List (Coord × Bool)) (w : Vertex),
    AllInv w l1 → AllInv (endpt w l1) l2 → AllInv w (l1 ++ l2)
  | [], _, _, _, h => h
  | (_, _) :: l1, l2, _, h1, h2 => ⟨h1.1, allInv_append l1 l2 _ h1.2 h2⟩

theorem allInv_box : ∀ (l : List (Coord × Bool)) (w : Vertex), (∀ x ∈ l, x.2 = sig x.1) →
    (∀ v c, InBox w (endpt w l) v → (sig c = true → v c < endpt w l c) →
      (sig c = false → endpt w l c < v c) → IsUnit (stepMat v c (sig c)).det) →
    AllInv w l
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
      allInv_box l _ hl' fun v c hb h1 h2 => H v c (fun c' => ?_) h1 h2⟩
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

theorem detU_up (v : Vertex) (i : Fin 4) (h1 : 1 ≤ v (.inl i))
    (hy : ∀ k : Fin 3, v (.inr k) ≤ v (.inl i)) (ha : a3Z v < 0) :
    IsUnit (stepMat v (.inl i) true).det := by
  have hs : stepMat v (.inl i) true = 1 + (shiftParam v (.inl i))⁻¹ • Tw v := by
    simp only [stepMat, isForward, ↓reduceIte]
  have hsp : shiftParam v (.inl i) = (v (.inl i) : ℚ) := rfl
  have hp : (v (.inl i) : ℚ) ≠ 0 := by exact_mod_cast (by omega : v (.inl i) ≠ 0)
  rw [hs, hsp]
  refine isUnit_det_step _ _ hp (a3_neg_of v ha).ne ?_
  rw [Qw_eq, eval_sub]
  have hD : (Dpol v).eval (-(v (.inl i) : ℚ)) = 0 := by
    unfold Dpol
    rw [eval_prod, prod_eq_zero (mem_univ i)]
    rw [eval_add, eval_X, eval_C]
    ring
  rw [hD, sub_zero, Apol, eval_mul, eval_X, eval_prod]
  refine mul_ne_zero (neg_ne_zero.2 hp) ?_
  rw [prod_ne_zero_iff]
  intro k _
  rw [eval_add, eval_X, eval_C]
  have : ((-(v (.inl i)) + (v (.inr k) - 1) : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast (show -(v (.inl i)) + (v (.inr k) - 1) ≠ 0 by have := hy k; omega)
  rwa [Int.cast_add, Int.cast_neg, Int.cast_sub, Int.cast_one] at this

theorem detU_inv (v : Vertex) (c : Coord) (up : Bool) (hf : isForward c up = false)
    (hg : Good v c up) : IsUnit (stepMat v c up).det := by
  rw [stepMat_inv v c up hf]
  exact Matrix.isUnit_nonsing_inv_det _ (hg.2.2.2 hf).2

theorem allInv_of_inv : ∀ (l : List (Coord × Bool)) (w : Vertex), AllGood w l →
    (∀ x ∈ l, isForward x.1 x.2 = false) → AllInv w l
  | [], _, _, _ => trivial
  | (c, up) :: l, w, h, hl =>
    ⟨detU_inv w c up (hl (c, up) List.mem_cons_self) h.1.1,
      allInv_of_inv l _ h.2 fun x hx => hl x (List.mem_cons_of_mem _ hx)⟩

theorem inv_B (N : ℕ) : ∀ x ∈ blkB N, isForward x.1 x.2 = false := by
  rintro ⟨c, up⟩ hx
  obtain ⟨h1, h2⟩ := mem_block _ _ _ hx
  exact (by decide : ∀ (c : Coord) (up : Bool), dir ![0, 0, 0, 0] ![2, 1, 3] c ≠ 0 →
    up = decide (0 ≤ dir ![0, 0, 0, 0] ![2, 1, 3] c) → isForward c up = false) c up h1 h2

theorem inv_D (N : ℕ) : ∀ x ∈ blkD N, isForward x.1 x.2 = false := by
  rintro ⟨c, up⟩ hx
  obtain ⟨h1, h2⟩ := mem_block _ _ _ hx
  exact (by decide : ∀ (c : Coord) (up : Bool), dir ![0, 0, 0, -1] ![0, 0, 0] c ≠ 0 →
    up = decide (0 ≤ dir ![0, 0, 0, -1] ![0, 0, 0] c) → isForward c up = false) c up h1 h2

theorem allInv_A (N : ℕ) : AllInv w0 (blkA 3 N) := by
  refine allInv_box _ _ (mono_block _ _ (by decide)) fun v c hb h1 h2 => ?_
  rw [endpt_A, w0_eq] at hb
  rw [endpt_A] at h1 h2
  obtain ⟨⟨a0, e0⟩, ⟨a1, e1⟩, ⟨a2, e2⟩, ⟨a3', e3⟩, ⟨b0, f0⟩, ⟨b1, f1⟩, ⟨b2, f2⟩⟩ := box_vtx hb
  have ha : a3Z v < 0 := by rw [a3Z_expand]; omega
  rcases c with i | i <;> fin_cases i
  · exact detU_up v 0 a0 (forall_fin3 _ (by omega) (by omega) (by omega)) ha
  · exact detU_up v 1 a1 (forall_fin3 _ (by omega) (by omega) (by omega)) ha
  · exact detU_up v 2 a2 (forall_fin3 _ (by omega) (by omega) (by omega)) ha
  · have s : (0 : ℤ) < v (.inl 3) := h2 rfl
    exfalso; omega
  · have s : v (.inr 0) < 1 := h1 rfl
    exfalso; omega
  · have s : v (.inr 1) < 1 := h1 rfl
    exfalso; omega
  · have s : v (.inr 2) < 1 := h1 rfl
    exfalso; omega

theorem allInv_C (N : ℕ) :
    AllInv (vtx (((3 : ℕ) : ℤ) * N + 1) (((3 : ℕ) : ℤ) * N + 1) (((3 : ℕ) : ℤ) * N + 1) 0
      (2 * N + 1) (N + 1) (3 * N + 1)) (blkC 3 N) := by
  refine allInv_box _ _ (mono_block _ _ (by decide)) fun v c hb h1 h2 => ?_
  rw [endpt_C] at hb h1 h2
  obtain ⟨⟨a0, e0⟩, ⟨a1, e1⟩, ⟨a2, e2⟩, ⟨a3', e3⟩, ⟨b0, f0⟩, ⟨b1, f1⟩, ⟨b2, f2⟩⟩ := box_vtx hb
  have ha : a3Z v < 0 := by rw [a3Z_expand]; push_cast at a0 a1 a2; omega
  rcases c with i | i <;> fin_cases i
  · exact detU_up v 0 (by push_cast at a0; omega)
      (forall_fin3 _ (by push_cast at a0; omega) (by push_cast at a0; omega)
        (by push_cast at a0; omega)) ha
  · exact detU_up v 1 (by push_cast at a1; omega)
      (forall_fin3 _ (by push_cast at a1; omega) (by push_cast at a1; omega)
        (by push_cast at a1; omega)) ha
  · exact detU_up v 2 (by push_cast at a2; omega)
      (forall_fin3 _ (by push_cast at a2; omega) (by push_cast at a2; omega)
        (by push_cast at a2; omega)) ha
  · have s : (0 : ℤ) < v (.inl 3) := h2 rfl
    exfalso; omega
  · have s : v (.inr 0) < 2 * N + 1 := h1 rfl
    exfalso; omega
  · have s : v (.inr 1) < N + 1 := h1 rfl
    exfalso; omega
  · have s : v (.inr 2) < 3 * N + 1 := h1 rfl
    exfalso; omega

theorem allInv_route (N : ℕ) : AllInv w0 (route 3 N) := by
  rw [route_eq]
  refine allInv_append _ _ _ (allInv_append _ _ _ (allInv_append _ _ _ (allInv_A N) ?_) ?_) ?_
  · rw [endpt_A]
    exact allInv_of_inv _ _ (allGood_B N _ _ _ (by push_cast; omega) (by push_cast; omega)
      (by push_cast; omega)) (inv_B N)
  · rw [endpt_append, endpt_A, endpt_B]
    exact allInv_C N
  · rw [endpt_append, endpt_append, endpt_A, endpt_B, endpt_C]
    exact allInv_of_inv _ _ (allGood_D N) (inv_D N)

theorem det_W (N : ℕ) : IsUnit (W N).det := det_walk_inv _ _ (allInv_route N)

/-! ### Real scaling -/

def rc : Matrix (Fin 3) (Fin 3) ℚ →+* Matrix (Fin 3) (Fin 3) ℝ := (Rat.castHom ℝ).mapMatrix

theorem rc_apply (M : Matrix (Fin 3) (Fin 3) ℚ) (i j : Fin 3) : rc M i j = (M i j : ℝ) := rfl

theorem rc_det (M : Matrix (Fin 3) (Fin 3) ℚ) : (rc M).det = (M.det : ℝ) :=
  ((Rat.castHom ℝ).map_det M).symm

theorem rc_inv (M : Matrix (Fin 3) (Fin 3) ℚ) (h : IsUnit M.det) : rc M⁻¹ = (rc M)⁻¹ :=
  (Matrix.inv_eq_left_inv (by rw [← map_mul, Matrix.nonsing_inv_mul _ h, map_one])).symm

def dg (N : ℕ) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal fun i => (N : ℝ) ^ (i : ℕ)

def sg (N : ℕ) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal fun i => ((N : ℝ) ^ (i : ℕ))⁻¹

theorem sg_dg (N : ℕ) (hN : N ≠ 0) : sg N * dg N = 1 := by
  rw [sg, dg, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact inv_mul_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.2 hN))

theorem dg_sg (N : ℕ) (hN : N ≠ 0) : dg N * sg N = 1 := by
  rw [sg, dg, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact mul_inv_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.2 hN))

def conj (N : ℕ) (M : Matrix (Fin 3) (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℝ := dg N * rc M * sg N

theorem conj_apply (N : ℕ) (M : Matrix (Fin 3) (Fin 3) ℚ) (i j : Fin 3) :
    conj N M i j = (N : ℝ) ^ (i : ℕ) * (M i j : ℝ) * ((N : ℝ) ^ (j : ℕ))⁻¹ := by
  rw [conj, sg, dg, Matrix.mul_diagonal, Matrix.diagonal_mul, rc_apply]

theorem conj_mul (N : ℕ) (hN : N ≠ 0) (A B : Matrix (Fin 3) (Fin 3) ℚ) :
    conj N (A * B) = conj N A * conj N B := by
  simp only [conj, map_mul]
  rw [show dg N * rc A * sg N * (dg N * rc B * sg N) =
    dg N * rc A * (sg N * dg N) * rc B * sg N by simp only [mul_assoc], sg_dg N hN, mul_one]
  simp only [mul_assoc]

theorem conj_one (N : ℕ) (hN : N ≠ 0) : conj N 1 = 1 := by
  rw [conj, map_one, mul_one, dg_sg N hN]

theorem conj_inv (N : ℕ) (hN : N ≠ 0) (A : Matrix (Fin 3) (Fin 3) ℚ) (h : IsUnit A.det) :
    conj N A⁻¹ = (conj N A)⁻¹ :=
  (Matrix.inv_eq_left_inv
    (by rw [← conj_mul N hN, Matrix.nonsing_inv_mul _ h, conj_one N hN])).symm

/-! ### The affine vertex family -/

def aff (e : Vertex) (N : ℕ) : Vertex := fun c => dAll c * N + e c

theorem dAll_x0 : dAll (.inl 0) = 10 := rfl
theorem dAll_x1 : dAll (.inl 1) = 9 := rfl
theorem dAll_x2 : dAll (.inl 2) = 11 := rfl
theorem dAll_x3 : dAll (.inl 3) = -11 := rfl
theorem dAll_y0 : dAll (.inr 0) = 2 := rfl
theorem dAll_y1 : dAll (.inr 1) = 1 := rfl
theorem dAll_y2 : dAll (.inr 2) = 3 := rfl

theorem eN_eq_aff (N : ℕ) : eN N = aff w0 N := by
  funext c
  rcases c with i | i <;> fin_cases i <;> simp [eN, vtx, dir, aff, dAll, w0]

theorem move_aff (e : Vertex) (N : ℕ) (c : Coord) (up : Bool) :
    move (aff e N) c up = aff (move e c up) N := by
  funext c'
  by_cases h : c' = c
  · subst h
    simp only [move_self, aff]
    cases up <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring
  · simp only [move_ne _ _ _ _ h, aff]

theorem shiftParam_aff (e : Vertex) (N : ℕ) (c : Coord) :
    shiftParam (aff e N) c = (dAll c : ℚ) * N + shiftParam e c := by
  rcases c with i | i
  · simp only [shiftParam, aff, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  · simp only [shiftParam, aff, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    ring

/-! ### Coefficients of `Q_w` -/

def xq (w : Vertex) (i : Fin 4) : ℚ := w (.inl i)

def yq (w : Vertex) (j : Fin 3) : ℚ := (w (.inr j) : ℚ) - 1

def k0 (w : Vertex) : ℚ := -(xq w 0 * xq w 1 * xq w 2 * xq w 3)

def k1 (w : Vertex) : ℚ := yq w 0 * yq w 1 * yq w 2 - (xq w 0 * xq w 1 * xq w 2 +
  xq w 0 * xq w 1 * xq w 3 + xq w 0 * xq w 2 * xq w 3 + xq w 1 * xq w 2 * xq w 3)

def k2 (w : Vertex) : ℚ := (yq w 0 * yq w 1 + yq w 0 * yq w 2 + yq w 1 * yq w 2) -
  (xq w 0 * xq w 1 + xq w 0 * xq w 2 + xq w 0 * xq w 3 + xq w 1 * xq w 2 + xq w 1 * xq w 3 +
    xq w 2 * xq w 3)

def k3 (w : Vertex) : ℚ := (yq w 0 + yq w 1 + yq w 2) - (xq w 0 + xq w 1 + xq w 2 + xq w 3)

theorem Qw_explicit (w : Vertex) :
    Qw w = C (k0 w) + C (k1 w) * X + C (k2 w) * X ^ 2 + C (k3 w) * X ^ 3 := by
  change X * ∏ j : Fin 3, (X + C (yq w j)) - ∏ i : Fin 4, (X + C (xq w i)) = _
  rw [Fin.prod_univ_three, Fin.prod_univ_four]
  simp only [k0, k1, k2, k3, C_add, C_sub, C_mul, C_neg]
  ring

theorem coeff_Qw (w : Vertex) : (Qw w).coeff 0 = k0 w ∧ (Qw w).coeff 1 = k1 w ∧
    (Qw w).coeff 2 = k2 w ∧ a3 w = k3 w := by
  rw [a3, Qw_explicit]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

theorem xq_aff (e : Vertex) (N : ℕ) (i : Fin 4) :
    xq (aff e N) i = (dAll (.inl i) : ℚ) * N + xq e i := by
  simp only [xq, aff, Int.cast_add, Int.cast_mul, Int.cast_natCast]

theorem yq_aff (e : Vertex) (N : ℕ) (j : Fin 3) :
    yq (aff e N) j = (dAll (.inr j) : ℚ) * N + yq e j := by
  simp only [yq, aff, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  ring

theorem k3_aff (e : Vertex) (N : ℕ) : k3 (aff e N) = -13 * N + k3 e := by
  simp only [k3, xq_aff, yq_aff, dAll_x0, dAll_x1, dAll_x2, dAll_x3, dAll_y0, dAll_y1, dAll_y2]
  push_cast
  ring

theorem k2_aff (e : Vertex) : ∃ B C : ℚ, ∀ N : ℕ, k2 (aff e N) = 42 * N ^ 2 + B * N + C :=
  ⟨-9 * xq e 0 - 10 * xq e 1 - 8 * xq e 2 - 30 * xq e 3 + 4 * yq e 0 + 5 * yq e 1 + 3 * yq e 2,
    k2 e, fun N => by
      simp only [k2, xq_aff, yq_aff, dAll_x0, dAll_x1, dAll_x2, dAll_x3, dAll_y0, dAll_y1, dAll_y2]
      push_cast
      ring⟩

theorem k1_aff (e : Vertex) :
    ∃ B C D : ℚ, ∀ N : ℕ, k1 (aff e N) = 2305 * N ^ 3 + B * N ^ 2 + C * N + D :=
  ⟨121 * xq e 0 + 121 * xq e 1 + 119 * xq e 2 - 299 * xq e 3 + 3 * yq e 0 + 6 * yq e 1 +
      2 * yq e 2,
    2 * xq e 0 * xq e 2 - 20 * xq e 0 * xq e 3 + xq e 1 * xq e 2 - 21 * xq e 1 * xq e 3 -
      19 * xq e 2 * xq e 3 + 3 * yq e 0 * yq e 1 + yq e 0 * yq e 2 + 2 * yq e 1 * yq e 2,
    k1 e, fun N => by
      simp only [k1, xq_aff, yq_aff, dAll_x0, dAll_x1, dAll_x2, dAll_x3, dAll_y0, dAll_y1, dAll_y2]
      push_cast
      ring⟩

theorem k0_aff (e : Vertex) :
    ∃ B C D E : ℚ, ∀ N : ℕ, k0 (aff e N) = 10890 * N ^ 4 + B * N ^ 3 + C * N ^ 2 + D * N + E :=
  ⟨1089 * xq e 0 + 1210 * xq e 1 + 990 * xq e 2 - 990 * xq e 3,
    121 * xq e 0 * xq e 1 + 99 * xq e 0 * xq e 2 - 99 * xq e 0 * xq e 3 + 110 * xq e 1 * xq e 2 -
      110 * xq e 1 * xq e 3 - 90 * xq e 2 * xq e 3,
    11 * xq e 0 * xq e 1 * xq e 2 - 11 * xq e 0 * xq e 1 * xq e 3 - 9 * xq e 0 * xq e 2 * xq e 3 -
      10 * xq e 1 * xq e 2 * xq e 3,
    k0 e, fun N => by
      simp only [k0, xq_aff, dAll_x0, dAll_x1, dAll_x2, dAll_x3]
      push_cast
      ring⟩

/-! ### Elementary limits -/

theorem tendsto_div_pow (c : ℝ) (k : ℕ) (hk : k ≠ 0) :
    Tendsto (fun N : ℕ => c / (N : ℝ) ^ k) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop ((tendsto_pow_atTop hk).comp tendsto_natCast_atTop_atTop)

theorem lim_deg1 (A B : ℝ) : Tendsto (fun N : ℕ => (A * N + B) / N) atTop (𝓝 A) := by
  have h : ∀ᶠ N : ℕ in atTop, (A * N + B) / N = A + B / N := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    field_simp
  rw [tendsto_congr' h]
  have := (tendsto_const_nhds (x := A)).add (tendsto_div_pow B 1 one_ne_zero)
  simp only [pow_one, add_zero] at this
  exact this

theorem lim_deg2 (A B C : ℝ) :
    Tendsto (fun N : ℕ => (A * N ^ 2 + B * N + C) / N ^ 2) atTop (𝓝 A) := by
  have h : ∀ᶠ N : ℕ in atTop, (A * N ^ 2 + B * N + C) / N ^ 2 = A + B / N + C / N ^ 2 := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    field_simp
  rw [tendsto_congr' h]
  have := ((tendsto_const_nhds (x := A)).add (tendsto_div_pow B 1 one_ne_zero)).add
    (tendsto_div_pow C 2 two_ne_zero)
  simp only [pow_one, add_zero] at this
  exact this

theorem lim_deg3 (A B C D : ℝ) :
    Tendsto (fun N : ℕ => (A * N ^ 3 + B * N ^ 2 + C * N + D) / N ^ 3) atTop (𝓝 A) := by
  have h : ∀ᶠ N : ℕ in atTop, (A * N ^ 3 + B * N ^ 2 + C * N + D) / N ^ 3 =
      A + B / N + C / N ^ 2 + D / N ^ 3 := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    field_simp
  rw [tendsto_congr' h]
  have := (((tendsto_const_nhds (x := A)).add (tendsto_div_pow B 1 one_ne_zero)).add
    (tendsto_div_pow C 2 two_ne_zero)).add (tendsto_div_pow D 3 three_ne_zero)
  simp only [pow_one, add_zero] at this
  exact this

theorem lim_deg4 (A B C D E : ℝ) :
    Tendsto (fun N : ℕ => (A * N ^ 4 + B * N ^ 3 + C * N ^ 2 + D * N + E) / N ^ 4) atTop
      (𝓝 A) := by
  have h : ∀ᶠ N : ℕ in atTop, (A * N ^ 4 + B * N ^ 3 + C * N ^ 2 + D * N + E) / N ^ 4 =
      A + B / N + C / N ^ 2 + D / N ^ 3 + E / N ^ 4 := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    field_simp
  rw [tendsto_congr' h]
  have := ((((tendsto_const_nhds (x := A)).add (tendsto_div_pow B 1 one_ne_zero)).add
    (tendsto_div_pow C 2 two_ne_zero)).add (tendsto_div_pow D 3 three_ne_zero)).add
    (tendsto_div_pow E 4 four_ne_zero)
  simp only [pow_one, add_zero] at this
  exact this

theorem tendsto_matrix {f : ℕ → Matrix (Fin 3) (Fin 3) ℝ} {L : Matrix (Fin 3) (Fin 3) ℝ}
    (h : ∀ i j, Tendsto (fun N => f N i j) atTop (𝓝 (L i j))) : Tendsto f atTop (𝓝 L) :=
  tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => h i j

theorem tendsto_matrix_elem {f : ℕ → Matrix (Fin 3) (Fin 3) ℝ} {L : Matrix (Fin 3) (Fin 3) ℝ}
    (h : Tendsto f atTop (𝓝 L)) (i j : Fin 3) : Tendsto (fun N => f N i j) atTop (𝓝 (L i j)) :=
  tendsto_pi_nhds.1 (tendsto_pi_nhds.1 h i) j

theorem lim_k3 (e : Vertex) : Tendsto (fun N : ℕ => (k3 (aff e N) : ℝ) / N) atTop (𝓝 (-13)) :=
  (lim_deg1 (-13) (k3 e : ℝ)).congr fun N => by rw [k3_aff]; push_cast; ring

theorem lim_k2 (e : Vertex) :
    Tendsto (fun N : ℕ => (k2 (aff e N) : ℝ) / N ^ 2) atTop (𝓝 42) := by
  obtain ⟨B, C, h⟩ := k2_aff e
  exact (lim_deg2 42 B C).congr fun N => by rw [h]; push_cast; ring

theorem lim_k1 (e : Vertex) :
    Tendsto (fun N : ℕ => (k1 (aff e N) : ℝ) / N ^ 3) atTop (𝓝 2305) := by
  obtain ⟨B, C, D, h⟩ := k1_aff e
  exact (lim_deg3 2305 B C D).congr fun N => by rw [h]; push_cast; ring

theorem lim_k0 (e : Vertex) :
    Tendsto (fun N : ℕ => (k0 (aff e N) : ℝ) / N ^ 4) atTop (𝓝 10890) := by
  obtain ⟨B, C, D, E, h⟩ := k0_aff e
  exact (lim_deg4 10890 B C D E).congr fun N => by rw [h]; push_cast; ring

theorem lim_p (s t : ℚ) : Tendsto (fun N : ℕ => ((s * N + t : ℚ) : ℝ) / N) atTop (𝓝 s) :=
  (lim_deg1 s t).congr fun N => by push_cast; ring

/-! ### The limit of one scaled factor -/

theorem one_add_smul_Tw (q : ℚ) (w : Vertex) :
    1 + q • Tw w = !![1, 0, q * (-(Qw w).coeff 0 / a3 w); q, 1, q * (-(Qw w).coeff 1 / a3 w);
      0, q, 1 + q * (-(Qw w).coeff 2 / a3 w)] := by
  rw [Tw_eq, Matrix.one_fin_three, Matrix.smul_of, Matrix.of_add_of]
  simp only [Matrix.smul_cons, Matrix.smul_empty, Matrix.cons_add_cons, Matrix.empty_add_empty,
    smul_eq_mul, mul_zero, add_zero, mul_one, zero_add]

def Finf (c : Coord) : Matrix (Fin 3) (Fin 3) ℝ := rc (1 + (dAll c : ℚ)⁻¹ • Tinf)

theorem Finf_eq (s : ℚ) : 1 + s⁻¹ • Tinf = !![1, 0, s⁻¹ * (10890 / 13); s⁻¹, 1, s⁻¹ * (2305 / 13);
    0, s⁻¹, 1 + s⁻¹ * (42 / 13)] := by
  rw [Tinf, Matrix.one_fin_three, Matrix.smul_of, Matrix.of_add_of]
  simp only [Matrix.smul_cons, Matrix.smul_empty, Matrix.cons_add_cons, Matrix.empty_add_empty,
    smul_eq_mul, mul_zero, add_zero, mul_one, zero_add]

theorem factor_tendsto (e : Vertex) (c : Coord) (hc : dAll c ≠ 0) (t : ℚ) :
    Tendsto (fun N : ℕ => conj N (1 + ((dAll c : ℚ) * N + t)⁻¹ • Tw (aff e N))) atTop
      (𝓝 (Finf c)) := by
  obtain ⟨s, hs_def⟩ : ∃ s : ℚ, s = (dAll c : ℚ) := ⟨_, rfl⟩
  have hs : s ≠ 0 := by rw [hs_def]; exact_mod_cast hc
  have hsr : (s : ℝ) ≠ 0 := by exact_mod_cast hs
  rw [← hs_def]
  simp only [Finf, ← hs_def, one_add_smul_Tw, Finf_eq]
  have L3 := lim_k3 e
  have L2 := lim_k2 e
  have L1 := lim_k1 e
  have L0 := lim_k0 e
  have Lp := lim_p s t
  have hA3 : ∀ᶠ N : ℕ in atTop, (k3 (aff e N) : ℝ) ≠ 0 := by
    filter_upwards [L3.eventually_ne (by norm_num : (-13 : ℝ) ≠ 0)] with N h1 h0
    exact h1 (by rw [h0, zero_div])
  have hP : ∀ᶠ N : ℕ in atTop, ((s * N + t : ℚ) : ℝ) ≠ 0 := by
    filter_upwards [Lp.eventually_ne hsr] with N h1 h0
    exact h1 (by rw [h0, zero_div])
  have hN0 : ∀ᶠ N : ℕ in atTop, (N : ℝ) ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact Nat.cast_ne_zero.2 hN.ne'
  refine tendsto_matrix fun i j => ?_
  simp only [conj_apply, rc_apply, (coeff_Qw _).1, (coeff_Qw _).2.1, (coeff_Qw _).2.2.1,
    (coeff_Qw _).2.2.2]
  have h13 : (-13 : ℝ) * s ≠ 0 := mul_ne_zero (by norm_num) hsr
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, pow_zero, pow_one, inv_one, one_mul, mul_one] <;> push_cast
  · exact tendsto_const_nhds
  · simp only [zero_mul]
    exact tendsto_const_nhds
  · have key := (L0.neg).div (L3.mul Lp) h13
    rw [show -(10890 : ℝ) / (-13 * s) = (s : ℝ)⁻¹ * (10890 / 13) by field_simp] at key
    refine key.congr' ?_
    filter_upwards [hA3, hP, hN0] with N h3 hp hn
    simp only [Pi.div_apply]
    push_cast at hp ⊢
    field_simp
  · have key := Lp.inv₀ hsr
    refine key.congr' ?_
    filter_upwards [hP, hN0] with N hp hn
    push_cast at hp ⊢
    field_simp
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [hN0] with N hn
    rw [mul_one, mul_inv_cancel₀ hn]
  · have key := (L1.neg).div (L3.mul Lp) h13
    rw [show -(2305 : ℝ) / (-13 * s) = (s : ℝ)⁻¹ * (2305 / 13) by field_simp] at key
    refine key.congr' ?_
    filter_upwards [hA3, hP, hN0] with N h3 hp hn
    simp only [Pi.div_apply]
    push_cast at hp ⊢
    field_simp
  · simp only [mul_zero]
    exact tendsto_const_nhds
  · have key := Lp.inv₀ hsr
    refine key.congr' ?_
    filter_upwards [hP, hN0] with N hp hn
    push_cast at hp ⊢
    field_simp
  · have key := (tendsto_const_nhds (x := (1 : ℝ))).add ((L2.neg).div (L3.mul Lp) h13)
    rw [show (1 : ℝ) + -(42 : ℝ) / (-13 * s) = 1 + (s : ℝ)⁻¹ * (42 / 13) by
      field_simp] at key
    refine key.congr' ?_
    filter_upwards [hA3, hP, hN0] with N h3 hp hn
    simp only [Pi.div_apply]
    push_cast at hp ⊢
    field_simp

/-! ### Limits along the block step -/

def limFac (c : Coord) (up : Bool) : Matrix (Fin 3) (Fin 3) ℝ :=
  if isForward c up then Finf c else (Finf c)⁻¹

def limProd : List (Coord × Bool) → Matrix (Fin 3) (Fin 3) ℝ
  | [] => 1
  | (c, up) :: l => limFac c up * limProd l

theorem Finf_det (c : Coord) (hc : dAll c ≠ 0) : (Finf c).det ≠ 0 := by
  rw [Finf, rc_det, Finf_eq, Matrix.det_fin_three]
  refine Rat.cast_ne_zero.2 ?_
  revert hc c
  decide +kernel

theorem step_tendsto (e : Vertex) (c : Coord) (up : Bool) (hc : dAll c ≠ 0)
    (hg : ∀ᶠ N : ℕ in atTop, Good (aff e N) c up) :
    Tendsto (fun N : ℕ => conj N (stepMat (aff e N) c up)) atTop (𝓝 (limFac c up)) := by
  cases hf : isForward c up
  · have hf' : isForward c (!up) = true := by rw [isForward_not, hf]; rfl
    have hs : ∀ N, stepMat (aff e N) c up =
        (1 + (shiftParam (aff (move e c up) N) c)⁻¹ • Tw (aff (move e c up) N))⁻¹ := fun N => by
      simp only [stepMat, hf, Bool.false_eq_true, ↓reduceIte, move_aff]
    have hs2 : ∀ N, stepMat (aff (move e c up) N) c (!up) =
        1 + (shiftParam (aff (move e c up) N) c)⁻¹ • Tw (aff (move e c up) N) := fun N => by
      simp only [stepMat, hf', ↓reduceIte]
    have hT := factor_tendsto (move e c up) c hc (shiftParam (move e c up) c)
    simp only [← shiftParam_aff] at hT
    have hinv : Tendsto (fun N : ℕ => (conj N (1 + (shiftParam (aff (move e c up) N) c)⁻¹ •
        Tw (aff (move e c up) N)))⁻¹) atTop (𝓝 (Finf c)⁻¹) := by
      refine (continuousAt_matrix_inv (Finf c) ?_).tendsto.comp hT
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ (Finf_det c hc)
    simp only [limFac, hf, Bool.false_eq_true, ↓reduceIte]
    refine hinv.congr' ?_
    filter_upwards [hg, eventually_gt_atTop 0] with N hgN hN
    have hunit := (hgN.2.2.2 hf).2
    rw [move_aff, hs2 N] at hunit
    rw [hs N, conj_inv N hN.ne' _ hunit]
  · have hs : ∀ N, stepMat (aff e N) c up =
        1 + ((dAll c : ℚ) * N + shiftParam e c)⁻¹ • Tw (aff e N) := fun N => by
      simp only [stepMat, hf, ↓reduceIte, shiftParam_aff]
    simp only [limFac, hf, ↓reduceIte]
    exact (factor_tendsto e c hc (shiftParam e c)).congr fun N => by rw [hs N]

theorem walk_tendsto : ∀ (l : List (Coord × Bool)) (e : Vertex), (∀ x ∈ l, dAll x.1 ≠ 0) →
    (∀ᶠ N : ℕ in atTop, AllGood (aff e N) l) →
    Tendsto (fun N : ℕ => conj N (walk (aff e N) l)) atTop (𝓝 (limProd l))
  | [], e, _, _ => by
    simp only [walk, limProd]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [conj_one N hN.ne']
  | (c, up) :: l, e, hd, hg => by
    have h1 := step_tendsto e c up (hd (c, up) List.mem_cons_self) (hg.mono fun N h => h.1.1)
    have h2 := walk_tendsto l (move e c up) (fun x hx => hd x (List.mem_cons_of_mem _ hx))
      (hg.mono fun N h => by rw [← move_aff]; exact h.2)
    simp only [limProd]
    refine (h1.mul h2).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    simp only [walk, move_aff]
    rw [conj_mul N hN.ne']

theorem blk_dAll : ∀ x ∈ blk, dAll x.1 ≠ 0 := fun _x hx => (mem_block _ _ _ hx).1

theorem MN_tendsto : Tendsto (fun N : ℕ => conj N (MN N)) atTop (𝓝 (limProd blk)) := by
  have h := walk_tendsto blk w0 blk_dAll (by
    filter_upwards [eventually_ge_atTop 2] with N hN
    rw [← eN_eq_aff]
    exact allGood_blk N hN)
  exact h.congr fun N => by rw [MN, eN_eq_aff]

/-! ### Identification of the limit product with `A_∞` -/

theorem limProd_append : ∀ (l1 l2 : List (Coord × Bool)),
    limProd (l1 ++ l2) = limProd l1 * limProd l2
  | [], l2 => by simp only [List.nil_append, limProd, one_mul]
  | (c, up) :: l1, l2 => by
    simp only [List.cons_append, limProd]
    rw [limProd_append l1 l2, mul_assoc]

theorem limProd_replicate (c : Coord) (up : Bool) :
    ∀ n : ℕ, limProd (List.replicate n (c, up)) = limFac c up ^ n
  | 0 => by simp only [List.replicate_zero, limProd, pow_zero]
  | n + 1 => by
    rw [List.replicate_succ, limProd, limProd_replicate c up n, pow_succ']

theorem blk_eq : blk = List.replicate 10 (.inl 0, true) ++ List.replicate 9 (.inl 1, true) ++
    List.replicate 11 (.inl 2, true) ++ List.replicate 11 (.inl 3, false) ++
    List.replicate 2 (.inr 0, true) ++ List.replicate 1 (.inr 1, true) ++
    List.replicate 3 (.inr 2, true) := by
  decide +kernel

theorem F_x0 : limFac (.inl 0) true = rc (1 + (10 : ℚ)⁻¹ • Tinf) := by
  change Finf (.inl 0) = _
  rw [Finf, dAll_x0]
  push_cast
  rfl

theorem F_x1 : limFac (.inl 1) true = rc (1 + (9 : ℚ)⁻¹ • Tinf) := by
  change Finf (.inl 1) = _
  rw [Finf, dAll_x1]
  push_cast
  rfl

theorem F_x2 : limFac (.inl 2) true = rc (1 + (11 : ℚ)⁻¹ • Tinf) := by
  change Finf (.inl 2) = _
  rw [Finf, dAll_x2]
  push_cast
  rfl

theorem unit_of_dAll (c : Coord) (hc : dAll c ≠ 0) : IsUnit (1 + (dAll c : ℚ)⁻¹ • Tinf).det := by
  have := Finf_det c hc
  rw [Finf, rc_det] at this
  exact isUnit_iff_ne_zero.2 (Rat.cast_ne_zero.1 this)

theorem F_x3 : limFac (.inl 3) false = rc (1 - (11 : ℚ)⁻¹ • Tinf)⁻¹ := by
  change (Finf (.inl 3))⁻¹ = _
  rw [Finf, ← rc_inv _ (unit_of_dAll _ (by decide)), dAll_x3]
  push_cast
  rw [inv_neg, neg_smul, ← sub_eq_add_neg]

theorem F_y0 : limFac (.inr 0) true = rc (1 + (2 : ℚ)⁻¹ • Tinf)⁻¹ := by
  change (Finf (.inr 0))⁻¹ = _
  rw [Finf, ← rc_inv _ (unit_of_dAll _ (by decide)), dAll_y0]
  push_cast
  rfl

theorem F_y1 : limFac (.inr 1) true = rc (1 + Tinf)⁻¹ := by
  change (Finf (.inr 1))⁻¹ = _
  rw [Finf, ← rc_inv _ (unit_of_dAll _ (by decide)), dAll_y1]
  push_cast
  rw [inv_one, one_smul]

theorem F_y2 : limFac (.inr 2) true = rc (1 + (3 : ℚ)⁻¹ • Tinf)⁻¹ := by
  change (Finf (.inr 2))⁻¹ = _
  rw [Finf, ← rc_inv _ (unit_of_dAll _ (by decide)), dAll_y2]
  push_cast
  rfl

theorem limProd_blk : limProd blk = rc Ainf := by
  rw [blk_eq, limProd_append, limProd_append, limProd_append, limProd_append, limProd_append,
    limProd_append, limProd_replicate, limProd_replicate, limProd_replicate, limProd_replicate,
    limProd_replicate, limProd_replicate, limProd_replicate, F_x0, F_x1, F_x2, F_x3, F_y0, F_y1,
    F_y2, Ainf]
  simp only [map_mul, map_pow, pow_one]

/-! ### The scaled transfer matrices and the observability determinant -/

def A (N : ℕ) : Matrix (Fin 3) (Fin 3) ℝ := dg N * rc (MN N) * sg (N + 1)

theorem dg_sg_succ_tendsto : Tendsto (fun N : ℕ => dg N * sg (N + 1)) atTop (𝓝 1) := by
  refine tendsto_matrix fun i j => ?_
  simp only [dg, sg, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs with h
  · have := (tendsto_natCast_div_add_atTop (1 : ℝ)).pow (i : ℕ)
    simp only [one_pow] at this
    refine this.congr fun N => ?_
    push_cast
    rw [div_pow, div_eq_mul_inv]
  · exact tendsto_const_nhds

theorem A_tendsto : Tendsto A atTop (𝓝 (rc Ainf)) := by
  have h := MN_tendsto.mul dg_sg_succ_tendsto
  rw [limProd_blk, mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  simp only [A, conj]
  rw [show dg N * rc (MN N) * sg N * (dg N * sg (N + 1)) =
    dg N * rc (MN N) * (sg N * dg N) * sg (N + 1) by simp only [mul_assoc], sg_dg N hN.ne',
    mul_one]

def obsR (X Y : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => (![(1 : Matrix (Fin 3) (Fin 3) ℝ), X, X * Y] j) i 0

def obsQ (N : ℕ) : Matrix (Fin 3) (Fin 3) ℚ :=
  Matrix.of fun i j => (![(1 : Matrix (Fin 3) (Fin 3) ℚ), MN N, MN N * MN (N + 1)] j) i 0

theorem obsR_tendsto :
    Tendsto (fun N => obsR (A N) (A (N + 1))) atTop (𝓝 (obsR (rc Ainf) (rc Ainf))) := by
  have hA := A_tendsto
  have hA' : Tendsto (fun N => A (N + 1)) atTop (𝓝 (rc Ainf)) :=
    hA.comp (tendsto_add_atTop_nat 1)
  have hAA := hA.mul hA'
  refine tendsto_matrix fun i j => ?_
  fin_cases j
  · simp only [obsR, Matrix.of_apply, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    exact tendsto_const_nhds
  · simp only [obsR, Matrix.of_apply, Fin.mk_one, Fin.isValue, Matrix.cons_val_one]
    exact tendsto_matrix_elem hA i 0
  · simp only [obsR, Matrix.of_apply, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    exact tendsto_matrix_elem hAA i 0

theorem obsR_limit_det : (obsR (rc Ainf) (rc Ainf)).det ≠ 0 := by
  have h : obsR (rc Ainf) (rc Ainf) = rc (Matrix.of fun i j : Fin 3 => (Ainf ^ (j : ℕ)) i 0) := by
    ext i j
    rw [rc_apply, Matrix.of_apply, ← rc_apply, obsR, Matrix.of_apply]
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, pow_zero, map_one]
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, pow_one]
    · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons, pow_two, map_mul]
  rw [h, rc_det, obs_det]
  exact Rat.cast_ne_zero.2 (by norm_num)

theorem obsR_det_eventually : ∀ᶠ N : ℕ in atTop, (obsR (A N) (A (N + 1))).det ≠ 0 := by
  have hc : Tendsto (fun M : Matrix (Fin 3) (Fin 3) ℝ => M.det) (𝓝 (obsR (rc Ainf) (rc Ainf)))
      (𝓝 (obsR (rc Ainf) (rc Ainf)).det) := continuous_id.matrix_det.tendsto _
  exact (hc.comp obsR_tendsto).eventually_ne obsR_limit_det

theorem obsR_eq (N : ℕ) : obsR (A N) (A (N + 1)) = dg N * rc (obsQ N) := by
  have hA1 : A N * A (N + 1) = dg N * rc (MN N * MN (N + 1)) * sg (N + 1 + 1) := by
    simp only [A, map_mul]
    rw [show dg N * rc (MN N) * sg (N + 1) * (dg (N + 1) * rc (MN (N + 1)) * sg (N + 1 + 1)) =
      dg N * rc (MN N) * (sg (N + 1) * dg (N + 1)) * rc (MN (N + 1)) * sg (N + 1 + 1) by
        simp only [mul_assoc], sg_dg (N + 1) (Nat.succ_ne_zero N), mul_one]
    simp only [mul_assoc]
  ext i j
  rw [obsR, obsQ, Matrix.of_apply, dg, Matrix.diagonal_mul, rc_apply, Matrix.of_apply]
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Matrix.one_apply]
    split_ifs with h
    · subst h
      simp only [Fin.val_zero, pow_zero, Rat.cast_one, mul_one]
    · simp only [Rat.cast_zero, mul_zero]
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [A, sg, Matrix.mul_diagonal, dg, Matrix.diagonal_mul, rc_apply, Fin.val_zero, pow_zero,
      inv_one, mul_one]
  · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    rw [hA1, sg, Matrix.mul_diagonal, dg, Matrix.diagonal_mul, rc_apply, Fin.val_zero, pow_zero,
      inv_one, mul_one]

theorem obsQ_det_eventually : ∀ᶠ N : ℕ in atTop, (obsQ N).det ≠ 0 := by
  filter_upwards [obsR_det_eventually] with N h
  rw [obsR_eq N, Matrix.det_mul, rc_det] at h
  intro h0
  apply h
  rw [h0, Rat.cast_zero, mul_zero]

/-! ### The bounded-gap statement -/

theorem row_apply (a : ℤ) (b : ℕ) (M : Matrix (Fin 3) (Fin 3) ℚ) :
    (((b : ℚ) • Rmat 0 - (a : ℚ) • Rmat 1) ᵥ* M) 0 =
      (b : ℚ) * (Rmat * M) 0 0 - a * (Rmat * M) 1 0 := by
  simp only [Matrix.vecMul, dotProduct, Matrix.mul_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, Fin.sum_univ_three]
  ring

theorem bounded_gap :
    ∀ᶠ N : ℕ in atTop, ∀ (a : ℤ) (b : ℕ), 0 < b →
      ∃ i : Fin 3, (b : ℚ) * Pread (N + i) 0 - a * Qread (N + i) 0 ≠ 0 := by
  filter_upwards [obsQ_det_eventually, eventually_ge_atTop 2] with N hdet hN a b hb
  by_contra hcon
  push Not at hcon
  obtain ⟨u, hu⟩ : ∃ u : Fin 3 → ℚ, u = (b : ℚ) • Rmat 0 - (a : ℚ) • Rmat 1 := ⟨_, rfl⟩
  have hW : ∀ i : Fin 3, (u ᵥ* W (N + i)) 0 = 0 := fun i => by
    rw [hu, row_apply]
    exact hcon i
  have h0 : (u ᵥ* W N) 0 = 0 := by simpa using hW 0
  have h1 : ((u ᵥ* W N) ᵥ* MN N) 0 = 0 := by
    rw [Matrix.vecMul_vecMul, ← W_succ N hN]
    simpa using hW 1
  have h2 : ((u ᵥ* W N) ᵥ* (MN N * MN (N + 1))) 0 = 0 := by
    rw [Matrix.vecMul_vecMul, ← mul_assoc, ← W_succ N hN, ← W_succ (N + 1) (by omega)]
    simpa using hW 2
  have hv : (u ᵥ* W N) ᵥ* obsQ N = 0 := by
    funext j
    have hj : ((u ᵥ* W N) ᵥ* obsQ N) j =
        ((u ᵥ* W N) ᵥ* (![(1 : Matrix (Fin 3) (Fin 3) ℚ), MN N, MN N * MN (N + 1)] j)) 0 := rfl
    rw [hj, Pi.zero_apply]
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Matrix.vecMul_one]
      exact h0
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one]
      exact h1
    · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons]
      exact h2
  have hv0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hv
  have hu0 := Matrix.eq_zero_of_vecMul_eq_zero (det_W N).ne_zero hv0
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  have h1 : u 1 = b * 2 := by
    rw [hu]
    simp [Rmat]
  rw [hu0, Pi.zero_apply] at h1
  linarith

end Zeta2BoundedGap
