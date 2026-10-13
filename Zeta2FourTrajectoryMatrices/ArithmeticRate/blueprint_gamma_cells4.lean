import Zeta2FourTrajectoryMatrices.ArithmeticRate.blueprint_gamma_core

open Zeta2Blueprint Zeta2GammaCore

noncomputable section

namespace Zeta2GammaCells

theorem cell_36 (x : ℝ) (hx1 : ((8 / 21 : ℚ) : ℝ) < x) (hx2 : x < ((5 / 13 : ℚ) : ℝ)) :
    phi x = 0 := by
  have f11 := floor_bounds 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have f10 := floor_bounds 10 3 _ _ x hx1 hx2 (by decide +kernel)
  have f9 := floor_bounds 9 3 _ _ x hx1 hx2 (by decide +kernel)
  have f8 := floor_bounds 8 3 _ _ x hx1 hx2 (by decide +kernel)
  have f2 := floor_bounds 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have f1 := floor_bounds 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f3 := floor_bounds 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have D := rho_decomp x 4 3 3 3 0 0 1 f11 f10 f9 f8 f2 f1 f3
  have hs0 := s_nonneg 4 x f11
  have hs1 := s_lt_one 4 x f11
  have f_s_t1 : A (-11) (-4 - 1) x < A 1 0 x :=
    A_lt (-11) (-4 - 1) 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_s : A 10 3 x < A (-11) (-4 - 1) x :=
    A_lt 10 3 (-11) (-4 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t11 : A (-11) (-4 - 1) x < A 11 4 x :=
    A_lt (-11) (-4 - 1) 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t2 : A (-11) (-4 - 1) x < A 2 0 x :=
    A_lt (-11) (-4 - 1) 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t3 : A (-11) (-4 - 1) x < A 3 1 x :=
    A_lt (-11) (-4 - 1) 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t9 : A (-11) (-4 - 1) x < A 9 3 x :=
    A_lt (-11) (-4 - 1) 9 3 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t1 : A 10 3 x < A 1 0 x :=
    A_lt 10 3 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t11 : A 1 0 x < A 11 4 x :=
    A_lt 1 0 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t1 : A 2 0 x < A 1 0 x :=
    A_lt 2 0 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t3 : A 1 0 x < A 3 1 x :=
    A_lt 1 0 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t1 : A 9 3 x < A 1 0 x :=
    A_lt 9 3 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t11 : A 10 3 x < A 11 4 x :=
    A_lt 10 3 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t2 : A 10 3 x < A 2 0 x :=
    A_lt 10 3 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t3 : A 10 3 x < A 3 1 x :=
    A_lt 10 3 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t9 : A 10 3 x < A 9 3 x :=
    A_lt 10 3 9 3 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t11 : A 2 0 x < A 11 4 x :=
    A_lt 2 0 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t3 : A 11 4 x < A 3 1 x :=
    A_lt 11 4 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t11 : A 9 3 x < A 11 4 x :=
    A_lt 9 3 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t3 : A 2 0 x < A 3 1 x :=
    A_lt 2 0 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t9 : A 2 0 x < A 9 3 x :=
    A_lt 2 0 9 3 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t3 : A 9 3 x < A 3 1 x :=
    A_lt 9 3 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have z_t10 : 0 < A 10 3 x :=
    A_pos 10 3 _ _ x hx1 hx2 (by decide +kernel)
  have o_t10 : A 10 3 x < 1 :=
    A_lt_one 10 3 _ _ x hx1 hx2 (by decide +kernel)
  have z_t9 : 0 < A 9 3 x :=
    A_pos 9 3 _ _ x hx1 hx2 (by decide +kernel)
  have o_t9 : A 9 3 x < 1 :=
    A_lt_one 9 3 _ _ x hx1 hx2 (by decide +kernel)
  have z_t11 : 0 < A 11 4 x :=
    A_pos 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have o_t11 : A 11 4 x < 1 :=
    A_lt_one 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have z_t2 : 0 < A 2 0 x :=
    A_pos 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t2 : A 2 0 x < 1 :=
    A_lt_one 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t1 : 0 < A 1 0 x :=
    A_pos 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t1 : A 1 0 x < 1 :=
    A_lt_one 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t3 : 0 < A 3 1 x :=
    A_pos 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have o_t3 : A 3 1 x < 1 :=
    A_lt_one 3 1 _ _ x hx1 hx2 (by decide +kernel)
  refine phi_eq x 0 ?_ ?_
  · intro y _ _
    exact rho_nonneg x y
  · refine ⟨0, le_rfl, zero_lt_one, ?_⟩
    rw [D 0 le_rfl zero_lt_one]
    simp only [Ival, not_lt.2 hs0, not_le.2 z_t10, not_le.2 z_t9, not_le.2 z_t11,
        not_le.2 z_t2, not_le.2 z_t1, not_le.2 z_t3]
    decide

theorem cell_37 (x : ℝ) (hx1 : ((5 / 13 : ℚ) : ℝ) < x) (hx2 : x < ((2 / 5 : ℚ) : ℝ)) :
    phi x = 0 := by
  have f11 := floor_bounds 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have f10 := floor_bounds 10 3 _ _ x hx1 hx2 (by decide +kernel)
  have f9 := floor_bounds 9 3 _ _ x hx1 hx2 (by decide +kernel)
  have f8 := floor_bounds 8 3 _ _ x hx1 hx2 (by decide +kernel)
  have f2 := floor_bounds 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have f1 := floor_bounds 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f3 := floor_bounds 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have D := rho_decomp x 4 3 3 3 0 0 1 f11 f10 f9 f8 f2 f1 f3
  have hs0 := s_nonneg 4 x f11
  have hs1 := s_lt_one 4 x f11
  have f_s_t1 : A (-11) (-4 - 1) x < A 1 0 x :=
    A_lt (-11) (-4 - 1) 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_s : A 10 3 x < A (-11) (-4 - 1) x :=
    A_lt 10 3 (-11) (-4 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t11 : A (-11) (-4 - 1) x < A 11 4 x :=
    A_lt (-11) (-4 - 1) 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_s : A 2 0 x < A (-11) (-4 - 1) x :=
    A_lt 2 0 (-11) (-4 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t3 : A (-11) (-4 - 1) x < A 3 1 x :=
    A_lt (-11) (-4 - 1) 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t9 : A (-11) (-4 - 1) x < A 9 3 x :=
    A_lt (-11) (-4 - 1) 9 3 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t1 : A 10 3 x < A 1 0 x :=
    A_lt 10 3 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t11 : A 1 0 x < A 11 4 x :=
    A_lt 1 0 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t1 : A 2 0 x < A 1 0 x :=
    A_lt 2 0 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t3 : A 1 0 x < A 3 1 x :=
    A_lt 1 0 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t1 : A 9 3 x < A 1 0 x :=
    A_lt 9 3 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t11 : A 10 3 x < A 11 4 x :=
    A_lt 10 3 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t2 : A 10 3 x < A 2 0 x :=
    A_lt 10 3 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t3 : A 10 3 x < A 3 1 x :=
    A_lt 10 3 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t9 : A 10 3 x < A 9 3 x :=
    A_lt 10 3 9 3 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t11 : A 2 0 x < A 11 4 x :=
    A_lt 2 0 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t3 : A 11 4 x < A 3 1 x :=
    A_lt 11 4 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t11 : A 9 3 x < A 11 4 x :=
    A_lt 9 3 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t3 : A 2 0 x < A 3 1 x :=
    A_lt 2 0 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t9 : A 2 0 x < A 9 3 x :=
    A_lt 2 0 9 3 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t3 : A 9 3 x < A 3 1 x :=
    A_lt 9 3 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have z_t10 : 0 < A 10 3 x :=
    A_pos 10 3 _ _ x hx1 hx2 (by decide +kernel)
  have o_t10 : A 10 3 x < 1 :=
    A_lt_one 10 3 _ _ x hx1 hx2 (by decide +kernel)
  have z_t9 : 0 < A 9 3 x :=
    A_pos 9 3 _ _ x hx1 hx2 (by decide +kernel)
  have o_t9 : A 9 3 x < 1 :=
    A_lt_one 9 3 _ _ x hx1 hx2 (by decide +kernel)
  have z_t11 : 0 < A 11 4 x :=
    A_pos 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have o_t11 : A 11 4 x < 1 :=
    A_lt_one 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have z_t2 : 0 < A 2 0 x :=
    A_pos 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t2 : A 2 0 x < 1 :=
    A_lt_one 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t1 : 0 < A 1 0 x :=
    A_pos 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t1 : A 1 0 x < 1 :=
    A_lt_one 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t3 : 0 < A 3 1 x :=
    A_pos 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have o_t3 : A 3 1 x < 1 :=
    A_lt_one 3 1 _ _ x hx1 hx2 (by decide +kernel)
  refine phi_eq x 0 ?_ ?_
  · intro y _ _
    exact rho_nonneg x y
  · refine ⟨0, le_rfl, zero_lt_one, ?_⟩
    rw [D 0 le_rfl zero_lt_one]
    simp only [Ival, not_lt.2 hs0, not_le.2 z_t10, not_le.2 z_t9, not_le.2 z_t11,
        not_le.2 z_t2, not_le.2 z_t1, not_le.2 z_t3]
    decide

theorem cell_38 (x : ℝ) (hx1 : ((2 / 5 : ℚ) : ℝ) < x) (hx2 : x < ((9 / 22 : ℚ) : ℝ)) :
    phi x = 0 := by
  have f11 := floor_bounds 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have f10 := floor_bounds 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f9 := floor_bounds 9 3 _ _ x hx1 hx2 (by decide +kernel)
  have f8 := floor_bounds 8 3 _ _ x hx1 hx2 (by decide +kernel)
  have f2 := floor_bounds 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have f1 := floor_bounds 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f3 := floor_bounds 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have D := rho_decomp x 4 4 3 3 0 0 1 f11 f10 f9 f8 f2 f1 f3
  have hs0 := s_nonneg 4 x f11
  have hs1 := s_lt_one 4 x f11
  have f_s_t1 : A (-11) (-4 - 1) x < A 1 0 x :=
    A_lt (-11) (-4 - 1) 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t10 : A (-11) (-4 - 1) x < A 10 4 x :=
    A_lt (-11) (-4 - 1) 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t11 : A (-11) (-4 - 1) x < A 11 4 x :=
    A_lt (-11) (-4 - 1) 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_s : A 2 0 x < A (-11) (-4 - 1) x :=
    A_lt 2 0 (-11) (-4 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t3 : A (-11) (-4 - 1) x < A 3 1 x :=
    A_lt (-11) (-4 - 1) 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_s : A 9 3 x < A (-11) (-4 - 1) x :=
    A_lt 9 3 (-11) (-4 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t10 : A 1 0 x < A 10 4 x :=
    A_lt 1 0 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t1 : A 11 4 x < A 1 0 x :=
    A_lt 11 4 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t1 : A 2 0 x < A 1 0 x :=
    A_lt 2 0 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t3 : A 1 0 x < A 3 1 x :=
    A_lt 1 0 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t1 : A 9 3 x < A 1 0 x :=
    A_lt 9 3 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t10 : A 11 4 x < A 10 4 x :=
    A_lt 11 4 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t10 : A 2 0 x < A 10 4 x :=
    A_lt 2 0 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_t10 : A 3 1 x < A 10 4 x :=
    A_lt 3 1 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t10 : A 9 3 x < A 10 4 x :=
    A_lt 9 3 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t11 : A 2 0 x < A 11 4 x :=
    A_lt 2 0 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t3 : A 11 4 x < A 3 1 x :=
    A_lt 11 4 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t11 : A 9 3 x < A 11 4 x :=
    A_lt 9 3 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t3 : A 2 0 x < A 3 1 x :=
    A_lt 2 0 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t9 : A 2 0 x < A 9 3 x :=
    A_lt 2 0 9 3 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t3 : A 9 3 x < A 3 1 x :=
    A_lt 9 3 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have z_t10 : 0 < A 10 4 x :=
    A_pos 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have o_t10 : A 10 4 x < 1 :=
    A_lt_one 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have z_t9 : 0 < A 9 3 x :=
    A_pos 9 3 _ _ x hx1 hx2 (by decide +kernel)
  have o_t9 : A 9 3 x < 1 :=
    A_lt_one 9 3 _ _ x hx1 hx2 (by decide +kernel)
  have z_t11 : 0 < A 11 4 x :=
    A_pos 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have o_t11 : A 11 4 x < 1 :=
    A_lt_one 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have z_t2 : 0 < A 2 0 x :=
    A_pos 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t2 : A 2 0 x < 1 :=
    A_lt_one 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t1 : 0 < A 1 0 x :=
    A_pos 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t1 : A 1 0 x < 1 :=
    A_lt_one 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t3 : 0 < A 3 1 x :=
    A_pos 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have o_t3 : A 3 1 x < 1 :=
    A_lt_one 3 1 _ _ x hx1 hx2 (by decide +kernel)
  refine phi_eq x 0 ?_ ?_
  · intro y _ _
    exact rho_nonneg x y
  · refine ⟨A 2 0 x, z_t2.le, o_t2, ?_⟩
    rw [D _ z_t2.le o_t2]
    simp only [Ival, not_lt.2 (f_t2_s).le, not_le.2 f_t2_t10, not_le.2 f_t2_t9,
        not_le.2 f_t2_t11, not_le.2 f_t2_t1, not_le.2 f_t2_t3, le_refl]
    decide

theorem cell_39 (x : ℝ) (hx1 : ((9 / 22 : ℚ) : ℝ) < x) (hx2 : x < ((5 / 12 : ℚ) : ℝ)) :
    phi x = 0 := by
  have f11 := floor_bounds 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have f10 := floor_bounds 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f9 := floor_bounds 9 3 _ _ x hx1 hx2 (by decide +kernel)
  have f8 := floor_bounds 8 3 _ _ x hx1 hx2 (by decide +kernel)
  have f2 := floor_bounds 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have f1 := floor_bounds 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f3 := floor_bounds 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have D := rho_decomp x 4 4 3 3 0 0 1 f11 f10 f9 f8 f2 f1 f3
  have hs0 := s_nonneg 4 x f11
  have hs1 := s_lt_one 4 x f11
  have f_s_t1 : A (-11) (-4 - 1) x < A 1 0 x :=
    A_lt (-11) (-4 - 1) 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t10 : A (-11) (-4 - 1) x < A 10 4 x :=
    A_lt (-11) (-4 - 1) 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_s : A 11 4 x < A (-11) (-4 - 1) x :=
    A_lt 11 4 (-11) (-4 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_s : A 2 0 x < A (-11) (-4 - 1) x :=
    A_lt 2 0 (-11) (-4 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t3 : A (-11) (-4 - 1) x < A 3 1 x :=
    A_lt (-11) (-4 - 1) 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_s : A 9 3 x < A (-11) (-4 - 1) x :=
    A_lt 9 3 (-11) (-4 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t10 : A 1 0 x < A 10 4 x :=
    A_lt 1 0 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t1 : A 11 4 x < A 1 0 x :=
    A_lt 11 4 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t1 : A 2 0 x < A 1 0 x :=
    A_lt 2 0 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t3 : A 1 0 x < A 3 1 x :=
    A_lt 1 0 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t1 : A 9 3 x < A 1 0 x :=
    A_lt 9 3 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t10 : A 11 4 x < A 10 4 x :=
    A_lt 11 4 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t10 : A 2 0 x < A 10 4 x :=
    A_lt 2 0 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_t10 : A 3 1 x < A 10 4 x :=
    A_lt 3 1 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t10 : A 9 3 x < A 10 4 x :=
    A_lt 9 3 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t11 : A 2 0 x < A 11 4 x :=
    A_lt 2 0 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t3 : A 11 4 x < A 3 1 x :=
    A_lt 11 4 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t11 : A 9 3 x < A 11 4 x :=
    A_lt 9 3 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t3 : A 2 0 x < A 3 1 x :=
    A_lt 2 0 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t9 : A 2 0 x < A 9 3 x :=
    A_lt 2 0 9 3 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t3 : A 9 3 x < A 3 1 x :=
    A_lt 9 3 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have z_t10 : 0 < A 10 4 x :=
    A_pos 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have o_t10 : A 10 4 x < 1 :=
    A_lt_one 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have z_t9 : 0 < A 9 3 x :=
    A_pos 9 3 _ _ x hx1 hx2 (by decide +kernel)
  have o_t9 : A 9 3 x < 1 :=
    A_lt_one 9 3 _ _ x hx1 hx2 (by decide +kernel)
  have z_t11 : 0 < A 11 4 x :=
    A_pos 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have o_t11 : A 11 4 x < 1 :=
    A_lt_one 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have z_t2 : 0 < A 2 0 x :=
    A_pos 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t2 : A 2 0 x < 1 :=
    A_lt_one 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t1 : 0 < A 1 0 x :=
    A_pos 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t1 : A 1 0 x < 1 :=
    A_lt_one 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t3 : 0 < A 3 1 x :=
    A_pos 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have o_t3 : A 3 1 x < 1 :=
    A_lt_one 3 1 _ _ x hx1 hx2 (by decide +kernel)
  refine phi_eq x 0 ?_ ?_
  · intro y _ _
    exact rho_nonneg x y
  · refine ⟨A 2 0 x, z_t2.le, o_t2, ?_⟩
    rw [D _ z_t2.le o_t2]
    simp only [Ival, not_lt.2 (f_t2_s).le, not_le.2 f_t2_t10, not_le.2 f_t2_t9,
        not_le.2 f_t2_t11, not_le.2 f_t2_t1, not_le.2 f_t2_t3, le_refl]
    decide

theorem cell_40 (x : ℝ) (hx1 : ((5 / 12 : ℚ) : ℝ) < x) (hx2 : x < ((3 / 7 : ℚ) : ℝ)) :
    phi x = 0 := by
  have f11 := floor_bounds 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have f10 := floor_bounds 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f9 := floor_bounds 9 3 _ _ x hx1 hx2 (by decide +kernel)
  have f8 := floor_bounds 8 3 _ _ x hx1 hx2 (by decide +kernel)
  have f2 := floor_bounds 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have f1 := floor_bounds 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f3 := floor_bounds 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have D := rho_decomp x 4 4 3 3 0 0 1 f11 f10 f9 f8 f2 f1 f3
  have hs0 := s_nonneg 4 x f11
  have hs1 := s_lt_one 4 x f11
  have f_t1_s : A 1 0 x < A (-11) (-4 - 1) x :=
    A_lt 1 0 (-11) (-4 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t10 : A (-11) (-4 - 1) x < A 10 4 x :=
    A_lt (-11) (-4 - 1) 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_s : A 11 4 x < A (-11) (-4 - 1) x :=
    A_lt 11 4 (-11) (-4 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_s : A 2 0 x < A (-11) (-4 - 1) x :=
    A_lt 2 0 (-11) (-4 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t3 : A (-11) (-4 - 1) x < A 3 1 x :=
    A_lt (-11) (-4 - 1) 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_s : A 9 3 x < A (-11) (-4 - 1) x :=
    A_lt 9 3 (-11) (-4 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t10 : A 1 0 x < A 10 4 x :=
    A_lt 1 0 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t1 : A 11 4 x < A 1 0 x :=
    A_lt 11 4 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t1 : A 2 0 x < A 1 0 x :=
    A_lt 2 0 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t3 : A 1 0 x < A 3 1 x :=
    A_lt 1 0 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t1 : A 9 3 x < A 1 0 x :=
    A_lt 9 3 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t10 : A 11 4 x < A 10 4 x :=
    A_lt 11 4 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t10 : A 2 0 x < A 10 4 x :=
    A_lt 2 0 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_t10 : A 3 1 x < A 10 4 x :=
    A_lt 3 1 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t10 : A 9 3 x < A 10 4 x :=
    A_lt 9 3 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t11 : A 2 0 x < A 11 4 x :=
    A_lt 2 0 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t3 : A 11 4 x < A 3 1 x :=
    A_lt 11 4 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t11 : A 9 3 x < A 11 4 x :=
    A_lt 9 3 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t3 : A 2 0 x < A 3 1 x :=
    A_lt 2 0 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t9 : A 2 0 x < A 9 3 x :=
    A_lt 2 0 9 3 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t3 : A 9 3 x < A 3 1 x :=
    A_lt 9 3 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have z_t10 : 0 < A 10 4 x :=
    A_pos 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have o_t10 : A 10 4 x < 1 :=
    A_lt_one 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have z_t9 : 0 < A 9 3 x :=
    A_pos 9 3 _ _ x hx1 hx2 (by decide +kernel)
  have o_t9 : A 9 3 x < 1 :=
    A_lt_one 9 3 _ _ x hx1 hx2 (by decide +kernel)
  have z_t11 : 0 < A 11 4 x :=
    A_pos 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have o_t11 : A 11 4 x < 1 :=
    A_lt_one 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have z_t2 : 0 < A 2 0 x :=
    A_pos 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t2 : A 2 0 x < 1 :=
    A_lt_one 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t1 : 0 < A 1 0 x :=
    A_pos 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t1 : A 1 0 x < 1 :=
    A_lt_one 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t3 : 0 < A 3 1 x :=
    A_pos 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have o_t3 : A 3 1 x < 1 :=
    A_lt_one 3 1 _ _ x hx1 hx2 (by decide +kernel)
  refine phi_eq x 0 ?_ ?_
  · intro y _ _
    exact rho_nonneg x y
  · refine ⟨A 2 0 x, z_t2.le, o_t2, ?_⟩
    rw [D _ z_t2.le o_t2]
    simp only [Ival, not_lt.2 (f_t2_s).le, not_le.2 f_t2_t10, not_le.2 f_t2_t9,
        not_le.2 f_t2_t11, not_le.2 f_t2_t1, not_le.2 f_t2_t3, le_refl]
    decide

theorem cell_41 (x : ℝ) (hx1 : ((3 / 7 : ℚ) : ℝ) < x) (hx2 : x < ((4 / 9 : ℚ) : ℝ)) :
    phi x = 1 := by
  have f11 := floor_bounds 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have f10 := floor_bounds 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f9 := floor_bounds 9 3 _ _ x hx1 hx2 (by decide +kernel)
  have f8 := floor_bounds 8 3 _ _ x hx1 hx2 (by decide +kernel)
  have f2 := floor_bounds 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have f1 := floor_bounds 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f3 := floor_bounds 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have D := rho_decomp x 4 4 3 3 0 0 1 f11 f10 f9 f8 f2 f1 f3
  have hs0 := s_nonneg 4 x f11
  have hs1 := s_lt_one 4 x f11
  have f_t1_s : A 1 0 x < A (-11) (-4 - 1) x :=
    A_lt 1 0 (-11) (-4 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_s : A 10 4 x < A (-11) (-4 - 1) x :=
    A_lt 10 4 (-11) (-4 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_s : A 11 4 x < A (-11) (-4 - 1) x :=
    A_lt 11 4 (-11) (-4 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_s : A 2 0 x < A (-11) (-4 - 1) x :=
    A_lt 2 0 (-11) (-4 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_s : A 3 1 x < A (-11) (-4 - 1) x :=
    A_lt 3 1 (-11) (-4 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_s : A 9 3 x < A (-11) (-4 - 1) x :=
    A_lt 9 3 (-11) (-4 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t10 : A 1 0 x < A 10 4 x :=
    A_lt 1 0 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t1 : A 11 4 x < A 1 0 x :=
    A_lt 11 4 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t1 : A 2 0 x < A 1 0 x :=
    A_lt 2 0 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t3 : A 1 0 x < A 3 1 x :=
    A_lt 1 0 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t1 : A 9 3 x < A 1 0 x :=
    A_lt 9 3 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t10 : A 11 4 x < A 10 4 x :=
    A_lt 11 4 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t10 : A 2 0 x < A 10 4 x :=
    A_lt 2 0 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t3 : A 10 4 x < A 3 1 x :=
    A_lt 10 4 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t10 : A 9 3 x < A 10 4 x :=
    A_lt 9 3 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t11 : A 2 0 x < A 11 4 x :=
    A_lt 2 0 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t3 : A 11 4 x < A 3 1 x :=
    A_lt 11 4 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t11 : A 9 3 x < A 11 4 x :=
    A_lt 9 3 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t3 : A 2 0 x < A 3 1 x :=
    A_lt 2 0 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t2 : A 9 3 x < A 2 0 x :=
    A_lt 9 3 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t3 : A 9 3 x < A 3 1 x :=
    A_lt 9 3 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have z_t10 : 0 < A 10 4 x :=
    A_pos 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have o_t10 : A 10 4 x < 1 :=
    A_lt_one 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have z_t9 : 0 < A 9 3 x :=
    A_pos 9 3 _ _ x hx1 hx2 (by decide +kernel)
  have o_t9 : A 9 3 x < 1 :=
    A_lt_one 9 3 _ _ x hx1 hx2 (by decide +kernel)
  have z_t11 : 0 < A 11 4 x :=
    A_pos 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have o_t11 : A 11 4 x < 1 :=
    A_lt_one 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have z_t2 : 0 < A 2 0 x :=
    A_pos 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t2 : A 2 0 x < 1 :=
    A_lt_one 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t1 : 0 < A 1 0 x :=
    A_pos 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t1 : A 1 0 x < 1 :=
    A_lt_one 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t3 : 0 < A 3 1 x :=
    A_pos 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have o_t3 : A 3 1 x < 1 :=
    A_lt_one 3 1 _ _ x hx1 hx2 (by decide +kernel)
  refine phi_eq x 1 ?_ ?_
  · intro y hy0 hy1
    rw [D y hy0 hy1]
    have := Ival_ge x 4 4 3 0 0 1 (1 - (1)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ y hy0
      hy1
    · omega
    · simp only [Ival, not_lt.2 hs0, not_le.2 z_t10, not_le.2 z_t9, not_le.2 z_t11,
        not_le.2 z_t2, not_le.2 z_t1, not_le.2 z_t3]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t10_s).le, (f_t9_t10).le, (f_t11_t10).le, (f_t2_t10).le,
        (f_t1_t10).le, not_le.2 f_t10_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t9_s).le, not_le.2 f_t9_t10, not_le.2 f_t9_t11,
        not_le.2 f_t9_t2, not_le.2 f_t9_t1, not_le.2 f_t9_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t11_s).le, not_le.2 f_t11_t10, (f_t9_t11).le, (f_t2_t11).le,
        not_le.2 f_t11_t1, not_le.2 f_t11_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t2_s).le, not_le.2 f_t2_t10, (f_t9_t2).le, not_le.2 f_t2_t11,
        not_le.2 f_t2_t1, not_le.2 f_t2_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t1_s).le, not_le.2 f_t1_t10, (f_t9_t1).le, (f_t11_t1).le,
        (f_t2_t1).le, not_le.2 f_t1_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t3_s).le, (f_t10_t3).le, (f_t9_t3).le, (f_t11_t3).le,
        (f_t2_t3).le, (f_t1_t3).le, le_refl]
      decide
    · simp only [Ip, (f_t10_s).le, (f_t9_s).le, (f_t11_s).le, (f_t2_s).le, (f_t1_s).le,
        (f_t3_s).le]
      decide
  · refine ⟨0, le_rfl, zero_lt_one, ?_⟩
    rw [D 0 le_rfl zero_lt_one]
    simp only [Ival, not_lt.2 hs0, not_le.2 z_t10, not_le.2 z_t9, not_le.2 z_t11,
        not_le.2 z_t2, not_le.2 z_t1, not_le.2 z_t3]
    decide

theorem cell_42 (x : ℝ) (hx1 : ((4 / 9 : ℚ) : ℝ) < x) (hx2 : x < ((9 / 20 : ℚ) : ℝ)) :
    phi x = 1 := by
  have f11 := floor_bounds 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have f10 := floor_bounds 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f9 := floor_bounds 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have f8 := floor_bounds 8 3 _ _ x hx1 hx2 (by decide +kernel)
  have f2 := floor_bounds 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have f1 := floor_bounds 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f3 := floor_bounds 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have D := rho_decomp x 4 4 4 3 0 0 1 f11 f10 f9 f8 f2 f1 f3
  have hs0 := s_nonneg 4 x f11
  have hs1 := s_lt_one 4 x f11
  have f_t1_s : A 1 0 x < A (-11) (-4 - 1) x :=
    A_lt 1 0 (-11) (-4 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_s : A 10 4 x < A (-11) (-4 - 1) x :=
    A_lt 10 4 (-11) (-4 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_s : A 11 4 x < A (-11) (-4 - 1) x :=
    A_lt 11 4 (-11) (-4 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_s : A 2 0 x < A (-11) (-4 - 1) x :=
    A_lt 2 0 (-11) (-4 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_s : A 3 1 x < A (-11) (-4 - 1) x :=
    A_lt 3 1 (-11) (-4 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t9 : A (-11) (-4 - 1) x < A 9 4 x :=
    A_lt (-11) (-4 - 1) 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t1 : A 10 4 x < A 1 0 x :=
    A_lt 10 4 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t1 : A 11 4 x < A 1 0 x :=
    A_lt 11 4 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t1 : A 2 0 x < A 1 0 x :=
    A_lt 2 0 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t3 : A 1 0 x < A 3 1 x :=
    A_lt 1 0 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t9 : A 1 0 x < A 9 4 x :=
    A_lt 1 0 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t10 : A 11 4 x < A 10 4 x :=
    A_lt 11 4 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t10 : A 2 0 x < A 10 4 x :=
    A_lt 2 0 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t3 : A 10 4 x < A 3 1 x :=
    A_lt 10 4 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t9 : A 10 4 x < A 9 4 x :=
    A_lt 10 4 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t2 : A 11 4 x < A 2 0 x :=
    A_lt 11 4 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t3 : A 11 4 x < A 3 1 x :=
    A_lt 11 4 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t9 : A 11 4 x < A 9 4 x :=
    A_lt 11 4 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t3 : A 2 0 x < A 3 1 x :=
    A_lt 2 0 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t9 : A 2 0 x < A 9 4 x :=
    A_lt 2 0 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_t9 : A 3 1 x < A 9 4 x :=
    A_lt 3 1 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have z_t10 : 0 < A 10 4 x :=
    A_pos 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have o_t10 : A 10 4 x < 1 :=
    A_lt_one 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have z_t9 : 0 < A 9 4 x :=
    A_pos 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have o_t9 : A 9 4 x < 1 :=
    A_lt_one 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have z_t11 : 0 < A 11 4 x :=
    A_pos 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have o_t11 : A 11 4 x < 1 :=
    A_lt_one 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have z_t2 : 0 < A 2 0 x :=
    A_pos 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t2 : A 2 0 x < 1 :=
    A_lt_one 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t1 : 0 < A 1 0 x :=
    A_pos 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t1 : A 1 0 x < 1 :=
    A_lt_one 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t3 : 0 < A 3 1 x :=
    A_pos 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have o_t3 : A 3 1 x < 1 :=
    A_lt_one 3 1 _ _ x hx1 hx2 (by decide +kernel)
  refine phi_eq x 1 ?_ ?_
  · intro y hy0 hy1
    rw [D y hy0 hy1]
    have := Ival_ge x 4 4 4 0 0 1 (1 - (2)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ y hy0
      hy1
    · omega
    · simp only [Ival, not_lt.2 hs0, not_le.2 z_t10, not_le.2 z_t9, not_le.2 z_t11,
        not_le.2 z_t2, not_le.2 z_t1, not_le.2 z_t3]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t10_s).le, not_le.2 f_t10_t9, (f_t11_t10).le, (f_t2_t10).le,
        not_le.2 f_t10_t1, not_le.2 f_t10_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, f_s_t9, (f_t10_t9).le, (f_t11_t9).le, (f_t2_t9).le, (f_t1_t9).le,
        (f_t3_t9).le, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t11_s).le, not_le.2 f_t11_t10, not_le.2 f_t11_t9,
        not_le.2 f_t11_t2, not_le.2 f_t11_t1, not_le.2 f_t11_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t2_s).le, not_le.2 f_t2_t10, not_le.2 f_t2_t9, (f_t11_t2).le,
        not_le.2 f_t2_t1, not_le.2 f_t2_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t1_s).le, (f_t10_t1).le, not_le.2 f_t1_t9, (f_t11_t1).le,
        (f_t2_t1).le, not_le.2 f_t1_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t3_s).le, (f_t10_t3).le, not_le.2 f_t3_t9, (f_t11_t3).le,
        (f_t2_t3).le, (f_t1_t3).le, le_refl]
      decide
    · simp only [Ip, (f_t10_s).le, not_le.2 f_s_t9, (f_t11_s).le, (f_t2_s).le, (f_t1_s).le,
        (f_t3_s).le]
      decide
  · refine ⟨A 3 1 x, z_t3.le, o_t3, ?_⟩
    rw [D _ z_t3.le o_t3]
    simp only [Ival, not_lt.2 (f_t3_s).le, (f_t10_t3).le, not_le.2 f_t3_t9, (f_t11_t3).le,
        (f_t2_t3).le, (f_t1_t3).le, le_refl]
    decide

theorem cell_43 (x : ℝ) (hx1 : ((9 / 20 : ℚ) : ℝ) < x) (hx2 : x < ((5 / 11 : ℚ) : ℝ)) :
    phi x = 1 := by
  have f11 := floor_bounds 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have f10 := floor_bounds 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f9 := floor_bounds 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have f8 := floor_bounds 8 3 _ _ x hx1 hx2 (by decide +kernel)
  have f2 := floor_bounds 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have f1 := floor_bounds 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f3 := floor_bounds 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have D := rho_decomp x 4 4 4 3 0 0 1 f11 f10 f9 f8 f2 f1 f3
  have hs0 := s_nonneg 4 x f11
  have hs1 := s_lt_one 4 x f11
  have f_t1_s : A 1 0 x < A (-11) (-4 - 1) x :=
    A_lt 1 0 (-11) (-4 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_s : A 10 4 x < A (-11) (-4 - 1) x :=
    A_lt 10 4 (-11) (-4 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_s : A 11 4 x < A (-11) (-4 - 1) x :=
    A_lt 11 4 (-11) (-4 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_s : A 2 0 x < A (-11) (-4 - 1) x :=
    A_lt 2 0 (-11) (-4 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_s : A 3 1 x < A (-11) (-4 - 1) x :=
    A_lt 3 1 (-11) (-4 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_s : A 9 4 x < A (-11) (-4 - 1) x :=
    A_lt 9 4 (-11) (-4 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t1 : A 10 4 x < A 1 0 x :=
    A_lt 10 4 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t1 : A 11 4 x < A 1 0 x :=
    A_lt 11 4 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t1 : A 2 0 x < A 1 0 x :=
    A_lt 2 0 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t3 : A 1 0 x < A 3 1 x :=
    A_lt 1 0 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t9 : A 1 0 x < A 9 4 x :=
    A_lt 1 0 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t10 : A 11 4 x < A 10 4 x :=
    A_lt 11 4 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t10 : A 2 0 x < A 10 4 x :=
    A_lt 2 0 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t3 : A 10 4 x < A 3 1 x :=
    A_lt 10 4 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t9 : A 10 4 x < A 9 4 x :=
    A_lt 10 4 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t2 : A 11 4 x < A 2 0 x :=
    A_lt 11 4 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t3 : A 11 4 x < A 3 1 x :=
    A_lt 11 4 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t9 : A 11 4 x < A 9 4 x :=
    A_lt 11 4 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t3 : A 2 0 x < A 3 1 x :=
    A_lt 2 0 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t9 : A 2 0 x < A 9 4 x :=
    A_lt 2 0 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_t9 : A 3 1 x < A 9 4 x :=
    A_lt 3 1 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have z_t10 : 0 < A 10 4 x :=
    A_pos 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have o_t10 : A 10 4 x < 1 :=
    A_lt_one 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have z_t9 : 0 < A 9 4 x :=
    A_pos 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have o_t9 : A 9 4 x < 1 :=
    A_lt_one 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have z_t11 : 0 < A 11 4 x :=
    A_pos 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have o_t11 : A 11 4 x < 1 :=
    A_lt_one 11 4 _ _ x hx1 hx2 (by decide +kernel)
  have z_t2 : 0 < A 2 0 x :=
    A_pos 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t2 : A 2 0 x < 1 :=
    A_lt_one 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t1 : 0 < A 1 0 x :=
    A_pos 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t1 : A 1 0 x < 1 :=
    A_lt_one 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t3 : 0 < A 3 1 x :=
    A_pos 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have o_t3 : A 3 1 x < 1 :=
    A_lt_one 3 1 _ _ x hx1 hx2 (by decide +kernel)
  refine phi_eq x 1 ?_ ?_
  · intro y hy0 hy1
    rw [D y hy0 hy1]
    have := Ival_ge x 4 4 4 0 0 1 (1 - (2)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ y hy0
      hy1
    · omega
    · simp only [Ival, not_lt.2 hs0, not_le.2 z_t10, not_le.2 z_t9, not_le.2 z_t11,
        not_le.2 z_t2, not_le.2 z_t1, not_le.2 z_t3]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t10_s).le, not_le.2 f_t10_t9, (f_t11_t10).le, (f_t2_t10).le,
        not_le.2 f_t10_t1, not_le.2 f_t10_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t9_s).le, (f_t10_t9).le, (f_t11_t9).le, (f_t2_t9).le,
        (f_t1_t9).le, (f_t3_t9).le, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t11_s).le, not_le.2 f_t11_t10, not_le.2 f_t11_t9,
        not_le.2 f_t11_t2, not_le.2 f_t11_t1, not_le.2 f_t11_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t2_s).le, not_le.2 f_t2_t10, not_le.2 f_t2_t9, (f_t11_t2).le,
        not_le.2 f_t2_t1, not_le.2 f_t2_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t1_s).le, (f_t10_t1).le, not_le.2 f_t1_t9, (f_t11_t1).le,
        (f_t2_t1).le, not_le.2 f_t1_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t3_s).le, (f_t10_t3).le, not_le.2 f_t3_t9, (f_t11_t3).le,
        (f_t2_t3).le, (f_t1_t3).le, le_refl]
      decide
    · simp only [Ip, (f_t10_s).le, (f_t9_s).le, (f_t11_s).le, (f_t2_s).le, (f_t1_s).le,
        (f_t3_s).le]
      decide
  · refine ⟨A 3 1 x, z_t3.le, o_t3, ?_⟩
    rw [D _ z_t3.le o_t3]
    simp only [Ival, not_lt.2 (f_t3_s).le, (f_t10_t3).le, not_le.2 f_t3_t9, (f_t11_t3).le,
        (f_t2_t3).le, (f_t1_t3).le, le_refl]
    decide

theorem cell_44 (x : ℝ) (hx1 : ((5 / 11 : ℚ) : ℝ) < x) (hx2 : x < ((6 / 13 : ℚ) : ℝ)) :
    phi x = 2 := by
  have f11 := floor_bounds 11 5 _ _ x hx1 hx2 (by decide +kernel)
  have f10 := floor_bounds 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f9 := floor_bounds 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have f8 := floor_bounds 8 3 _ _ x hx1 hx2 (by decide +kernel)
  have f2 := floor_bounds 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have f1 := floor_bounds 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f3 := floor_bounds 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have D := rho_decomp x 5 4 4 3 0 0 1 f11 f10 f9 f8 f2 f1 f3
  have hs0 := s_nonneg 5 x f11
  have hs1 := s_lt_one 5 x f11
  have f_s_t1 : A (-11) (-5 - 1) x < A 1 0 x :=
    A_lt (-11) (-5 - 1) 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t10 : A (-11) (-5 - 1) x < A 10 4 x :=
    A_lt (-11) (-5 - 1) 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t11 : A (-11) (-5 - 1) x < A 11 5 x :=
    A_lt (-11) (-5 - 1) 11 5 _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t2 : A (-11) (-5 - 1) x < A 2 0 x :=
    A_lt (-11) (-5 - 1) 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t3 : A (-11) (-5 - 1) x < A 3 1 x :=
    A_lt (-11) (-5 - 1) 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t9 : A (-11) (-5 - 1) x < A 9 4 x :=
    A_lt (-11) (-5 - 1) 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t1 : A 10 4 x < A 1 0 x :=
    A_lt 10 4 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t11 : A 1 0 x < A 11 5 x :=
    A_lt 1 0 11 5 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t1 : A 2 0 x < A 1 0 x :=
    A_lt 2 0 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t3 : A 1 0 x < A 3 1 x :=
    A_lt 1 0 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t9 : A 1 0 x < A 9 4 x :=
    A_lt 1 0 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t11 : A 10 4 x < A 11 5 x :=
    A_lt 10 4 11 5 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t10 : A 2 0 x < A 10 4 x :=
    A_lt 2 0 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t3 : A 10 4 x < A 3 1 x :=
    A_lt 10 4 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t9 : A 10 4 x < A 9 4 x :=
    A_lt 10 4 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t11 : A 2 0 x < A 11 5 x :=
    A_lt 2 0 11 5 _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_t11 : A 3 1 x < A 11 5 x :=
    A_lt 3 1 11 5 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t11 : A 9 4 x < A 11 5 x :=
    A_lt 9 4 11 5 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t3 : A 2 0 x < A 3 1 x :=
    A_lt 2 0 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t9 : A 2 0 x < A 9 4 x :=
    A_lt 2 0 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_t9 : A 3 1 x < A 9 4 x :=
    A_lt 3 1 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have z_t10 : 0 < A 10 4 x :=
    A_pos 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have o_t10 : A 10 4 x < 1 :=
    A_lt_one 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have z_t9 : 0 < A 9 4 x :=
    A_pos 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have o_t9 : A 9 4 x < 1 :=
    A_lt_one 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have z_t11 : 0 < A 11 5 x :=
    A_pos 11 5 _ _ x hx1 hx2 (by decide +kernel)
  have o_t11 : A 11 5 x < 1 :=
    A_lt_one 11 5 _ _ x hx1 hx2 (by decide +kernel)
  have z_t2 : 0 < A 2 0 x :=
    A_pos 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t2 : A 2 0 x < 1 :=
    A_lt_one 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t1 : 0 < A 1 0 x :=
    A_pos 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t1 : A 1 0 x < 1 :=
    A_lt_one 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t3 : 0 < A 3 1 x :=
    A_pos 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have o_t3 : A 3 1 x < 1 :=
    A_lt_one 3 1 _ _ x hx1 hx2 (by decide +kernel)
  refine phi_eq x 2 ?_ ?_
  · intro y hy0 hy1
    rw [D y hy0 hy1]
    have := Ival_ge x 5 4 4 0 0 1 (2 - (3)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ y hy0
      hy1
    · omega
    · simp only [Ival, not_lt.2 hs0, not_le.2 z_t10, not_le.2 z_t9, not_le.2 z_t11,
        not_le.2 z_t2, not_le.2 z_t1, not_le.2 z_t3]
      decide
    · intro _ _
      simp only [Ival, f_s_t10, not_le.2 f_t10_t9, not_le.2 f_t10_t11, (f_t2_t10).le,
        not_le.2 f_t10_t1, not_le.2 f_t10_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, f_s_t9, (f_t10_t9).le, not_le.2 f_t9_t11, (f_t2_t9).le, (f_t1_t9).le,
        (f_t3_t9).le, le_refl]
      decide
    · intro _ _
      simp only [Ival, f_s_t11, (f_t10_t11).le, (f_t9_t11).le, (f_t2_t11).le, (f_t1_t11).le,
        (f_t3_t11).le, le_refl]
      decide
    · intro _ _
      simp only [Ival, f_s_t2, not_le.2 f_t2_t10, not_le.2 f_t2_t9, not_le.2 f_t2_t11,
        not_le.2 f_t2_t1, not_le.2 f_t2_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, f_s_t1, (f_t10_t1).le, not_le.2 f_t1_t9, not_le.2 f_t1_t11, (f_t2_t1).le,
        not_le.2 f_t1_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, f_s_t3, (f_t10_t3).le, not_le.2 f_t3_t9, not_le.2 f_t3_t11, (f_t2_t3).le,
        (f_t1_t3).le, le_refl]
      decide
    · simp only [Ip, not_le.2 f_s_t10, not_le.2 f_s_t9, not_le.2 f_s_t11, not_le.2 f_s_t2,
        not_le.2 f_s_t1, not_le.2 f_s_t3]
      decide
  · refine ⟨A 3 1 x, z_t3.le, o_t3, ?_⟩
    rw [D _ z_t3.le o_t3]
    simp only [Ival, f_s_t3, (f_t10_t3).le, not_le.2 f_t3_t9, not_le.2 f_t3_t11, (f_t2_t3).le,
        (f_t1_t3).le, le_refl]
    decide

theorem cell_45 (x : ℝ) (hx1 : ((6 / 13 : ℚ) : ℝ) < x) (hx2 : x < ((10 / 21 : ℚ) : ℝ)) :
    phi x = 2 := by
  have f11 := floor_bounds 11 5 _ _ x hx1 hx2 (by decide +kernel)
  have f10 := floor_bounds 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f9 := floor_bounds 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have f8 := floor_bounds 8 3 _ _ x hx1 hx2 (by decide +kernel)
  have f2 := floor_bounds 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have f1 := floor_bounds 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f3 := floor_bounds 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have D := rho_decomp x 5 4 4 3 0 0 1 f11 f10 f9 f8 f2 f1 f3
  have hs0 := s_nonneg 5 x f11
  have hs1 := s_lt_one 5 x f11
  have f_s_t1 : A (-11) (-5 - 1) x < A 1 0 x :=
    A_lt (-11) (-5 - 1) 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t10 : A (-11) (-5 - 1) x < A 10 4 x :=
    A_lt (-11) (-5 - 1) 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t11 : A (-11) (-5 - 1) x < A 11 5 x :=
    A_lt (-11) (-5 - 1) 11 5 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_s : A 2 0 x < A (-11) (-5 - 1) x :=
    A_lt 2 0 (-11) (-5 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t3 : A (-11) (-5 - 1) x < A 3 1 x :=
    A_lt (-11) (-5 - 1) 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t9 : A (-11) (-5 - 1) x < A 9 4 x :=
    A_lt (-11) (-5 - 1) 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t1 : A 10 4 x < A 1 0 x :=
    A_lt 10 4 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t11 : A 1 0 x < A 11 5 x :=
    A_lt 1 0 11 5 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t1 : A 2 0 x < A 1 0 x :=
    A_lt 2 0 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t3 : A 1 0 x < A 3 1 x :=
    A_lt 1 0 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t9 : A 1 0 x < A 9 4 x :=
    A_lt 1 0 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t11 : A 10 4 x < A 11 5 x :=
    A_lt 10 4 11 5 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t10 : A 2 0 x < A 10 4 x :=
    A_lt 2 0 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t3 : A 10 4 x < A 3 1 x :=
    A_lt 10 4 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t9 : A 10 4 x < A 9 4 x :=
    A_lt 10 4 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t11 : A 2 0 x < A 11 5 x :=
    A_lt 2 0 11 5 _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_t11 : A 3 1 x < A 11 5 x :=
    A_lt 3 1 11 5 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t11 : A 9 4 x < A 11 5 x :=
    A_lt 9 4 11 5 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t3 : A 2 0 x < A 3 1 x :=
    A_lt 2 0 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t9 : A 2 0 x < A 9 4 x :=
    A_lt 2 0 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_t9 : A 3 1 x < A 9 4 x :=
    A_lt 3 1 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have z_t10 : 0 < A 10 4 x :=
    A_pos 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have o_t10 : A 10 4 x < 1 :=
    A_lt_one 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have z_t9 : 0 < A 9 4 x :=
    A_pos 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have o_t9 : A 9 4 x < 1 :=
    A_lt_one 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have z_t11 : 0 < A 11 5 x :=
    A_pos 11 5 _ _ x hx1 hx2 (by decide +kernel)
  have o_t11 : A 11 5 x < 1 :=
    A_lt_one 11 5 _ _ x hx1 hx2 (by decide +kernel)
  have z_t2 : 0 < A 2 0 x :=
    A_pos 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t2 : A 2 0 x < 1 :=
    A_lt_one 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t1 : 0 < A 1 0 x :=
    A_pos 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t1 : A 1 0 x < 1 :=
    A_lt_one 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t3 : 0 < A 3 1 x :=
    A_pos 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have o_t3 : A 3 1 x < 1 :=
    A_lt_one 3 1 _ _ x hx1 hx2 (by decide +kernel)
  refine phi_eq x 2 ?_ ?_
  · intro y hy0 hy1
    rw [D y hy0 hy1]
    have := Ival_ge x 5 4 4 0 0 1 (2 - (3)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ y hy0
      hy1
    · omega
    · simp only [Ival, not_lt.2 hs0, not_le.2 z_t10, not_le.2 z_t9, not_le.2 z_t11,
        not_le.2 z_t2, not_le.2 z_t1, not_le.2 z_t3]
      decide
    · intro _ _
      simp only [Ival, f_s_t10, not_le.2 f_t10_t9, not_le.2 f_t10_t11, (f_t2_t10).le,
        not_le.2 f_t10_t1, not_le.2 f_t10_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, f_s_t9, (f_t10_t9).le, not_le.2 f_t9_t11, (f_t2_t9).le, (f_t1_t9).le,
        (f_t3_t9).le, le_refl]
      decide
    · intro _ _
      simp only [Ival, f_s_t11, (f_t10_t11).le, (f_t9_t11).le, (f_t2_t11).le, (f_t1_t11).le,
        (f_t3_t11).le, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t2_s).le, not_le.2 f_t2_t10, not_le.2 f_t2_t9,
        not_le.2 f_t2_t11, not_le.2 f_t2_t1, not_le.2 f_t2_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, f_s_t1, (f_t10_t1).le, not_le.2 f_t1_t9, not_le.2 f_t1_t11, (f_t2_t1).le,
        not_le.2 f_t1_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, f_s_t3, (f_t10_t3).le, not_le.2 f_t3_t9, not_le.2 f_t3_t11, (f_t2_t3).le,
        (f_t1_t3).le, le_refl]
      decide
    · simp only [Ip, not_le.2 f_s_t10, not_le.2 f_s_t9, not_le.2 f_s_t11, (f_t2_s).le,
        not_le.2 f_s_t1, not_le.2 f_s_t3]
      decide
  · refine ⟨A 2 0 x, z_t2.le, o_t2, ?_⟩
    rw [D _ z_t2.le o_t2]
    simp only [Ival, not_lt.2 (f_t2_s).le, not_le.2 f_t2_t10, not_le.2 f_t2_t9,
        not_le.2 f_t2_t11, not_le.2 f_t2_t1, not_le.2 f_t2_t3, le_refl]
    decide

theorem cell_46 (x : ℝ) (hx1 : ((10 / 21 : ℚ) : ℝ) < x) (hx2 : x < ((1 / 2 : ℚ) : ℝ)) :
    phi x = 2 := by
  have f11 := floor_bounds 11 5 _ _ x hx1 hx2 (by decide +kernel)
  have f10 := floor_bounds 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f9 := floor_bounds 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have f8 := floor_bounds 8 3 _ _ x hx1 hx2 (by decide +kernel)
  have f2 := floor_bounds 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have f1 := floor_bounds 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f3 := floor_bounds 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have D := rho_decomp x 5 4 4 3 0 0 1 f11 f10 f9 f8 f2 f1 f3
  have hs0 := s_nonneg 5 x f11
  have hs1 := s_lt_one 5 x f11
  have f_s_t1 : A (-11) (-5 - 1) x < A 1 0 x :=
    A_lt (-11) (-5 - 1) 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_s : A 10 4 x < A (-11) (-5 - 1) x :=
    A_lt 10 4 (-11) (-5 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t11 : A (-11) (-5 - 1) x < A 11 5 x :=
    A_lt (-11) (-5 - 1) 11 5 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_s : A 2 0 x < A (-11) (-5 - 1) x :=
    A_lt 2 0 (-11) (-5 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t3 : A (-11) (-5 - 1) x < A 3 1 x :=
    A_lt (-11) (-5 - 1) 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t9 : A (-11) (-5 - 1) x < A 9 4 x :=
    A_lt (-11) (-5 - 1) 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t1 : A 10 4 x < A 1 0 x :=
    A_lt 10 4 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t11 : A 1 0 x < A 11 5 x :=
    A_lt 1 0 11 5 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t1 : A 2 0 x < A 1 0 x :=
    A_lt 2 0 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t3 : A 1 0 x < A 3 1 x :=
    A_lt 1 0 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t9 : A 1 0 x < A 9 4 x :=
    A_lt 1 0 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t11 : A 10 4 x < A 11 5 x :=
    A_lt 10 4 11 5 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t10 : A 2 0 x < A 10 4 x :=
    A_lt 2 0 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t3 : A 10 4 x < A 3 1 x :=
    A_lt 10 4 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t9 : A 10 4 x < A 9 4 x :=
    A_lt 10 4 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t11 : A 2 0 x < A 11 5 x :=
    A_lt 2 0 11 5 _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_t11 : A 3 1 x < A 11 5 x :=
    A_lt 3 1 11 5 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t11 : A 9 4 x < A 11 5 x :=
    A_lt 9 4 11 5 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t3 : A 2 0 x < A 3 1 x :=
    A_lt 2 0 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t9 : A 2 0 x < A 9 4 x :=
    A_lt 2 0 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_t9 : A 3 1 x < A 9 4 x :=
    A_lt 3 1 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have z_t10 : 0 < A 10 4 x :=
    A_pos 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have o_t10 : A 10 4 x < 1 :=
    A_lt_one 10 4 _ _ x hx1 hx2 (by decide +kernel)
  have z_t9 : 0 < A 9 4 x :=
    A_pos 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have o_t9 : A 9 4 x < 1 :=
    A_lt_one 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have z_t11 : 0 < A 11 5 x :=
    A_pos 11 5 _ _ x hx1 hx2 (by decide +kernel)
  have o_t11 : A 11 5 x < 1 :=
    A_lt_one 11 5 _ _ x hx1 hx2 (by decide +kernel)
  have z_t2 : 0 < A 2 0 x :=
    A_pos 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t2 : A 2 0 x < 1 :=
    A_lt_one 2 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t1 : 0 < A 1 0 x :=
    A_pos 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t1 : A 1 0 x < 1 :=
    A_lt_one 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t3 : 0 < A 3 1 x :=
    A_pos 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have o_t3 : A 3 1 x < 1 :=
    A_lt_one 3 1 _ _ x hx1 hx2 (by decide +kernel)
  refine phi_eq x 2 ?_ ?_
  · intro y hy0 hy1
    rw [D y hy0 hy1]
    have := Ival_ge x 5 4 4 0 0 1 (2 - (3)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ y hy0
      hy1
    · omega
    · simp only [Ival, not_lt.2 hs0, not_le.2 z_t10, not_le.2 z_t9, not_le.2 z_t11,
        not_le.2 z_t2, not_le.2 z_t1, not_le.2 z_t3]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t10_s).le, not_le.2 f_t10_t9, not_le.2 f_t10_t11,
        (f_t2_t10).le, not_le.2 f_t10_t1, not_le.2 f_t10_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, f_s_t9, (f_t10_t9).le, not_le.2 f_t9_t11, (f_t2_t9).le, (f_t1_t9).le,
        (f_t3_t9).le, le_refl]
      decide
    · intro _ _
      simp only [Ival, f_s_t11, (f_t10_t11).le, (f_t9_t11).le, (f_t2_t11).le, (f_t1_t11).le,
        (f_t3_t11).le, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t2_s).le, not_le.2 f_t2_t10, not_le.2 f_t2_t9,
        not_le.2 f_t2_t11, not_le.2 f_t2_t1, not_le.2 f_t2_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, f_s_t1, (f_t10_t1).le, not_le.2 f_t1_t9, not_le.2 f_t1_t11, (f_t2_t1).le,
        not_le.2 f_t1_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, f_s_t3, (f_t10_t3).le, not_le.2 f_t3_t9, not_le.2 f_t3_t11, (f_t2_t3).le,
        (f_t1_t3).le, le_refl]
      decide
    · simp only [Ip, (f_t10_s).le, not_le.2 f_s_t9, not_le.2 f_s_t11, (f_t2_s).le,
        not_le.2 f_s_t1, not_le.2 f_s_t3]
      decide
  · refine ⟨A 2 0 x, z_t2.le, o_t2, ?_⟩
    rw [D _ z_t2.le o_t2]
    simp only [Ival, not_lt.2 (f_t2_s).le, not_le.2 f_t2_t10, not_le.2 f_t2_t9,
        not_le.2 f_t2_t11, not_le.2 f_t2_t1, not_le.2 f_t2_t3, le_refl]
    decide

theorem cell_47 (x : ℝ) (hx1 : ((1 / 2 : ℚ) : ℝ) < x) (hx2 : x < ((11 / 21 : ℚ) : ℝ)) :
    phi x = 0 := by
  have f11 := floor_bounds 11 5 _ _ x hx1 hx2 (by decide +kernel)
  have f10 := floor_bounds 10 5 _ _ x hx1 hx2 (by decide +kernel)
  have f9 := floor_bounds 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have f8 := floor_bounds 8 4 _ _ x hx1 hx2 (by decide +kernel)
  have f2 := floor_bounds 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f1 := floor_bounds 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f3 := floor_bounds 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have D := rho_decomp x 5 5 4 4 1 0 1 f11 f10 f9 f8 f2 f1 f3
  have hs0 := s_nonneg 5 x f11
  have hs1 := s_lt_one 5 x f11
  have f_t1_s : A 1 0 x < A (-11) (-5 - 1) x :=
    A_lt 1 0 (-11) (-5 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t10 : A (-11) (-5 - 1) x < A 10 5 x :=
    A_lt (-11) (-5 - 1) 10 5 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_s : A 11 5 x < A (-11) (-5 - 1) x :=
    A_lt 11 5 (-11) (-5 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t2 : A (-11) (-5 - 1) x < A 2 1 x :=
    A_lt (-11) (-5 - 1) 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_s : A 3 1 x < A (-11) (-5 - 1) x :=
    A_lt 3 1 (-11) (-5 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_s : A 9 4 x < A (-11) (-5 - 1) x :=
    A_lt 9 4 (-11) (-5 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t10 : A 1 0 x < A 10 5 x :=
    A_lt 1 0 10 5 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t1 : A 11 5 x < A 1 0 x :=
    A_lt 11 5 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t2 : A 1 0 x < A 2 1 x :=
    A_lt 1 0 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_t1 : A 3 1 x < A 1 0 x :=
    A_lt 3 1 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t1 : A 9 4 x < A 1 0 x :=
    A_lt 9 4 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t10 : A 11 5 x < A 10 5 x :=
    A_lt 11 5 10 5 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t2 : A 10 5 x < A 2 1 x :=
    A_lt 10 5 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_t10 : A 3 1 x < A 10 5 x :=
    A_lt 3 1 10 5 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t10 : A 9 4 x < A 10 5 x :=
    A_lt 9 4 10 5 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t2 : A 11 5 x < A 2 1 x :=
    A_lt 11 5 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t3 : A 11 5 x < A 3 1 x :=
    A_lt 11 5 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t9 : A 11 5 x < A 9 4 x :=
    A_lt 11 5 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_t2 : A 3 1 x < A 2 1 x :=
    A_lt 3 1 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t2 : A 9 4 x < A 2 1 x :=
    A_lt 9 4 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t3 : A 9 4 x < A 3 1 x :=
    A_lt 9 4 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have z_t10 : 0 < A 10 5 x :=
    A_pos 10 5 _ _ x hx1 hx2 (by decide +kernel)
  have o_t10 : A 10 5 x < 1 :=
    A_lt_one 10 5 _ _ x hx1 hx2 (by decide +kernel)
  have z_t9 : 0 < A 9 4 x :=
    A_pos 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have o_t9 : A 9 4 x < 1 :=
    A_lt_one 9 4 _ _ x hx1 hx2 (by decide +kernel)
  have z_t11 : 0 < A 11 5 x :=
    A_pos 11 5 _ _ x hx1 hx2 (by decide +kernel)
  have o_t11 : A 11 5 x < 1 :=
    A_lt_one 11 5 _ _ x hx1 hx2 (by decide +kernel)
  have z_t2 : 0 < A 2 1 x :=
    A_pos 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have o_t2 : A 2 1 x < 1 :=
    A_lt_one 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have z_t1 : 0 < A 1 0 x :=
    A_pos 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t1 : A 1 0 x < 1 :=
    A_lt_one 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t3 : 0 < A 3 1 x :=
    A_pos 3 1 _ _ x hx1 hx2 (by decide +kernel)
  have o_t3 : A 3 1 x < 1 :=
    A_lt_one 3 1 _ _ x hx1 hx2 (by decide +kernel)
  refine phi_eq x 0 ?_ ?_
  · intro y _ _
    exact rho_nonneg x y
  · refine ⟨0, le_rfl, zero_lt_one, ?_⟩
    rw [D 0 le_rfl zero_lt_one]
    simp only [Ival, not_lt.2 hs0, not_le.2 z_t10, not_le.2 z_t9, not_le.2 z_t11,
        not_le.2 z_t2, not_le.2 z_t1, not_le.2 z_t3]
    decide

end Zeta2GammaCells
