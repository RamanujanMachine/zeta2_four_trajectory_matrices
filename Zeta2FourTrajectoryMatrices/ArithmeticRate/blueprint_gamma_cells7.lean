import Zeta2FourTrajectoryMatrices.ArithmeticRate.blueprint_gamma_core

open Zeta2Blueprint Zeta2GammaCore

noncomputable section

namespace Zeta2GammaCells

theorem cell_72 (x : ℝ) (hx1 : ((17 / 22 : ℚ) : ℝ) < x) (hx2 : x < ((7 / 9 : ℚ) : ℝ)) :
    phi x = 0 := by
  have f11 := floor_bounds 11 8 _ _ x hx1 hx2 (by decide +kernel)
  have f10 := floor_bounds 10 7 _ _ x hx1 hx2 (by decide +kernel)
  have f9 := floor_bounds 9 6 _ _ x hx1 hx2 (by decide +kernel)
  have f8 := floor_bounds 8 6 _ _ x hx1 hx2 (by decide +kernel)
  have f2 := floor_bounds 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f1 := floor_bounds 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f3 := floor_bounds 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have D := rho_decomp x 8 7 6 6 1 0 2 f11 f10 f9 f8 f2 f1 f3
  have hs0 := s_nonneg 8 x f11
  have hs1 := s_lt_one 8 x f11
  have f_t1_s : A 1 0 x < A (-11) (-8 - 1) x :=
    A_lt 1 0 (-11) (-8 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_s : A 10 7 x < A (-11) (-8 - 1) x :=
    A_lt 10 7 (-11) (-8 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_s : A 11 8 x < A (-11) (-8 - 1) x :=
    A_lt 11 8 (-11) (-8 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_s : A 2 1 x < A (-11) (-8 - 1) x :=
    A_lt 2 1 (-11) (-8 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t3 : A (-11) (-8 - 1) x < A 3 2 x :=
    A_lt (-11) (-8 - 1) 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_s : A 9 6 x < A (-11) (-8 - 1) x :=
    A_lt 9 6 (-11) (-8 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t10 : A 1 0 x < A 10 7 x :=
    A_lt 1 0 10 7 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t11 : A 1 0 x < A 11 8 x :=
    A_lt 1 0 11 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t2 : A 1 0 x < A 2 1 x :=
    A_lt 1 0 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t3 : A 1 0 x < A 3 2 x :=
    A_lt 1 0 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t1 : A 9 6 x < A 1 0 x :=
    A_lt 9 6 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t11 : A 10 7 x < A 11 8 x :=
    A_lt 10 7 11 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t2 : A 10 7 x < A 2 1 x :=
    A_lt 10 7 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t3 : A 10 7 x < A 3 2 x :=
    A_lt 10 7 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t10 : A 9 6 x < A 10 7 x :=
    A_lt 9 6 10 7 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t11 : A 2 1 x < A 11 8 x :=
    A_lt 2 1 11 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t3 : A 11 8 x < A 3 2 x :=
    A_lt 11 8 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t11 : A 9 6 x < A 11 8 x :=
    A_lt 9 6 11 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t3 : A 2 1 x < A 3 2 x :=
    A_lt 2 1 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t2 : A 9 6 x < A 2 1 x :=
    A_lt 9 6 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t3 : A 9 6 x < A 3 2 x :=
    A_lt 9 6 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have z_t10 : 0 < A 10 7 x :=
    A_pos 10 7 _ _ x hx1 hx2 (by decide +kernel)
  have o_t10 : A 10 7 x < 1 :=
    A_lt_one 10 7 _ _ x hx1 hx2 (by decide +kernel)
  have z_t9 : 0 < A 9 6 x :=
    A_pos 9 6 _ _ x hx1 hx2 (by decide +kernel)
  have o_t9 : A 9 6 x < 1 :=
    A_lt_one 9 6 _ _ x hx1 hx2 (by decide +kernel)
  have z_t11 : 0 < A 11 8 x :=
    A_pos 11 8 _ _ x hx1 hx2 (by decide +kernel)
  have o_t11 : A 11 8 x < 1 :=
    A_lt_one 11 8 _ _ x hx1 hx2 (by decide +kernel)
  have z_t2 : 0 < A 2 1 x :=
    A_pos 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have o_t2 : A 2 1 x < 1 :=
    A_lt_one 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have z_t1 : 0 < A 1 0 x :=
    A_pos 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t1 : A 1 0 x < 1 :=
    A_lt_one 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t3 : 0 < A 3 2 x :=
    A_pos 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have o_t3 : A 3 2 x < 1 :=
    A_lt_one 3 2 _ _ x hx1 hx2 (by decide +kernel)
  refine phi_eq x 0 ?_ ?_
  · intro y _ _
    exact rho_nonneg x y
  · refine ⟨0, le_rfl, zero_lt_one, ?_⟩
    rw [D 0 le_rfl zero_lt_one]
    simp only [Ival, not_lt.2 hs0, not_le.2 z_t10, not_le.2 z_t9, not_le.2 z_t11,
        not_le.2 z_t2, not_le.2 z_t1, not_le.2 z_t3]
    decide

theorem cell_73 (x : ℝ) (hx1 : ((7 / 9 : ℚ) : ℝ) < x) (hx2 : x < ((11 / 14 : ℚ) : ℝ)) :
    phi x = 1 := by
  have f11 := floor_bounds 11 8 _ _ x hx1 hx2 (by decide +kernel)
  have f10 := floor_bounds 10 7 _ _ x hx1 hx2 (by decide +kernel)
  have f9 := floor_bounds 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f8 := floor_bounds 8 6 _ _ x hx1 hx2 (by decide +kernel)
  have f2 := floor_bounds 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f1 := floor_bounds 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f3 := floor_bounds 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have D := rho_decomp x 8 7 7 6 1 0 2 f11 f10 f9 f8 f2 f1 f3
  have hs0 := s_nonneg 8 x f11
  have hs1 := s_lt_one 8 x f11
  have f_t1_s : A 1 0 x < A (-11) (-8 - 1) x :=
    A_lt 1 0 (-11) (-8 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_s : A 10 7 x < A (-11) (-8 - 1) x :=
    A_lt 10 7 (-11) (-8 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_s : A 11 8 x < A (-11) (-8 - 1) x :=
    A_lt 11 8 (-11) (-8 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_s : A 2 1 x < A (-11) (-8 - 1) x :=
    A_lt 2 1 (-11) (-8 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t3 : A (-11) (-8 - 1) x < A 3 2 x :=
    A_lt (-11) (-8 - 1) 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t9 : A (-11) (-8 - 1) x < A 9 7 x :=
    A_lt (-11) (-8 - 1) 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t1 : A 10 7 x < A 1 0 x :=
    A_lt 10 7 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t11 : A 1 0 x < A 11 8 x :=
    A_lt 1 0 11 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t2 : A 1 0 x < A 2 1 x :=
    A_lt 1 0 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t3 : A 1 0 x < A 3 2 x :=
    A_lt 1 0 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t9 : A 1 0 x < A 9 7 x :=
    A_lt 1 0 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t11 : A 10 7 x < A 11 8 x :=
    A_lt 10 7 11 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t2 : A 10 7 x < A 2 1 x :=
    A_lt 10 7 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t3 : A 10 7 x < A 3 2 x :=
    A_lt 10 7 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t9 : A 10 7 x < A 9 7 x :=
    A_lt 10 7 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t2 : A 11 8 x < A 2 1 x :=
    A_lt 11 8 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t3 : A 11 8 x < A 3 2 x :=
    A_lt 11 8 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t9 : A 11 8 x < A 9 7 x :=
    A_lt 11 8 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t3 : A 2 1 x < A 3 2 x :=
    A_lt 2 1 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t9 : A 2 1 x < A 9 7 x :=
    A_lt 2 1 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_t9 : A 3 2 x < A 9 7 x :=
    A_lt 3 2 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have z_t10 : 0 < A 10 7 x :=
    A_pos 10 7 _ _ x hx1 hx2 (by decide +kernel)
  have o_t10 : A 10 7 x < 1 :=
    A_lt_one 10 7 _ _ x hx1 hx2 (by decide +kernel)
  have z_t9 : 0 < A 9 7 x :=
    A_pos 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have o_t9 : A 9 7 x < 1 :=
    A_lt_one 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have z_t11 : 0 < A 11 8 x :=
    A_pos 11 8 _ _ x hx1 hx2 (by decide +kernel)
  have o_t11 : A 11 8 x < 1 :=
    A_lt_one 11 8 _ _ x hx1 hx2 (by decide +kernel)
  have z_t2 : 0 < A 2 1 x :=
    A_pos 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have o_t2 : A 2 1 x < 1 :=
    A_lt_one 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have z_t1 : 0 < A 1 0 x :=
    A_pos 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t1 : A 1 0 x < 1 :=
    A_lt_one 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t3 : 0 < A 3 2 x :=
    A_pos 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have o_t3 : A 3 2 x < 1 :=
    A_lt_one 3 2 _ _ x hx1 hx2 (by decide +kernel)
  refine phi_eq x 1 ?_ ?_
  · intro y hy0 hy1
    rw [D y hy0 hy1]
    have := Ival_ge x 8 7 7 1 0 2 (1 - (1)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ y hy0
      hy1
    · omega
    · simp only [Ival, not_lt.2 hs0, not_le.2 z_t10, not_le.2 z_t9, not_le.2 z_t11,
        not_le.2 z_t2, not_le.2 z_t1, not_le.2 z_t3]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t10_s).le, not_le.2 f_t10_t9, not_le.2 f_t10_t11,
        not_le.2 f_t10_t2, not_le.2 f_t10_t1, not_le.2 f_t10_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, f_s_t9, (f_t10_t9).le, (f_t11_t9).le, (f_t2_t9).le, (f_t1_t9).le,
        (f_t3_t9).le, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t11_s).le, (f_t10_t11).le, not_le.2 f_t11_t9,
        not_le.2 f_t11_t2, (f_t1_t11).le, not_le.2 f_t11_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t2_s).le, (f_t10_t2).le, not_le.2 f_t2_t9, (f_t11_t2).le,
        (f_t1_t2).le, not_le.2 f_t2_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t1_s).le, (f_t10_t1).le, not_le.2 f_t1_t9, not_le.2 f_t1_t11,
        not_le.2 f_t1_t2, not_le.2 f_t1_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, f_s_t3, (f_t10_t3).le, not_le.2 f_t3_t9, (f_t11_t3).le, (f_t2_t3).le,
        (f_t1_t3).le, le_refl]
      decide
    · simp only [Ip, (f_t10_s).le, not_le.2 f_s_t9, (f_t11_s).le, (f_t2_s).le, (f_t1_s).le,
        not_le.2 f_s_t3]
      decide
  · refine ⟨0, le_rfl, zero_lt_one, ?_⟩
    rw [D 0 le_rfl zero_lt_one]
    simp only [Ival, not_lt.2 hs0, not_le.2 z_t10, not_le.2 z_t9, not_le.2 z_t11,
        not_le.2 z_t2, not_le.2 z_t1, not_le.2 z_t3]
    decide

theorem cell_74 (x : ℝ) (hx1 : ((11 / 14 : ℚ) : ℝ) < x) (hx2 : x < ((4 / 5 : ℚ) : ℝ)) :
    phi x = 0 := by
  have f11 := floor_bounds 11 8 _ _ x hx1 hx2 (by decide +kernel)
  have f10 := floor_bounds 10 7 _ _ x hx1 hx2 (by decide +kernel)
  have f9 := floor_bounds 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f8 := floor_bounds 8 6 _ _ x hx1 hx2 (by decide +kernel)
  have f2 := floor_bounds 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f1 := floor_bounds 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f3 := floor_bounds 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have D := rho_decomp x 8 7 7 6 1 0 2 f11 f10 f9 f8 f2 f1 f3
  have hs0 := s_nonneg 8 x f11
  have hs1 := s_lt_one 8 x f11
  have f_t1_s : A 1 0 x < A (-11) (-8 - 1) x :=
    A_lt 1 0 (-11) (-8 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_s : A 10 7 x < A (-11) (-8 - 1) x :=
    A_lt 10 7 (-11) (-8 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_s : A 11 8 x < A (-11) (-8 - 1) x :=
    A_lt 11 8 (-11) (-8 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_s : A 2 1 x < A (-11) (-8 - 1) x :=
    A_lt 2 1 (-11) (-8 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_s : A 3 2 x < A (-11) (-8 - 1) x :=
    A_lt 3 2 (-11) (-8 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t9 : A (-11) (-8 - 1) x < A 9 7 x :=
    A_lt (-11) (-8 - 1) 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t1 : A 10 7 x < A 1 0 x :=
    A_lt 10 7 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t11 : A 1 0 x < A 11 8 x :=
    A_lt 1 0 11 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t2 : A 1 0 x < A 2 1 x :=
    A_lt 1 0 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t3 : A 1 0 x < A 3 2 x :=
    A_lt 1 0 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t9 : A 1 0 x < A 9 7 x :=
    A_lt 1 0 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t11 : A 10 7 x < A 11 8 x :=
    A_lt 10 7 11 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t2 : A 10 7 x < A 2 1 x :=
    A_lt 10 7 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t3 : A 10 7 x < A 3 2 x :=
    A_lt 10 7 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t9 : A 10 7 x < A 9 7 x :=
    A_lt 10 7 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t2 : A 11 8 x < A 2 1 x :=
    A_lt 11 8 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t3 : A 11 8 x < A 3 2 x :=
    A_lt 11 8 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t9 : A 11 8 x < A 9 7 x :=
    A_lt 11 8 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t3 : A 2 1 x < A 3 2 x :=
    A_lt 2 1 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t9 : A 2 1 x < A 9 7 x :=
    A_lt 2 1 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_t9 : A 3 2 x < A 9 7 x :=
    A_lt 3 2 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have z_t10 : 0 < A 10 7 x :=
    A_pos 10 7 _ _ x hx1 hx2 (by decide +kernel)
  have o_t10 : A 10 7 x < 1 :=
    A_lt_one 10 7 _ _ x hx1 hx2 (by decide +kernel)
  have z_t9 : 0 < A 9 7 x :=
    A_pos 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have o_t9 : A 9 7 x < 1 :=
    A_lt_one 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have z_t11 : 0 < A 11 8 x :=
    A_pos 11 8 _ _ x hx1 hx2 (by decide +kernel)
  have o_t11 : A 11 8 x < 1 :=
    A_lt_one 11 8 _ _ x hx1 hx2 (by decide +kernel)
  have z_t2 : 0 < A 2 1 x :=
    A_pos 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have o_t2 : A 2 1 x < 1 :=
    A_lt_one 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have z_t1 : 0 < A 1 0 x :=
    A_pos 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t1 : A 1 0 x < 1 :=
    A_lt_one 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t3 : 0 < A 3 2 x :=
    A_pos 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have o_t3 : A 3 2 x < 1 :=
    A_lt_one 3 2 _ _ x hx1 hx2 (by decide +kernel)
  refine phi_eq x 0 ?_ ?_
  · intro y _ _
    exact rho_nonneg x y
  · refine ⟨A 3 2 x, z_t3.le, o_t3, ?_⟩
    rw [D _ z_t3.le o_t3]
    simp only [Ival, not_lt.2 (f_t3_s).le, (f_t10_t3).le, not_le.2 f_t3_t9, (f_t11_t3).le,
        (f_t2_t3).le, (f_t1_t3).le, le_refl]
    decide

theorem cell_75 (x : ℝ) (hx1 : ((4 / 5 : ℚ) : ℝ) < x) (hx2 : x < ((17 / 21 : ℚ) : ℝ)) :
    phi x = 0 := by
  have f11 := floor_bounds 11 8 _ _ x hx1 hx2 (by decide +kernel)
  have f10 := floor_bounds 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f9 := floor_bounds 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f8 := floor_bounds 8 6 _ _ x hx1 hx2 (by decide +kernel)
  have f2 := floor_bounds 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f1 := floor_bounds 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f3 := floor_bounds 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have D := rho_decomp x 8 8 7 6 1 0 2 f11 f10 f9 f8 f2 f1 f3
  have hs0 := s_nonneg 8 x f11
  have hs1 := s_lt_one 8 x f11
  have f_t1_s : A 1 0 x < A (-11) (-8 - 1) x :=
    A_lt 1 0 (-11) (-8 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t10 : A (-11) (-8 - 1) x < A 10 8 x :=
    A_lt (-11) (-8 - 1) 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_s : A 11 8 x < A (-11) (-8 - 1) x :=
    A_lt 11 8 (-11) (-8 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_s : A 2 1 x < A (-11) (-8 - 1) x :=
    A_lt 2 1 (-11) (-8 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_s : A 3 2 x < A (-11) (-8 - 1) x :=
    A_lt 3 2 (-11) (-8 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_s : A 9 7 x < A (-11) (-8 - 1) x :=
    A_lt 9 7 (-11) (-8 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t10 : A 1 0 x < A 10 8 x :=
    A_lt 1 0 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t1 : A 11 8 x < A 1 0 x :=
    A_lt 11 8 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t2 : A 1 0 x < A 2 1 x :=
    A_lt 1 0 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t3 : A 1 0 x < A 3 2 x :=
    A_lt 1 0 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t9 : A 1 0 x < A 9 7 x :=
    A_lt 1 0 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t10 : A 11 8 x < A 10 8 x :=
    A_lt 11 8 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t10 : A 2 1 x < A 10 8 x :=
    A_lt 2 1 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_t10 : A 3 2 x < A 10 8 x :=
    A_lt 3 2 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t10 : A 9 7 x < A 10 8 x :=
    A_lt 9 7 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t2 : A 11 8 x < A 2 1 x :=
    A_lt 11 8 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t3 : A 11 8 x < A 3 2 x :=
    A_lt 11 8 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t9 : A 11 8 x < A 9 7 x :=
    A_lt 11 8 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t3 : A 2 1 x < A 3 2 x :=
    A_lt 2 1 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t9 : A 2 1 x < A 9 7 x :=
    A_lt 2 1 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_t9 : A 3 2 x < A 9 7 x :=
    A_lt 3 2 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have z_t10 : 0 < A 10 8 x :=
    A_pos 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have o_t10 : A 10 8 x < 1 :=
    A_lt_one 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have z_t9 : 0 < A 9 7 x :=
    A_pos 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have o_t9 : A 9 7 x < 1 :=
    A_lt_one 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have z_t11 : 0 < A 11 8 x :=
    A_pos 11 8 _ _ x hx1 hx2 (by decide +kernel)
  have o_t11 : A 11 8 x < 1 :=
    A_lt_one 11 8 _ _ x hx1 hx2 (by decide +kernel)
  have z_t2 : 0 < A 2 1 x :=
    A_pos 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have o_t2 : A 2 1 x < 1 :=
    A_lt_one 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have z_t1 : 0 < A 1 0 x :=
    A_pos 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t1 : A 1 0 x < 1 :=
    A_lt_one 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t3 : 0 < A 3 2 x :=
    A_pos 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have o_t3 : A 3 2 x < 1 :=
    A_lt_one 3 2 _ _ x hx1 hx2 (by decide +kernel)
  refine phi_eq x 0 ?_ ?_
  · intro y _ _
    exact rho_nonneg x y
  · refine ⟨A 3 2 x, z_t3.le, o_t3, ?_⟩
    rw [D _ z_t3.le o_t3]
    simp only [Ival, not_lt.2 (f_t3_s).le, not_le.2 f_t3_t10, not_le.2 f_t3_t9, (f_t11_t3).le,
        (f_t2_t3).le, (f_t1_t3).le, le_refl]
    decide

theorem cell_76 (x : ℝ) (hx1 : ((17 / 21 : ℚ) : ℝ) < x) (hx2 : x < ((9 / 11 : ℚ) : ℝ)) :
    phi x = 0 := by
  have f11 := floor_bounds 11 8 _ _ x hx1 hx2 (by decide +kernel)
  have f10 := floor_bounds 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f9 := floor_bounds 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f8 := floor_bounds 8 6 _ _ x hx1 hx2 (by decide +kernel)
  have f2 := floor_bounds 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f1 := floor_bounds 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f3 := floor_bounds 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have D := rho_decomp x 8 8 7 6 1 0 2 f11 f10 f9 f8 f2 f1 f3
  have hs0 := s_nonneg 8 x f11
  have hs1 := s_lt_one 8 x f11
  have f_t1_s : A 1 0 x < A (-11) (-8 - 1) x :=
    A_lt 1 0 (-11) (-8 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_s : A 10 8 x < A (-11) (-8 - 1) x :=
    A_lt 10 8 (-11) (-8 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_s : A 11 8 x < A (-11) (-8 - 1) x :=
    A_lt 11 8 (-11) (-8 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_s : A 2 1 x < A (-11) (-8 - 1) x :=
    A_lt 2 1 (-11) (-8 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_s : A 3 2 x < A (-11) (-8 - 1) x :=
    A_lt 3 2 (-11) (-8 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_s : A 9 7 x < A (-11) (-8 - 1) x :=
    A_lt 9 7 (-11) (-8 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t10 : A 1 0 x < A 10 8 x :=
    A_lt 1 0 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t1 : A 11 8 x < A 1 0 x :=
    A_lt 11 8 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t2 : A 1 0 x < A 2 1 x :=
    A_lt 1 0 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t3 : A 1 0 x < A 3 2 x :=
    A_lt 1 0 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t9 : A 1 0 x < A 9 7 x :=
    A_lt 1 0 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t10 : A 11 8 x < A 10 8 x :=
    A_lt 11 8 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t10 : A 2 1 x < A 10 8 x :=
    A_lt 2 1 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_t10 : A 3 2 x < A 10 8 x :=
    A_lt 3 2 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t10 : A 9 7 x < A 10 8 x :=
    A_lt 9 7 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t2 : A 11 8 x < A 2 1 x :=
    A_lt 11 8 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t3 : A 11 8 x < A 3 2 x :=
    A_lt 11 8 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t9 : A 11 8 x < A 9 7 x :=
    A_lt 11 8 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t3 : A 2 1 x < A 3 2 x :=
    A_lt 2 1 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t9 : A 2 1 x < A 9 7 x :=
    A_lt 2 1 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_t9 : A 3 2 x < A 9 7 x :=
    A_lt 3 2 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have z_t10 : 0 < A 10 8 x :=
    A_pos 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have o_t10 : A 10 8 x < 1 :=
    A_lt_one 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have z_t9 : 0 < A 9 7 x :=
    A_pos 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have o_t9 : A 9 7 x < 1 :=
    A_lt_one 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have z_t11 : 0 < A 11 8 x :=
    A_pos 11 8 _ _ x hx1 hx2 (by decide +kernel)
  have o_t11 : A 11 8 x < 1 :=
    A_lt_one 11 8 _ _ x hx1 hx2 (by decide +kernel)
  have z_t2 : 0 < A 2 1 x :=
    A_pos 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have o_t2 : A 2 1 x < 1 :=
    A_lt_one 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have z_t1 : 0 < A 1 0 x :=
    A_pos 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t1 : A 1 0 x < 1 :=
    A_lt_one 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t3 : 0 < A 3 2 x :=
    A_pos 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have o_t3 : A 3 2 x < 1 :=
    A_lt_one 3 2 _ _ x hx1 hx2 (by decide +kernel)
  refine phi_eq x 0 ?_ ?_
  · intro y _ _
    exact rho_nonneg x y
  · refine ⟨A 3 2 x, z_t3.le, o_t3, ?_⟩
    rw [D _ z_t3.le o_t3]
    simp only [Ival, not_lt.2 (f_t3_s).le, not_le.2 f_t3_t10, not_le.2 f_t3_t9, (f_t11_t3).le,
        (f_t2_t3).le, (f_t1_t3).le, le_refl]
    decide

theorem cell_77 (x : ℝ) (hx1 : ((9 / 11 : ℚ) : ℝ) < x) (hx2 : x < ((5 / 6 : ℚ) : ℝ)) :
    phi x = 1 := by
  have f11 := floor_bounds 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f10 := floor_bounds 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f9 := floor_bounds 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f8 := floor_bounds 8 6 _ _ x hx1 hx2 (by decide +kernel)
  have f2 := floor_bounds 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f1 := floor_bounds 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f3 := floor_bounds 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have D := rho_decomp x 9 8 7 6 1 0 2 f11 f10 f9 f8 f2 f1 f3
  have hs0 := s_nonneg 9 x f11
  have hs1 := s_lt_one 9 x f11
  have f_s_t1 : A (-11) (-9 - 1) x < A 1 0 x :=
    A_lt (-11) (-9 - 1) 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t10 : A (-11) (-9 - 1) x < A 10 8 x :=
    A_lt (-11) (-9 - 1) 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t11 : A (-11) (-9 - 1) x < A 11 9 x :=
    A_lt (-11) (-9 - 1) 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t2 : A (-11) (-9 - 1) x < A 2 1 x :=
    A_lt (-11) (-9 - 1) 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t3 : A (-11) (-9 - 1) x < A 3 2 x :=
    A_lt (-11) (-9 - 1) 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t9 : A (-11) (-9 - 1) x < A 9 7 x :=
    A_lt (-11) (-9 - 1) 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t10 : A 1 0 x < A 10 8 x :=
    A_lt 1 0 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t11 : A 1 0 x < A 11 9 x :=
    A_lt 1 0 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t2 : A 1 0 x < A 2 1 x :=
    A_lt 1 0 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t3 : A 1 0 x < A 3 2 x :=
    A_lt 1 0 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t9 : A 1 0 x < A 9 7 x :=
    A_lt 1 0 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t11 : A 10 8 x < A 11 9 x :=
    A_lt 10 8 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t10 : A 2 1 x < A 10 8 x :=
    A_lt 2 1 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_t10 : A 3 2 x < A 10 8 x :=
    A_lt 3 2 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t10 : A 9 7 x < A 10 8 x :=
    A_lt 9 7 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t11 : A 2 1 x < A 11 9 x :=
    A_lt 2 1 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_t11 : A 3 2 x < A 11 9 x :=
    A_lt 3 2 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t11 : A 9 7 x < A 11 9 x :=
    A_lt 9 7 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t3 : A 2 1 x < A 3 2 x :=
    A_lt 2 1 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t9 : A 2 1 x < A 9 7 x :=
    A_lt 2 1 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_t9 : A 3 2 x < A 9 7 x :=
    A_lt 3 2 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have z_t10 : 0 < A 10 8 x :=
    A_pos 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have o_t10 : A 10 8 x < 1 :=
    A_lt_one 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have z_t9 : 0 < A 9 7 x :=
    A_pos 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have o_t9 : A 9 7 x < 1 :=
    A_lt_one 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have z_t11 : 0 < A 11 9 x :=
    A_pos 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have o_t11 : A 11 9 x < 1 :=
    A_lt_one 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have z_t2 : 0 < A 2 1 x :=
    A_pos 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have o_t2 : A 2 1 x < 1 :=
    A_lt_one 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have z_t1 : 0 < A 1 0 x :=
    A_pos 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t1 : A 1 0 x < 1 :=
    A_lt_one 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t3 : 0 < A 3 2 x :=
    A_pos 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have o_t3 : A 3 2 x < 1 :=
    A_lt_one 3 2 _ _ x hx1 hx2 (by decide +kernel)
  refine phi_eq x 1 ?_ ?_
  · intro y hy0 hy1
    rw [D y hy0 hy1]
    have := Ival_ge x 9 8 7 1 0 2 (1 - (3)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ y hy0
      hy1
    · omega
    · simp only [Ival, not_lt.2 hs0, not_le.2 z_t10, not_le.2 z_t9, not_le.2 z_t11,
        not_le.2 z_t2, not_le.2 z_t1, not_le.2 z_t3]
      decide
    · intro _ _
      simp only [Ival, f_s_t10, (f_t9_t10).le, not_le.2 f_t10_t11, (f_t2_t10).le, (f_t1_t10).le,
        (f_t3_t10).le, le_refl]
      decide
    · intro _ _
      simp only [Ival, f_s_t9, not_le.2 f_t9_t10, not_le.2 f_t9_t11, (f_t2_t9).le, (f_t1_t9).le,
        (f_t3_t9).le, le_refl]
      decide
    · intro _ _
      simp only [Ival, f_s_t11, (f_t10_t11).le, (f_t9_t11).le, (f_t2_t11).le, (f_t1_t11).le,
        (f_t3_t11).le, le_refl]
      decide
    · intro _ _
      simp only [Ival, f_s_t2, not_le.2 f_t2_t10, not_le.2 f_t2_t9, not_le.2 f_t2_t11,
        (f_t1_t2).le, not_le.2 f_t2_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, f_s_t1, not_le.2 f_t1_t10, not_le.2 f_t1_t9, not_le.2 f_t1_t11,
        not_le.2 f_t1_t2, not_le.2 f_t1_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, f_s_t3, not_le.2 f_t3_t10, not_le.2 f_t3_t9, not_le.2 f_t3_t11,
        (f_t2_t3).le, (f_t1_t3).le, le_refl]
      decide
    · simp only [Ip, not_le.2 f_s_t10, not_le.2 f_s_t9, not_le.2 f_s_t11, not_le.2 f_s_t2,
        not_le.2 f_s_t1, not_le.2 f_s_t3]
      decide
  · refine ⟨A 3 2 x, z_t3.le, o_t3, ?_⟩
    rw [D _ z_t3.le o_t3]
    simp only [Ival, f_s_t3, not_le.2 f_t3_t10, not_le.2 f_t3_t9, not_le.2 f_t3_t11,
        (f_t2_t3).le, (f_t1_t3).le, le_refl]
    decide

theorem cell_78 (x : ℝ) (hx1 : ((5 / 6 : ℚ) : ℝ) < x) (hx2 : x < ((11 / 13 : ℚ) : ℝ)) :
    phi x = 2 := by
  have f11 := floor_bounds 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f10 := floor_bounds 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f9 := floor_bounds 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f8 := floor_bounds 8 6 _ _ x hx1 hx2 (by decide +kernel)
  have f2 := floor_bounds 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f1 := floor_bounds 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f3 := floor_bounds 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have D := rho_decomp x 9 8 7 6 1 0 2 f11 f10 f9 f8 f2 f1 f3
  have hs0 := s_nonneg 9 x f11
  have hs1 := s_lt_one 9 x f11
  have f_t1_s : A 1 0 x < A (-11) (-9 - 1) x :=
    A_lt 1 0 (-11) (-9 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t10 : A (-11) (-9 - 1) x < A 10 8 x :=
    A_lt (-11) (-9 - 1) 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t11 : A (-11) (-9 - 1) x < A 11 9 x :=
    A_lt (-11) (-9 - 1) 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t2 : A (-11) (-9 - 1) x < A 2 1 x :=
    A_lt (-11) (-9 - 1) 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t3 : A (-11) (-9 - 1) x < A 3 2 x :=
    A_lt (-11) (-9 - 1) 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t9 : A (-11) (-9 - 1) x < A 9 7 x :=
    A_lt (-11) (-9 - 1) 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t10 : A 1 0 x < A 10 8 x :=
    A_lt 1 0 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t11 : A 1 0 x < A 11 9 x :=
    A_lt 1 0 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t2 : A 1 0 x < A 2 1 x :=
    A_lt 1 0 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t3 : A 1 0 x < A 3 2 x :=
    A_lt 1 0 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t9 : A 1 0 x < A 9 7 x :=
    A_lt 1 0 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t11 : A 10 8 x < A 11 9 x :=
    A_lt 10 8 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t10 : A 2 1 x < A 10 8 x :=
    A_lt 2 1 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_t10 : A 3 2 x < A 10 8 x :=
    A_lt 3 2 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t10 : A 9 7 x < A 10 8 x :=
    A_lt 9 7 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t11 : A 2 1 x < A 11 9 x :=
    A_lt 2 1 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_t11 : A 3 2 x < A 11 9 x :=
    A_lt 3 2 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t11 : A 9 7 x < A 11 9 x :=
    A_lt 9 7 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t3 : A 2 1 x < A 3 2 x :=
    A_lt 2 1 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t9 : A 2 1 x < A 9 7 x :=
    A_lt 2 1 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t3 : A 9 7 x < A 3 2 x :=
    A_lt 9 7 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have z_t10 : 0 < A 10 8 x :=
    A_pos 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have o_t10 : A 10 8 x < 1 :=
    A_lt_one 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have z_t9 : 0 < A 9 7 x :=
    A_pos 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have o_t9 : A 9 7 x < 1 :=
    A_lt_one 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have z_t11 : 0 < A 11 9 x :=
    A_pos 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have o_t11 : A 11 9 x < 1 :=
    A_lt_one 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have z_t2 : 0 < A 2 1 x :=
    A_pos 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have o_t2 : A 2 1 x < 1 :=
    A_lt_one 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have z_t1 : 0 < A 1 0 x :=
    A_pos 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t1 : A 1 0 x < 1 :=
    A_lt_one 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t3 : 0 < A 3 2 x :=
    A_pos 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have o_t3 : A 3 2 x < 1 :=
    A_lt_one 3 2 _ _ x hx1 hx2 (by decide +kernel)
  refine phi_eq x 2 ?_ ?_
  · intro y hy0 hy1
    rw [D y hy0 hy1]
    have := Ival_ge x 9 8 7 1 0 2 (2 - (3)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ y hy0
      hy1
    · omega
    · simp only [Ival, not_lt.2 hs0, not_le.2 z_t10, not_le.2 z_t9, not_le.2 z_t11,
        not_le.2 z_t2, not_le.2 z_t1, not_le.2 z_t3]
      decide
    · intro _ _
      simp only [Ival, f_s_t10, (f_t9_t10).le, not_le.2 f_t10_t11, (f_t2_t10).le, (f_t1_t10).le,
        (f_t3_t10).le, le_refl]
      decide
    · intro _ _
      simp only [Ival, f_s_t9, not_le.2 f_t9_t10, not_le.2 f_t9_t11, (f_t2_t9).le, (f_t1_t9).le,
        not_le.2 f_t9_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, f_s_t11, (f_t10_t11).le, (f_t9_t11).le, (f_t2_t11).le, (f_t1_t11).le,
        (f_t3_t11).le, le_refl]
      decide
    · intro _ _
      simp only [Ival, f_s_t2, not_le.2 f_t2_t10, not_le.2 f_t2_t9, not_le.2 f_t2_t11,
        (f_t1_t2).le, not_le.2 f_t2_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t1_s).le, not_le.2 f_t1_t10, not_le.2 f_t1_t9,
        not_le.2 f_t1_t11, not_le.2 f_t1_t2, not_le.2 f_t1_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, f_s_t3, not_le.2 f_t3_t10, (f_t9_t3).le, not_le.2 f_t3_t11, (f_t2_t3).le,
        (f_t1_t3).le, le_refl]
      decide
    · simp only [Ip, not_le.2 f_s_t10, not_le.2 f_s_t9, not_le.2 f_s_t11, not_le.2 f_s_t2,
        (f_t1_s).le, not_le.2 f_s_t3]
      decide
  · refine ⟨A 2 1 x, z_t2.le, o_t2, ?_⟩
    rw [D _ z_t2.le o_t2]
    simp only [Ival, f_s_t2, not_le.2 f_t2_t10, not_le.2 f_t2_t9, not_le.2 f_t2_t11,
        (f_t1_t2).le, not_le.2 f_t2_t3, le_refl]
    decide

theorem cell_79 (x : ℝ) (hx1 : ((11 / 13 : ℚ) : ℝ) < x) (hx2 : x < ((17 / 20 : ℚ) : ℝ)) :
    phi x = 1 := by
  have f11 := floor_bounds 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f10 := floor_bounds 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f9 := floor_bounds 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f8 := floor_bounds 8 6 _ _ x hx1 hx2 (by decide +kernel)
  have f2 := floor_bounds 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f1 := floor_bounds 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f3 := floor_bounds 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have D := rho_decomp x 9 8 7 6 1 0 2 f11 f10 f9 f8 f2 f1 f3
  have hs0 := s_nonneg 9 x f11
  have hs1 := s_lt_one 9 x f11
  have f_t1_s : A 1 0 x < A (-11) (-9 - 1) x :=
    A_lt 1 0 (-11) (-9 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t10 : A (-11) (-9 - 1) x < A 10 8 x :=
    A_lt (-11) (-9 - 1) 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t11 : A (-11) (-9 - 1) x < A 11 9 x :=
    A_lt (-11) (-9 - 1) 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_s : A 2 1 x < A (-11) (-9 - 1) x :=
    A_lt 2 1 (-11) (-9 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t3 : A (-11) (-9 - 1) x < A 3 2 x :=
    A_lt (-11) (-9 - 1) 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t9 : A (-11) (-9 - 1) x < A 9 7 x :=
    A_lt (-11) (-9 - 1) 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t10 : A 1 0 x < A 10 8 x :=
    A_lt 1 0 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t11 : A 1 0 x < A 11 9 x :=
    A_lt 1 0 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t2 : A 1 0 x < A 2 1 x :=
    A_lt 1 0 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t3 : A 1 0 x < A 3 2 x :=
    A_lt 1 0 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t9 : A 1 0 x < A 9 7 x :=
    A_lt 1 0 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t11 : A 10 8 x < A 11 9 x :=
    A_lt 10 8 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t10 : A 2 1 x < A 10 8 x :=
    A_lt 2 1 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_t10 : A 3 2 x < A 10 8 x :=
    A_lt 3 2 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t10 : A 9 7 x < A 10 8 x :=
    A_lt 9 7 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t11 : A 2 1 x < A 11 9 x :=
    A_lt 2 1 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_t11 : A 3 2 x < A 11 9 x :=
    A_lt 3 2 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t11 : A 9 7 x < A 11 9 x :=
    A_lt 9 7 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t3 : A 2 1 x < A 3 2 x :=
    A_lt 2 1 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t9 : A 2 1 x < A 9 7 x :=
    A_lt 2 1 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t3 : A 9 7 x < A 3 2 x :=
    A_lt 9 7 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have z_t10 : 0 < A 10 8 x :=
    A_pos 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have o_t10 : A 10 8 x < 1 :=
    A_lt_one 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have z_t9 : 0 < A 9 7 x :=
    A_pos 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have o_t9 : A 9 7 x < 1 :=
    A_lt_one 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have z_t11 : 0 < A 11 9 x :=
    A_pos 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have o_t11 : A 11 9 x < 1 :=
    A_lt_one 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have z_t2 : 0 < A 2 1 x :=
    A_pos 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have o_t2 : A 2 1 x < 1 :=
    A_lt_one 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have z_t1 : 0 < A 1 0 x :=
    A_pos 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t1 : A 1 0 x < 1 :=
    A_lt_one 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t3 : 0 < A 3 2 x :=
    A_pos 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have o_t3 : A 3 2 x < 1 :=
    A_lt_one 3 2 _ _ x hx1 hx2 (by decide +kernel)
  refine phi_eq x 1 ?_ ?_
  · intro y hy0 hy1
    rw [D y hy0 hy1]
    have := Ival_ge x 9 8 7 1 0 2 (1 - (3)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ y hy0
      hy1
    · omega
    · simp only [Ival, not_lt.2 hs0, not_le.2 z_t10, not_le.2 z_t9, not_le.2 z_t11,
        not_le.2 z_t2, not_le.2 z_t1, not_le.2 z_t3]
      decide
    · intro _ _
      simp only [Ival, f_s_t10, (f_t9_t10).le, not_le.2 f_t10_t11, (f_t2_t10).le, (f_t1_t10).le,
        (f_t3_t10).le, le_refl]
      decide
    · intro _ _
      simp only [Ival, f_s_t9, not_le.2 f_t9_t10, not_le.2 f_t9_t11, (f_t2_t9).le, (f_t1_t9).le,
        not_le.2 f_t9_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, f_s_t11, (f_t10_t11).le, (f_t9_t11).le, (f_t2_t11).le, (f_t1_t11).le,
        (f_t3_t11).le, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t2_s).le, not_le.2 f_t2_t10, not_le.2 f_t2_t9,
        not_le.2 f_t2_t11, (f_t1_t2).le, not_le.2 f_t2_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t1_s).le, not_le.2 f_t1_t10, not_le.2 f_t1_t9,
        not_le.2 f_t1_t11, not_le.2 f_t1_t2, not_le.2 f_t1_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, f_s_t3, not_le.2 f_t3_t10, (f_t9_t3).le, not_le.2 f_t3_t11, (f_t2_t3).le,
        (f_t1_t3).le, le_refl]
      decide
    · simp only [Ip, not_le.2 f_s_t10, not_le.2 f_s_t9, not_le.2 f_s_t11, (f_t2_s).le,
        (f_t1_s).le, not_le.2 f_s_t3]
      decide
  · refine ⟨A 2 1 x, z_t2.le, o_t2, ?_⟩
    rw [D _ z_t2.le o_t2]
    simp only [Ival, not_lt.2 (f_t2_s).le, not_le.2 f_t2_t10, not_le.2 f_t2_t9,
        not_le.2 f_t2_t11, (f_t1_t2).le, not_le.2 f_t2_t3, le_refl]
    decide

theorem cell_80 (x : ℝ) (hx1 : ((17 / 20 : ℚ) : ℝ) < x) (hx2 : x < ((6 / 7 : ℚ) : ℝ)) :
    phi x = 1 := by
  have f11 := floor_bounds 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f10 := floor_bounds 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f9 := floor_bounds 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f8 := floor_bounds 8 6 _ _ x hx1 hx2 (by decide +kernel)
  have f2 := floor_bounds 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f1 := floor_bounds 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f3 := floor_bounds 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have D := rho_decomp x 9 8 7 6 1 0 2 f11 f10 f9 f8 f2 f1 f3
  have hs0 := s_nonneg 9 x f11
  have hs1 := s_lt_one 9 x f11
  have f_t1_s : A 1 0 x < A (-11) (-9 - 1) x :=
    A_lt 1 0 (-11) (-9 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t10 : A (-11) (-9 - 1) x < A 10 8 x :=
    A_lt (-11) (-9 - 1) 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t11 : A (-11) (-9 - 1) x < A 11 9 x :=
    A_lt (-11) (-9 - 1) 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_s : A 2 1 x < A (-11) (-9 - 1) x :=
    A_lt 2 1 (-11) (-9 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t3 : A (-11) (-9 - 1) x < A 3 2 x :=
    A_lt (-11) (-9 - 1) 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_s : A 9 7 x < A (-11) (-9 - 1) x :=
    A_lt 9 7 (-11) (-9 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t10 : A 1 0 x < A 10 8 x :=
    A_lt 1 0 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t11 : A 1 0 x < A 11 9 x :=
    A_lt 1 0 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t2 : A 1 0 x < A 2 1 x :=
    A_lt 1 0 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t3 : A 1 0 x < A 3 2 x :=
    A_lt 1 0 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t9 : A 1 0 x < A 9 7 x :=
    A_lt 1 0 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t11 : A 10 8 x < A 11 9 x :=
    A_lt 10 8 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t10 : A 2 1 x < A 10 8 x :=
    A_lt 2 1 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_t10 : A 3 2 x < A 10 8 x :=
    A_lt 3 2 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t10 : A 9 7 x < A 10 8 x :=
    A_lt 9 7 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t11 : A 2 1 x < A 11 9 x :=
    A_lt 2 1 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_t11 : A 3 2 x < A 11 9 x :=
    A_lt 3 2 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t11 : A 9 7 x < A 11 9 x :=
    A_lt 9 7 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t3 : A 2 1 x < A 3 2 x :=
    A_lt 2 1 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t9 : A 2 1 x < A 9 7 x :=
    A_lt 2 1 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t3 : A 9 7 x < A 3 2 x :=
    A_lt 9 7 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have z_t10 : 0 < A 10 8 x :=
    A_pos 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have o_t10 : A 10 8 x < 1 :=
    A_lt_one 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have z_t9 : 0 < A 9 7 x :=
    A_pos 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have o_t9 : A 9 7 x < 1 :=
    A_lt_one 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have z_t11 : 0 < A 11 9 x :=
    A_pos 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have o_t11 : A 11 9 x < 1 :=
    A_lt_one 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have z_t2 : 0 < A 2 1 x :=
    A_pos 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have o_t2 : A 2 1 x < 1 :=
    A_lt_one 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have z_t1 : 0 < A 1 0 x :=
    A_pos 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t1 : A 1 0 x < 1 :=
    A_lt_one 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t3 : 0 < A 3 2 x :=
    A_pos 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have o_t3 : A 3 2 x < 1 :=
    A_lt_one 3 2 _ _ x hx1 hx2 (by decide +kernel)
  refine phi_eq x 1 ?_ ?_
  · intro y hy0 hy1
    rw [D y hy0 hy1]
    have := Ival_ge x 9 8 7 1 0 2 (1 - (3)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ y hy0
      hy1
    · omega
    · simp only [Ival, not_lt.2 hs0, not_le.2 z_t10, not_le.2 z_t9, not_le.2 z_t11,
        not_le.2 z_t2, not_le.2 z_t1, not_le.2 z_t3]
      decide
    · intro _ _
      simp only [Ival, f_s_t10, (f_t9_t10).le, not_le.2 f_t10_t11, (f_t2_t10).le, (f_t1_t10).le,
        (f_t3_t10).le, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t9_s).le, not_le.2 f_t9_t10, not_le.2 f_t9_t11, (f_t2_t9).le,
        (f_t1_t9).le, not_le.2 f_t9_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, f_s_t11, (f_t10_t11).le, (f_t9_t11).le, (f_t2_t11).le, (f_t1_t11).le,
        (f_t3_t11).le, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t2_s).le, not_le.2 f_t2_t10, not_le.2 f_t2_t9,
        not_le.2 f_t2_t11, (f_t1_t2).le, not_le.2 f_t2_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t1_s).le, not_le.2 f_t1_t10, not_le.2 f_t1_t9,
        not_le.2 f_t1_t11, not_le.2 f_t1_t2, not_le.2 f_t1_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, f_s_t3, not_le.2 f_t3_t10, (f_t9_t3).le, not_le.2 f_t3_t11, (f_t2_t3).le,
        (f_t1_t3).le, le_refl]
      decide
    · simp only [Ip, not_le.2 f_s_t10, (f_t9_s).le, not_le.2 f_s_t11, (f_t2_s).le, (f_t1_s).le,
        not_le.2 f_s_t3]
      decide
  · refine ⟨A 2 1 x, z_t2.le, o_t2, ?_⟩
    rw [D _ z_t2.le o_t2]
    simp only [Ival, not_lt.2 (f_t2_s).le, not_le.2 f_t2_t10, not_le.2 f_t2_t9,
        not_le.2 f_t2_t11, (f_t1_t2).le, not_le.2 f_t2_t3, le_refl]
    decide

theorem cell_81 (x : ℝ) (hx1 : ((6 / 7 : ℚ) : ℝ) < x) (hx2 : x < ((19 / 22 : ℚ) : ℝ)) :
    phi x = 2 := by
  have f11 := floor_bounds 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f10 := floor_bounds 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f9 := floor_bounds 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f8 := floor_bounds 8 6 _ _ x hx1 hx2 (by decide +kernel)
  have f2 := floor_bounds 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f1 := floor_bounds 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f3 := floor_bounds 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have D := rho_decomp x 9 8 7 6 1 0 2 f11 f10 f9 f8 f2 f1 f3
  have hs0 := s_nonneg 9 x f11
  have hs1 := s_lt_one 9 x f11
  have f_t1_s : A 1 0 x < A (-11) (-9 - 1) x :=
    A_lt 1 0 (-11) (-9 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_s : A 10 8 x < A (-11) (-9 - 1) x :=
    A_lt 10 8 (-11) (-9 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_s_t11 : A (-11) (-9 - 1) x < A 11 9 x :=
    A_lt (-11) (-9 - 1) 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_s : A 2 1 x < A (-11) (-9 - 1) x :=
    A_lt 2 1 (-11) (-9 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_s : A 3 2 x < A (-11) (-9 - 1) x :=
    A_lt 3 2 (-11) (-9 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_s : A 9 7 x < A (-11) (-9 - 1) x :=
    A_lt 9 7 (-11) (-9 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t10 : A 1 0 x < A 10 8 x :=
    A_lt 1 0 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t11 : A 1 0 x < A 11 9 x :=
    A_lt 1 0 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t2 : A 1 0 x < A 2 1 x :=
    A_lt 1 0 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t3 : A 1 0 x < A 3 2 x :=
    A_lt 1 0 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t9 : A 1 0 x < A 9 7 x :=
    A_lt 1 0 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t11 : A 10 8 x < A 11 9 x :=
    A_lt 10 8 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t10 : A 2 1 x < A 10 8 x :=
    A_lt 2 1 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t3 : A 10 8 x < A 3 2 x :=
    A_lt 10 8 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t10 : A 9 7 x < A 10 8 x :=
    A_lt 9 7 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t11 : A 2 1 x < A 11 9 x :=
    A_lt 2 1 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_t11 : A 3 2 x < A 11 9 x :=
    A_lt 3 2 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t11 : A 9 7 x < A 11 9 x :=
    A_lt 9 7 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t3 : A 2 1 x < A 3 2 x :=
    A_lt 2 1 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t2 : A 9 7 x < A 2 1 x :=
    A_lt 9 7 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t3 : A 9 7 x < A 3 2 x :=
    A_lt 9 7 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have z_t10 : 0 < A 10 8 x :=
    A_pos 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have o_t10 : A 10 8 x < 1 :=
    A_lt_one 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have z_t9 : 0 < A 9 7 x :=
    A_pos 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have o_t9 : A 9 7 x < 1 :=
    A_lt_one 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have z_t11 : 0 < A 11 9 x :=
    A_pos 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have o_t11 : A 11 9 x < 1 :=
    A_lt_one 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have z_t2 : 0 < A 2 1 x :=
    A_pos 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have o_t2 : A 2 1 x < 1 :=
    A_lt_one 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have z_t1 : 0 < A 1 0 x :=
    A_pos 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t1 : A 1 0 x < 1 :=
    A_lt_one 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t3 : 0 < A 3 2 x :=
    A_pos 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have o_t3 : A 3 2 x < 1 :=
    A_lt_one 3 2 _ _ x hx1 hx2 (by decide +kernel)
  refine phi_eq x 2 ?_ ?_
  · intro y hy0 hy1
    rw [D y hy0 hy1]
    have := Ival_ge x 9 8 7 1 0 2 (2 - (3)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ y hy0
      hy1
    · omega
    · simp only [Ival, not_lt.2 hs0, not_le.2 z_t10, not_le.2 z_t9, not_le.2 z_t11,
        not_le.2 z_t2, not_le.2 z_t1, not_le.2 z_t3]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t10_s).le, (f_t9_t10).le, not_le.2 f_t10_t11, (f_t2_t10).le,
        (f_t1_t10).le, not_le.2 f_t10_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t9_s).le, not_le.2 f_t9_t10, not_le.2 f_t9_t11,
        not_le.2 f_t9_t2, (f_t1_t9).le, not_le.2 f_t9_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, f_s_t11, (f_t10_t11).le, (f_t9_t11).le, (f_t2_t11).le, (f_t1_t11).le,
        (f_t3_t11).le, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t2_s).le, not_le.2 f_t2_t10, (f_t9_t2).le, not_le.2 f_t2_t11,
        (f_t1_t2).le, not_le.2 f_t2_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t1_s).le, not_le.2 f_t1_t10, not_le.2 f_t1_t9,
        not_le.2 f_t1_t11, not_le.2 f_t1_t2, not_le.2 f_t1_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t3_s).le, (f_t10_t3).le, (f_t9_t3).le, not_le.2 f_t3_t11,
        (f_t2_t3).le, (f_t1_t3).le, le_refl]
      decide
    · simp only [Ip, (f_t10_s).le, (f_t9_s).le, not_le.2 f_s_t11, (f_t2_s).le, (f_t1_s).le,
        (f_t3_s).le]
      decide
  · refine ⟨A 2 1 x, z_t2.le, o_t2, ?_⟩
    rw [D _ z_t2.le o_t2]
    simp only [Ival, not_lt.2 (f_t2_s).le, not_le.2 f_t2_t10, (f_t9_t2).le, not_le.2 f_t2_t11,
        (f_t1_t2).le, not_le.2 f_t2_t3, le_refl]
    decide

theorem cell_82 (x : ℝ) (hx1 : ((19 / 22 : ℚ) : ℝ) < x) (hx2 : x < ((7 / 8 : ℚ) : ℝ)) :
    phi x = 2 := by
  have f11 := floor_bounds 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f10 := floor_bounds 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f9 := floor_bounds 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f8 := floor_bounds 8 6 _ _ x hx1 hx2 (by decide +kernel)
  have f2 := floor_bounds 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f1 := floor_bounds 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f3 := floor_bounds 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have D := rho_decomp x 9 8 7 6 1 0 2 f11 f10 f9 f8 f2 f1 f3
  have hs0 := s_nonneg 9 x f11
  have hs1 := s_lt_one 9 x f11
  have f_t1_s : A 1 0 x < A (-11) (-9 - 1) x :=
    A_lt 1 0 (-11) (-9 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_s : A 10 8 x < A (-11) (-9 - 1) x :=
    A_lt 10 8 (-11) (-9 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_s : A 11 9 x < A (-11) (-9 - 1) x :=
    A_lt 11 9 (-11) (-9 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_s : A 2 1 x < A (-11) (-9 - 1) x :=
    A_lt 2 1 (-11) (-9 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_s : A 3 2 x < A (-11) (-9 - 1) x :=
    A_lt 3 2 (-11) (-9 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_s : A 9 7 x < A (-11) (-9 - 1) x :=
    A_lt 9 7 (-11) (-9 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t10 : A 1 0 x < A 10 8 x :=
    A_lt 1 0 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t11 : A 1 0 x < A 11 9 x :=
    A_lt 1 0 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t2 : A 1 0 x < A 2 1 x :=
    A_lt 1 0 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t3 : A 1 0 x < A 3 2 x :=
    A_lt 1 0 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t9 : A 1 0 x < A 9 7 x :=
    A_lt 1 0 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t11 : A 10 8 x < A 11 9 x :=
    A_lt 10 8 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t10 : A 2 1 x < A 10 8 x :=
    A_lt 2 1 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t3 : A 10 8 x < A 3 2 x :=
    A_lt 10 8 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t10 : A 9 7 x < A 10 8 x :=
    A_lt 9 7 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t11 : A 2 1 x < A 11 9 x :=
    A_lt 2 1 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_t11 : A 3 2 x < A 11 9 x :=
    A_lt 3 2 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t11 : A 9 7 x < A 11 9 x :=
    A_lt 9 7 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t3 : A 2 1 x < A 3 2 x :=
    A_lt 2 1 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t2 : A 9 7 x < A 2 1 x :=
    A_lt 9 7 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t3 : A 9 7 x < A 3 2 x :=
    A_lt 9 7 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have z_t10 : 0 < A 10 8 x :=
    A_pos 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have o_t10 : A 10 8 x < 1 :=
    A_lt_one 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have z_t9 : 0 < A 9 7 x :=
    A_pos 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have o_t9 : A 9 7 x < 1 :=
    A_lt_one 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have z_t11 : 0 < A 11 9 x :=
    A_pos 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have o_t11 : A 11 9 x < 1 :=
    A_lt_one 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have z_t2 : 0 < A 2 1 x :=
    A_pos 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have o_t2 : A 2 1 x < 1 :=
    A_lt_one 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have z_t1 : 0 < A 1 0 x :=
    A_pos 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t1 : A 1 0 x < 1 :=
    A_lt_one 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t3 : 0 < A 3 2 x :=
    A_pos 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have o_t3 : A 3 2 x < 1 :=
    A_lt_one 3 2 _ _ x hx1 hx2 (by decide +kernel)
  refine phi_eq x 2 ?_ ?_
  · intro y hy0 hy1
    rw [D y hy0 hy1]
    have := Ival_ge x 9 8 7 1 0 2 (2 - (3)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ y hy0
      hy1
    · omega
    · simp only [Ival, not_lt.2 hs0, not_le.2 z_t10, not_le.2 z_t9, not_le.2 z_t11,
        not_le.2 z_t2, not_le.2 z_t1, not_le.2 z_t3]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t10_s).le, (f_t9_t10).le, not_le.2 f_t10_t11, (f_t2_t10).le,
        (f_t1_t10).le, not_le.2 f_t10_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t9_s).le, not_le.2 f_t9_t10, not_le.2 f_t9_t11,
        not_le.2 f_t9_t2, (f_t1_t9).le, not_le.2 f_t9_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t11_s).le, (f_t10_t11).le, (f_t9_t11).le, (f_t2_t11).le,
        (f_t1_t11).le, (f_t3_t11).le, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t2_s).le, not_le.2 f_t2_t10, (f_t9_t2).le, not_le.2 f_t2_t11,
        (f_t1_t2).le, not_le.2 f_t2_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t1_s).le, not_le.2 f_t1_t10, not_le.2 f_t1_t9,
        not_le.2 f_t1_t11, not_le.2 f_t1_t2, not_le.2 f_t1_t3, le_refl]
      decide
    · intro _ _
      simp only [Ival, not_lt.2 (f_t3_s).le, (f_t10_t3).le, (f_t9_t3).le, not_le.2 f_t3_t11,
        (f_t2_t3).le, (f_t1_t3).le, le_refl]
      decide
    · simp only [Ip, (f_t10_s).le, (f_t9_s).le, (f_t11_s).le, (f_t2_s).le, (f_t1_s).le,
        (f_t3_s).le]
      decide
  · refine ⟨A 2 1 x, z_t2.le, o_t2, ?_⟩
    rw [D _ z_t2.le o_t2]
    simp only [Ival, not_lt.2 (f_t2_s).le, not_le.2 f_t2_t10, (f_t9_t2).le, not_le.2 f_t2_t11,
        (f_t1_t2).le, not_le.2 f_t2_t3, le_refl]
    decide

theorem cell_83 (x : ℝ) (hx1 : ((7 / 8 : ℚ) : ℝ) < x) (hx2 : x < ((8 / 9 : ℚ) : ℝ)) :
    phi x = 0 := by
  have f11 := floor_bounds 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f10 := floor_bounds 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f9 := floor_bounds 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have f8 := floor_bounds 8 7 _ _ x hx1 hx2 (by decide +kernel)
  have f2 := floor_bounds 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f1 := floor_bounds 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f3 := floor_bounds 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have D := rho_decomp x 9 8 7 7 1 0 2 f11 f10 f9 f8 f2 f1 f3
  have hs0 := s_nonneg 9 x f11
  have hs1 := s_lt_one 9 x f11
  have f_t1_s : A 1 0 x < A (-11) (-9 - 1) x :=
    A_lt 1 0 (-11) (-9 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_s : A 10 8 x < A (-11) (-9 - 1) x :=
    A_lt 10 8 (-11) (-9 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_s : A 11 9 x < A (-11) (-9 - 1) x :=
    A_lt 11 9 (-11) (-9 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_s : A 2 1 x < A (-11) (-9 - 1) x :=
    A_lt 2 1 (-11) (-9 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t3_s : A 3 2 x < A (-11) (-9 - 1) x :=
    A_lt 3 2 (-11) (-9 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_s : A 9 7 x < A (-11) (-9 - 1) x :=
    A_lt 9 7 (-11) (-9 - 1) _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t10 : A 1 0 x < A 10 8 x :=
    A_lt 1 0 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t11 : A 1 0 x < A 11 9 x :=
    A_lt 1 0 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t2 : A 1 0 x < A 2 1 x :=
    A_lt 1 0 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t1_t3 : A 1 0 x < A 3 2 x :=
    A_lt 1 0 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t1 : A 9 7 x < A 1 0 x :=
    A_lt 9 7 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t11 : A 10 8 x < A 11 9 x :=
    A_lt 10 8 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t2 : A 10 8 x < A 2 1 x :=
    A_lt 10 8 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t10_t3 : A 10 8 x < A 3 2 x :=
    A_lt 10 8 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t10 : A 9 7 x < A 10 8 x :=
    A_lt 9 7 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t11 : A 2 1 x < A 11 9 x :=
    A_lt 2 1 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t11_t3 : A 11 9 x < A 3 2 x :=
    A_lt 11 9 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t11 : A 9 7 x < A 11 9 x :=
    A_lt 9 7 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have f_t2_t3 : A 2 1 x < A 3 2 x :=
    A_lt 2 1 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t2 : A 9 7 x < A 2 1 x :=
    A_lt 9 7 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have f_t9_t3 : A 9 7 x < A 3 2 x :=
    A_lt 9 7 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have z_t10 : 0 < A 10 8 x :=
    A_pos 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have o_t10 : A 10 8 x < 1 :=
    A_lt_one 10 8 _ _ x hx1 hx2 (by decide +kernel)
  have z_t9 : 0 < A 9 7 x :=
    A_pos 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have o_t9 : A 9 7 x < 1 :=
    A_lt_one 9 7 _ _ x hx1 hx2 (by decide +kernel)
  have z_t11 : 0 < A 11 9 x :=
    A_pos 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have o_t11 : A 11 9 x < 1 :=
    A_lt_one 11 9 _ _ x hx1 hx2 (by decide +kernel)
  have z_t2 : 0 < A 2 1 x :=
    A_pos 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have o_t2 : A 2 1 x < 1 :=
    A_lt_one 2 1 _ _ x hx1 hx2 (by decide +kernel)
  have z_t1 : 0 < A 1 0 x :=
    A_pos 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have o_t1 : A 1 0 x < 1 :=
    A_lt_one 1 0 _ _ x hx1 hx2 (by decide +kernel)
  have z_t3 : 0 < A 3 2 x :=
    A_pos 3 2 _ _ x hx1 hx2 (by decide +kernel)
  have o_t3 : A 3 2 x < 1 :=
    A_lt_one 3 2 _ _ x hx1 hx2 (by decide +kernel)
  refine phi_eq x 0 ?_ ?_
  · intro y _ _
    exact rho_nonneg x y
  · refine ⟨0, le_rfl, zero_lt_one, ?_⟩
    rw [D 0 le_rfl zero_lt_one]
    simp only [Ival, not_lt.2 hs0, not_le.2 z_t10, not_le.2 z_t9, not_le.2 z_t11,
        not_le.2 z_t2, not_le.2 z_t1, not_le.2 z_t3]
    decide

end Zeta2GammaCells
