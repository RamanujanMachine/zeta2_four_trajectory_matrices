import Zeta2FourTrajectoryMatrices.ArithmeticRate.blueprint_gamma_cells1
import Zeta2FourTrajectoryMatrices.ArithmeticRate.blueprint_gamma_cells2
import Zeta2FourTrajectoryMatrices.ArithmeticRate.blueprint_gamma_cells3
import Zeta2FourTrajectoryMatrices.ArithmeticRate.blueprint_gamma_cells4
import Zeta2FourTrajectoryMatrices.ArithmeticRate.blueprint_gamma_cells5
import Zeta2FourTrajectoryMatrices.ArithmeticRate.blueprint_gamma_cells6
import Zeta2FourTrajectoryMatrices.ArithmeticRate.blueprint_gamma_cells7
import Zeta2FourTrajectoryMatrices.ArithmeticRate.blueprint_gamma_cells8

open Zeta2Blueprint Zeta2GammaCore Zeta2GammaCells Finset

noncomputable section

namespace Zeta2GammaTable

/-- The cut points `0 = c₀ < c₁ < ⋯ < c₉₄ = 1` of the 94-cell partition. -/
def cut : ℕ → ℚ
  | 0 => 0
  | 1 => 1 / 22
  | 2 => 1 / 21
  | 3 => 1 / 20
  | 4 => 1 / 14
  | 5 => 1 / 13
  | 6 => 1 / 12
  | 7 => 1 / 11
  | 8 => 2 / 21
  | 9 => 1 / 10
  | 10 => 1 / 9
  | 11 => 1 / 8
  | 12 => 3 / 22
  | 13 => 1 / 7
  | 14 => 3 / 20
  | 15 => 2 / 13
  | 16 => 1 / 6
  | 17 => 2 / 11
  | 18 => 4 / 21
  | 19 => 1 / 5
  | 20 => 3 / 14
  | 21 => 2 / 9
  | 22 => 5 / 22
  | 23 => 3 / 13
  | 24 => 5 / 21
  | 25 => 1 / 4
  | 26 => 3 / 11
  | 27 => 2 / 7
  | 28 => 3 / 10
  | 29 => 4 / 13
  | 30 => 7 / 22
  | 31 => 1 / 3
  | 32 => 7 / 20
  | 33 => 5 / 14
  | 34 => 4 / 11
  | 35 => 3 / 8
  | 36 => 8 / 21
  | 37 => 5 / 13
  | 38 => 2 / 5
  | 39 => 9 / 22
  | 40 => 5 / 12
  | 41 => 3 / 7
  | 42 => 4 / 9
  | 43 => 9 / 20
  | 44 => 5 / 11
  | 45 => 6 / 13
  | 46 => 10 / 21
  | 47 => 1 / 2
  | 48 => 11 / 21
  | 49 => 7 / 13
  | 50 => 6 / 11
  | 51 => 11 / 20
  | 52 => 5 / 9
  | 53 => 4 / 7
  | 54 => 7 / 12
  | 55 => 13 / 22
  | 56 => 3 / 5
  | 57 => 8 / 13
  | 58 => 13 / 21
  | 59 => 5 / 8
  | 60 => 7 / 11
  | 61 => 9 / 14
  | 62 => 13 / 20
  | 63 => 2 / 3
  | 64 => 15 / 22
  | 65 => 9 / 13
  | 66 => 7 / 10
  | 67 => 5 / 7
  | 68 => 8 / 11
  | 69 => 3 / 4
  | 70 => 16 / 21
  | 71 => 10 / 13
  | 72 => 17 / 22
  | 73 => 7 / 9
  | 74 => 11 / 14
  | 75 => 4 / 5
  | 76 => 17 / 21
  | 77 => 9 / 11
  | 78 => 5 / 6
  | 79 => 11 / 13
  | 80 => 17 / 20
  | 81 => 6 / 7
  | 82 => 19 / 22
  | 83 => 7 / 8
  | 84 => 8 / 9
  | 85 => 9 / 10
  | 86 => 19 / 21
  | 87 => 10 / 11
  | 88 => 11 / 12
  | 89 => 12 / 13
  | 90 => 13 / 14
  | 91 => 19 / 20
  | 92 => 20 / 21
  | 93 => 21 / 22
  | 94 => 1
  | _ => 1

/-- The value of `φ` on the open cell `(cᵢ, cᵢ₊₁)`. -/
def hv : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 1
  | 8 => 1
  | 9 => 2
  | 10 => 3
  | 11 => 0
  | 12 => 0
  | 13 => 0
  | 14 => 0
  | 15 => 0
  | 16 => 0
  | 17 => 1
  | 18 => 1
  | 19 => 2
  | 20 => 2
  | 21 => 2
  | 22 => 2
  | 23 => 2
  | 24 => 2
  | 25 => 0
  | 26 => 1
  | 27 => 1
  | 28 => 1
  | 29 => 1
  | 30 => 1
  | 31 => 2
  | 32 => 2
  | 33 => 2
  | 34 => 3
  | 35 => 0
  | 36 => 0
  | 37 => 0
  | 38 => 0
  | 39 => 0
  | 40 => 0
  | 41 => 1
  | 42 => 1
  | 43 => 1
  | 44 => 2
  | 45 => 2
  | 46 => 2
  | 47 => 0
  | 48 => 0
  | 49 => 0
  | 50 => 1
  | 51 => 1
  | 52 => 2
  | 53 => 2
  | 54 => 1
  | 55 => 1
  | 56 => 2
  | 57 => 2
  | 58 => 2
  | 59 => 0
  | 60 => 1
  | 61 => 0
  | 62 => 0
  | 63 => 1
  | 64 => 1
  | 65 => 1
  | 66 => 1
  | 67 => 2
  | 68 => 3
  | 69 => 0
  | 70 => 0
  | 71 => 0
  | 72 => 0
  | 73 => 1
  | 74 => 0
  | 75 => 0
  | 76 => 0
  | 77 => 1
  | 78 => 2
  | 79 => 1
  | 80 => 1
  | 81 => 2
  | 82 => 2
  | 83 => 0
  | 84 => 0
  | 85 => 0
  | 86 => 0
  | 87 => 1
  | 88 => 1
  | 89 => 1
  | 90 => 0
  | 91 => 0
  | 92 => 0
  | 93 => 0
  | _ => 0

/-- Numerators of the cut points. -/
def an : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 1
  | 10 => 1
  | 11 => 1
  | 12 => 3
  | 13 => 1
  | 14 => 3
  | 15 => 2
  | 16 => 1
  | 17 => 2
  | 18 => 4
  | 19 => 1
  | 20 => 3
  | 21 => 2
  | 22 => 5
  | 23 => 3
  | 24 => 5
  | 25 => 1
  | 26 => 3
  | 27 => 2
  | 28 => 3
  | 29 => 4
  | 30 => 7
  | 31 => 1
  | 32 => 7
  | 33 => 5
  | 34 => 4
  | 35 => 3
  | 36 => 8
  | 37 => 5
  | 38 => 2
  | 39 => 9
  | 40 => 5
  | 41 => 3
  | 42 => 4
  | 43 => 9
  | 44 => 5
  | 45 => 6
  | 46 => 10
  | 47 => 1
  | 48 => 11
  | 49 => 7
  | 50 => 6
  | 51 => 11
  | 52 => 5
  | 53 => 4
  | 54 => 7
  | 55 => 13
  | 56 => 3
  | 57 => 8
  | 58 => 13
  | 59 => 5
  | 60 => 7
  | 61 => 9
  | 62 => 13
  | 63 => 2
  | 64 => 15
  | 65 => 9
  | 66 => 7
  | 67 => 5
  | 68 => 8
  | 69 => 3
  | 70 => 16
  | 71 => 10
  | 72 => 17
  | 73 => 7
  | 74 => 11
  | 75 => 4
  | 76 => 17
  | 77 => 9
  | 78 => 5
  | 79 => 11
  | 80 => 17
  | 81 => 6
  | 82 => 19
  | 83 => 7
  | 84 => 8
  | 85 => 9
  | 86 => 19
  | 87 => 10
  | 88 => 11
  | 89 => 12
  | 90 => 13
  | 91 => 19
  | 92 => 20
  | 93 => 21
  | 94 => 1
  | _ => 1

/-- Denominators of the cut points. -/
def ad : ℕ → ℕ
  | 0 => 1
  | 1 => 22
  | 2 => 21
  | 3 => 20
  | 4 => 14
  | 5 => 13
  | 6 => 12
  | 7 => 11
  | 8 => 21
  | 9 => 10
  | 10 => 9
  | 11 => 8
  | 12 => 22
  | 13 => 7
  | 14 => 20
  | 15 => 13
  | 16 => 6
  | 17 => 11
  | 18 => 21
  | 19 => 5
  | 20 => 14
  | 21 => 9
  | 22 => 22
  | 23 => 13
  | 24 => 21
  | 25 => 4
  | 26 => 11
  | 27 => 7
  | 28 => 10
  | 29 => 13
  | 30 => 22
  | 31 => 3
  | 32 => 20
  | 33 => 14
  | 34 => 11
  | 35 => 8
  | 36 => 21
  | 37 => 13
  | 38 => 5
  | 39 => 22
  | 40 => 12
  | 41 => 7
  | 42 => 9
  | 43 => 20
  | 44 => 11
  | 45 => 13
  | 46 => 21
  | 47 => 2
  | 48 => 21
  | 49 => 13
  | 50 => 11
  | 51 => 20
  | 52 => 9
  | 53 => 7
  | 54 => 12
  | 55 => 22
  | 56 => 5
  | 57 => 13
  | 58 => 21
  | 59 => 8
  | 60 => 11
  | 61 => 14
  | 62 => 20
  | 63 => 3
  | 64 => 22
  | 65 => 13
  | 66 => 10
  | 67 => 7
  | 68 => 11
  | 69 => 4
  | 70 => 21
  | 71 => 13
  | 72 => 22
  | 73 => 9
  | 74 => 14
  | 75 => 5
  | 76 => 21
  | 77 => 11
  | 78 => 6
  | 79 => 13
  | 80 => 20
  | 81 => 7
  | 82 => 22
  | 83 => 8
  | 84 => 9
  | 85 => 10
  | 86 => 21
  | 87 => 11
  | 88 => 12
  | 89 => 13
  | 90 => 14
  | 91 => 20
  | 92 => 21
  | 93 => 22
  | 94 => 1
  | _ => 1

/-- The cell values as natural numbers. -/
def hvN : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 1
  | 8 => 1
  | 9 => 2
  | 10 => 3
  | 11 => 0
  | 12 => 0
  | 13 => 0
  | 14 => 0
  | 15 => 0
  | 16 => 0
  | 17 => 1
  | 18 => 1
  | 19 => 2
  | 20 => 2
  | 21 => 2
  | 22 => 2
  | 23 => 2
  | 24 => 2
  | 25 => 0
  | 26 => 1
  | 27 => 1
  | 28 => 1
  | 29 => 1
  | 30 => 1
  | 31 => 2
  | 32 => 2
  | 33 => 2
  | 34 => 3
  | 35 => 0
  | 36 => 0
  | 37 => 0
  | 38 => 0
  | 39 => 0
  | 40 => 0
  | 41 => 1
  | 42 => 1
  | 43 => 1
  | 44 => 2
  | 45 => 2
  | 46 => 2
  | 47 => 0
  | 48 => 0
  | 49 => 0
  | 50 => 1
  | 51 => 1
  | 52 => 2
  | 53 => 2
  | 54 => 1
  | 55 => 1
  | 56 => 2
  | 57 => 2
  | 58 => 2
  | 59 => 0
  | 60 => 1
  | 61 => 0
  | 62 => 0
  | 63 => 1
  | 64 => 1
  | 65 => 1
  | 66 => 1
  | 67 => 2
  | 68 => 3
  | 69 => 0
  | 70 => 0
  | 71 => 0
  | 72 => 0
  | 73 => 1
  | 74 => 0
  | 75 => 0
  | 76 => 0
  | 77 => 1
  | 78 => 2
  | 79 => 1
  | 80 => 1
  | 81 => 2
  | 82 => 2
  | 83 => 0
  | 84 => 0
  | 85 => 0
  | 86 => 0
  | 87 => 1
  | 88 => 1
  | 89 => 1
  | 90 => 0
  | 91 => 0
  | 92 => 0
  | 93 => 0
  | _ => 0

theorem cut_zero : cut 0 = 0 := by decide +kernel

theorem cut_last : cut 94 = 1 := by decide +kernel

theorem cut_13 : cut 5 = 1 / 13 := by decide +kernel

theorem cut_lt : ∀ i, i < 94 → cut i < cut (i + 1) := by decide +kernel

theorem cut_eq_div : ∀ i, i < 95 → cut i = (an i : ℚ) / ad i := by decide +kernel

theorem ad_pos : ∀ i, i < 95 → 0 < ad i := by decide +kernel

theorem hv_eq : ∀ i, i < 94 → hv i = (hvN i : ℤ) := by decide +kernel

theorem hv_nonneg : ∀ i, i < 94 → 0 ≤ hv i := by decide +kernel

theorem hv_le : ∀ i, i < 94 → hv i ≤ 3 := by decide +kernel

theorem hv_pos_cut : ∀ i, i < 94 → hv i ≠ 0 → (1 / 13 : ℚ) ≤ cut i := by decide +kernel

theorem hv_zero_of_lt : ∀ i, i < 94 → cut (i + 1) ≤ (1 / 13 : ℚ) → hv i = 0 := by decide +kernel

theorem mean_eq : ∑ i ∈ range 94, hv i * (cut (i + 1) - cut i) = 3517 / 4095 := by decide +kernel

theorem cell_all : ∀ i, i < 94 → ∀ x : ℝ, ((cut i : ℚ) : ℝ) < x → x < ((cut (i + 1) : ℚ) : ℝ) →
    phi x = hv i := by
  intro i hi
  interval_cases i
  · exact cell_0
  · exact cell_1
  · exact cell_2
  · exact cell_3
  · exact cell_4
  · exact cell_5
  · exact cell_6
  · exact cell_7
  · exact cell_8
  · exact cell_9
  · exact cell_10
  · exact cell_11
  · exact cell_12
  · exact cell_13
  · exact cell_14
  · exact cell_15
  · exact cell_16
  · exact cell_17
  · exact cell_18
  · exact cell_19
  · exact cell_20
  · exact cell_21
  · exact cell_22
  · exact cell_23
  · exact cell_24
  · exact cell_25
  · exact cell_26
  · exact cell_27
  · exact cell_28
  · exact cell_29
  · exact cell_30
  · exact cell_31
  · exact cell_32
  · exact cell_33
  · exact cell_34
  · exact cell_35
  · exact cell_36
  · exact cell_37
  · exact cell_38
  · exact cell_39
  · exact cell_40
  · exact cell_41
  · exact cell_42
  · exact cell_43
  · exact cell_44
  · exact cell_45
  · exact cell_46
  · exact cell_47
  · exact cell_48
  · exact cell_49
  · exact cell_50
  · exact cell_51
  · exact cell_52
  · exact cell_53
  · exact cell_54
  · exact cell_55
  · exact cell_56
  · exact cell_57
  · exact cell_58
  · exact cell_59
  · exact cell_60
  · exact cell_61
  · exact cell_62
  · exact cell_63
  · exact cell_64
  · exact cell_65
  · exact cell_66
  · exact cell_67
  · exact cell_68
  · exact cell_69
  · exact cell_70
  · exact cell_71
  · exact cell_72
  · exact cell_73
  · exact cell_74
  · exact cell_75
  · exact cell_76
  · exact cell_77
  · exact cell_78
  · exact cell_79
  · exact cell_80
  · exact cell_81
  · exact cell_82
  · exact cell_83
  · exact cell_84
  · exact cell_85
  · exact cell_86
  · exact cell_87
  · exact cell_88
  · exact cell_89
  · exact cell_90
  · exact cell_91
  · exact cell_92
  · exact cell_93

end Zeta2GammaTable
