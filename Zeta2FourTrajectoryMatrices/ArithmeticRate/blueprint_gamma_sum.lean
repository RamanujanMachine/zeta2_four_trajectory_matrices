import Zeta2FourTrajectoryMatrices.ArithmeticRate.blueprint_gamma_sumB

open Zeta2GammaTable Finset

namespace Zeta2GammaSum

/-- The scaled numerator of cell `i`. -/
def numI (i : ℕ) : ℕ := 10 ^ 15 * (hvN i * (an (i + 1) * ad i - an i * ad (i + 1)))

theorem data_eq :
    data = List.ofFn fun i : Fin 94 => (an i, ad i, an (i + 1), ad (i + 1), numI i) := by
  decide +kernel

theorem foldl_add {α : Type*} (f : α → ℕ) : ∀ (l : List α) (a : ℕ),
    l.foldl (fun acc c => acc + f c) a = a + (l.map f).sum
  | [], a => (Nat.add_zero a).symm
  | c :: l, a => by
    rw [List.foldl_cons, foldl_add f l, List.map_cons, List.sum_cons, Nat.add_assoc]

theorem list_sum_range (g : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map g).sum = ∑ i ∈ range n, g i := by
  rw [← List.map_coe_finRange_eq_range, List.map_map, Finset.sum_range, Fin.sum_univ_def]
  rfl

/-- The rounded term of period `k` and cell `i`. -/
def idxTerm (k i : ℕ) : ℕ := natTerm k (an i, ad i, an (i + 1), ad (i + 1), numI i)

theorem periodNat_eq (k : ℕ) : periodNat k = ∑ i ∈ range 94, idxTerm k i := by
  rw [periodNat, foldl_add, Nat.zero_add, data_eq, List.map_ofFn, Fin.sum_ofFn, Finset.sum_range]
  rfl

theorem chunk_eq (s : ℕ) : chunk s = ∑ k ∈ range 500, periodNat (s + k) := by
  rw [chunk, foldl_add, Nat.zero_add, list_sum_range]

theorem total_eq : ∑ k ∈ range 2000, periodNat k = 12127998763267375 := by
  rw [show (2000 : ℕ) = 500 + 500 + 500 + 500 from rfl, Finset.sum_range_add,
    Finset.sum_range_add, Finset.sum_range_add]
  have e0 : ∑ k ∈ range 500, periodNat k = chunk 0 := by
    rw [chunk_eq]
    exact Finset.sum_congr rfl fun k _ => by rw [Nat.zero_add]
  rw [e0, ← chunk_eq, ← chunk_eq, ← chunk_eq, chunk0, chunk1, chunk2, chunk3]

end Zeta2GammaSum
