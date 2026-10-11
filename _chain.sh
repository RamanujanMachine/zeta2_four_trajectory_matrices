cd "C:/Lean/zeta2_four_trajectory_matrices"
: > _chain.log
for n in blueprint_gamma_core blueprint_gamma_cells1 blueprint_gamma_cells2 blueprint_gamma_cells3 blueprint_gamma_cells4 blueprint_gamma_cells5 blueprint_gamma_cells6 blueprint_gamma_cells7 blueprint_gamma_cells8 blueprint_gamma_table blueprint_gamma_sumA blueprint_gamma_sumB blueprint_gamma_sum blueprint_gamma_int blueprint_gamma_bounds blueprint_irr_criterion blueprint_limit_spectrum blueprint_bounded_gap; do
  echo "=== build $n" >> _chain.log
  lake build $n 2>&1 | grep -i "error\|warning: $n" | head -12 >> _chain.log
done
echo "=== BUILD-PHASE-DONE" >> _chain.log
for f in blueprint_irr_criterion blueprint_limit_spectrum blueprint_bounded_gap blueprint_gamma_core blueprint_gamma_cells1 blueprint_gamma_cells2 blueprint_gamma_cells3 blueprint_gamma_cells4 blueprint_gamma_cells5 blueprint_gamma_cells6 blueprint_gamma_cells7 blueprint_gamma_cells8 blueprint_gamma_table blueprint_gamma_sumA blueprint_gamma_sumB blueprint_gamma_sum blueprint_gamma_int blueprint_gamma_bounds; do
  echo "=== profile $f" >> _chain.log
  lake env lean --profile $f.lean 2>&1 | grep -A40 "cumulative profiling" | grep "elaboration\|tactic execution\|type checking\|import\|typeclass inference\|simp \|linarith\|interpretation\|blocked" | grep -v "took" >> _chain.log
done
echo "=== CHAIN-DONE" >> _chain.log
