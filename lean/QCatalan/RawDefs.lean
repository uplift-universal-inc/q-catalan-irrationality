import QCatalan.Defs

/-!
# Conservative cyclotomic normalization

This alternative denominator uses direct cluster bounds at orders divisible by
four. Its slightly larger cost still leaves a strict irrationality margin and
avoids formal tail interpolation. The manuscript's sharper normalization `E`,
`CK`, and `PK` remains separately defined and unchanged.
-/

open Polynomial Finset
namespace QCatalan

/-- Raw proper-cluster cost for nodes in index classes of spacing `h`. -/
def rawClusterCost (K h : ℕ) : ℕ :=
  ∑ a ∈ Icc 1 K, if a % 2 = 1 then K - a * h else 0

/-- Direct cyclotomic exponent, with a conservative fourth congruence class. -/
def rawE (K d : ℕ) : ℕ :=
  if d = 0 then 0 else
  if d % 2 = 1 then
    if d ≤ K then
      (K % d) * clusterCost (K / d + 1) + (d - K % d) * clusterCost (K / d)
    else if d ≤ 2 * K then 2 * (K - (d - 1) / 2) else 0
  else if d % 4 = 2 then rawClusterCost K (d/2)
  else rawClusterCost K (2*(d/4)) + (K-(d/4)-1)

/-- Integer cyclotomic clearer for the direct cluster route. -/
noncomputable def rawCK (p K : ℕ) : ℤ :=
  ∏ d ∈ Icc 1 (4*K), Phi p d ^ rawE K d

/-- Candidate integral polynomial using conservative direct cyclotomic clearing. -/
noncomputable def rawPK (p K : ℕ) : ℚ[X] :=
  Delta p K * C ((rawCK p K : ℚ) / (p : ℚ)^cK K)

/-- Elementary rational upper bound for the new cubic denominator cost. -/
def rawCost : ℚ := 115552 / 99225

/-- The corresponding elementary lower bound for the strict margin. -/
def rawMargin : ℚ := 7/6 - rawCost

theorem rawCost_lt_budget : rawCost < 7/6 := by norm_num [rawCost]
theorem rawMargin_pos : 0 < rawMargin := by norm_num [rawMargin, rawCost]

end QCatalan
