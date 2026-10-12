import QCatalan.ContentAuxRearrangement

/-!
# Exact content and analytic exponents

These finite identities prove the cubic leading terms used in the final
arithmetic/analytic budget, with explicit quadratic remainders.
-/

open Finset
namespace QCatalan

/-- The sum subtracted in the base-prime content exponent. -/
def contentLoss (K : ℕ) : ℕ := ∑ i ∈ range K, contentWeight K (2*i)

lemma contentLoss_add_two (K : ℕ) :
    contentLoss (K+2) = (K+2)*(K+3) + contentLoss K := by
  unfold contentLoss
  rw [show K+2 = (K+1)+1 by omega, sum_range_succ']
  have hs : (∑ i ∈ range (K+1), contentWeight (K+2) (2*(i+1))) =
      ∑ i ∈ range (K+1), contentWeight K (2*i) := by
    apply sum_congr rfl
    intro i hi
    unfold contentWeight
    rw [show K+2-2*(i+1) = K-2*i by omega]
  rw [hs, sum_range_succ]
  simp [contentWeight, show K-2*K = 0 by omega]
  ring

/-- The parity correction in the exact quadratic progression. -/
theorem contentLoss_exact (K : ℕ) :
    12 * contentLoss K = 2*K^3 + 9*K^2 + 10*K + 3*(K%2) := by
  induction K using Nat.twoStepInduction with
  | zero => simp [contentLoss]
  | one => norm_num [contentLoss, contentWeight]
  | more K ih _ =>
    rw [contentLoss_add_two]
    have hm : (K+2)%2 = K%2 := by omega
    rw [hm]
    nlinarith

lemma contentLoss_le (K : ℕ) : contentLoss K ≤ K^2*(K+1) := by
  unfold contentLoss contentWeight
  calc
    (∑ i ∈ range K, (K-2*i)*(K-2*i+1)) ≤ ∑ _i ∈ range K, K*(K+1) := by
      exact sum_le_sum fun i hi => Nat.mul_le_mul (Nat.sub_le _ _) (by omega)
    _ = K^2*(K+1) := by simp; ring

/-- A subtraction-free exact identity for the content exponent. -/
theorem cK_exact (K : ℕ) :
    12*cK K + 10*K + 3*(K%2) = 10*K^3 + 3*K^2 := by
  have hl := contentLoss_le K
  have he := contentLoss_exact K
  have hd : cK K + contentLoss K = K^2*(K+1) := by
    exact Nat.sub_add_cancel hl
  nlinarith

lemma aj_succ (j : ℕ) : aj (j+1) = aj j + (2*((j+2)/2)-1) := by
  unfold aj
  rw [sum_Icc_succ_top (by omega)]

/-- The root-exponent sum is precisely `ceil(j²/2)`. -/
theorem aj_exact (j : ℕ) : 2*aj j = j^2 + j%2 := by
  induction j with
  | zero => simp [aj]
  | succ j ih =>
    rw [aj_succ]
    have hr : 2*(2*((j+2)/2)-1) + 2*(j%2) = 2*j+2 := by omega
    have hm : (j+1)%2 + j%2 = 1 := by omega
    nlinarith

lemma bK_succ (K : ℕ) : bK (K+1) = bK K + 2*aj K := by
  unfold bK
  rw [sum_range_succ]
  ring

/-- A subtraction-free exact identity for the double-root analytic exponent. -/
theorem bK_exact (K : ℕ) :
    6*bK K + 3*K^2 + 3*(K%2) = 2*K^3 + 4*K := by
  induction K with
  | zero => simp [bK]
  | succ K ih =>
    rw [bK_succ]
    have ha := aj_exact K
    have hm : (K+1)%2 + K%2 = 1 := by omega
    nlinarith

/-- The content cubic term has an explicit quadratic error bound. -/
theorem cK_cubic_bounds (K : ℕ) :
    (5/6 : ℝ)*(K:ℝ)^3 - (K:ℝ) - 1 ≤ cK K ∧
      (cK K : ℝ) ≤ (5/6 : ℝ)*(K:ℝ)^3 + (1/4 : ℝ)*(K:ℝ)^2 := by
  have he := cK_exact K
  have hm : K%2 ≤ 1 := by omega
  have hK : (0:ℝ) ≤ K := Nat.cast_nonneg _
  have hmod : (0:ℝ) ≤ (K%2:ℕ) := Nat.cast_nonneg _
  have he' : (12:ℝ)*(cK K:ℝ) + 10*(K:ℝ) + 3*(K%2:ℕ) =
      10*(K:ℝ)^3 + 3*(K:ℝ)^2 := by exact_mod_cast he
  have hm' : ((K%2:ℕ):ℝ) ≤ 1 := by exact_mod_cast hm
  constructor <;> nlinarith [sq_nonneg (K:ℝ)]

/-- The analytic cubic term has an explicit quadratic error bound. -/
theorem bK_cubic_bounds (K : ℕ) :
    (1/3 : ℝ)*(K:ℝ)^3 - (1/2 : ℝ)*(K:ℝ)^2 - 1 ≤ bK K ∧
      (bK K : ℝ) ≤ (1/3 : ℝ)*(K:ℝ)^3 + (2/3 : ℝ)*(K:ℝ) := by
  have he := bK_exact K
  have hm : K%2 ≤ 1 := by omega
  have hK : (0:ℝ) ≤ K := Nat.cast_nonneg _
  have hmod : (0:ℝ) ≤ (K%2:ℕ) := Nat.cast_nonneg _
  have he' : (6:ℝ)*(bK K:ℝ) + 3*(K:ℝ)^2 + 3*(K%2:ℕ) =
      2*(K:ℝ)^3 + 4*(K:ℝ) := by exact_mod_cast he
  have hm' : ((K%2:ℕ):ℝ) ≤ 1 := by exact_mod_cast hm
  constructor <;> nlinarith [sq_nonneg (K:ℝ)]

/-- Exact total cubic budget supplied jointly by content and analytic decay. -/
theorem cK_add_bK_exact (K : ℕ) :
    12*(cK K+bK K) + 3*K^2 + 2*K + 9*(K%2) = 14*K^3 := by
  have hc := cK_exact K
  have hb := bK_exact K
  nlinarith

/-- A convenient uniform quadratic remainder for the full `7/6` budget. -/
theorem cK_add_bK_cubic_bounds (K : ℕ) :
    (7/6 : ℝ)*(K:ℝ)^3 - (7/6 : ℝ)*(K:ℝ)^2 ≤ (cK K:ℝ)+bK K ∧
      (cK K:ℝ)+bK K ≤ (7/6 : ℝ)*(K:ℝ)^3 := by
  have he := cK_add_bK_exact K
  have he' : (12:ℝ)*((cK K:ℝ)+bK K) + 3*(K:ℝ)^2 +
      2*(K:ℝ) + 9*(K%2:ℕ) = 14*(K:ℝ)^3 := by exact_mod_cast he
  have hm : ((K%2:ℕ):ℝ) ≤ 1 := by exact_mod_cast (show K%2 ≤ 1 by omega)
  have hmod : (0:ℝ) ≤ (K%2:ℕ) := Nat.cast_nonneg _
  have hK : (0:ℝ) ≤ K := Nat.cast_nonneg _
  constructor
  · by_cases hzero : K = 0
    · subst K; norm_num [cK, bK]
    · have hK1 : (1:ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
      nlinarith [sq_nonneg ((K:ℝ)-1)]
  · nlinarith [sq_nonneg (K:ℝ)]

end QCatalan
