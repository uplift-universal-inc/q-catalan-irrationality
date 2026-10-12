import QCatalan.RawDefs
import QCatalan.RawRamp
import QCatalan.OddReciprocals

/-! # Bounds for the two raw cluster contributions and the polynomial tail -/

open Polynomial Finset Real
namespace QCatalan

private theorem sum_Icc_eq_range_of_zero (K : ℕ) (f : ℕ → ℝ) (hf : f 0 = 0) :
    (∑ d ∈ Icc 1 K, f d) = ∑ d ∈ range (K + 1), f d := by
  have hI : Icc 1 K = Ico 1 (K + 1) := by ext d; simp
  rw [hI, Finset.sum_Ico_eq_sub _ (by omega), Finset.sum_range_one, hf, sub_zero]

theorem rawClusterCost_cast (K h : ℕ) :
    (rawClusterCost K h : ℝ) =
      ∑ a ∈ ((Icc 1 K).filter (fun a => a % 2 = 1)), ((K - a * h : ℕ) : ℝ) := by
  unfold rawClusterCost
  rw [Nat.cast_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  split_ifs <;> simp

/-- Interchanging the two finite sums produces precisely the ramp family. -/
theorem weighted_rawClusterCost_sum (w : ℕ → ℝ) (K t : ℕ) :
    (∑ d ∈ Icc 1 K, w d * d * (rawClusterCost K (t * d) : ℝ)) =
      ∑ a ∈ ((Icc 1 K).filter (fun a => a % 2 = 1)), weightedNatRamp w K (t * a) := by
  simp_rw [rawClusterCost_cast, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  unfold weightedNatRamp
  rw [sum_Icc_eq_range_of_zero K _ (by simp)]
  apply Finset.sum_congr rfl
  intro d hd
  have he : a * (t * d) = t * a * d := by ring
  rw [he]

/-- Twice-odd cyclotomic orders contribute one odd reciprocal-square family. -/
theorem rawClusterCost_odd_totient_sum_le (K : ℕ) :
    (∑ h ∈ Icc 1 K, if h % 2 = 1 then
      (rawClusterCost K h : ℝ) * Nat.totient h else 0) ≤
      (256 / 3675 * (89 / 72)) * (K : ℝ) ^ 3 +
        18030000 * (K : ℝ) ^ 2 * (1 + Real.log K) := by
  have hpoint : (∑ h ∈ Icc 1 K, if h % 2 = 1 then
      (rawClusterCost K h : ℝ) * Nat.totient h else 0) ≤
      ∑ h ∈ Icc 1 K, oddRawSieve h * h * (rawClusterCost K h : ℝ) := by
    apply Finset.sum_le_sum
    intro h hh
    by_cases ho : h % 2 = 1
    · simp only [ho, ite_true]
      have hp := mul_le_mul_of_nonneg_left
        (odd_totient_le_rawSieve h (by omega))
        (show (0 : ℝ) ≤ rawClusterCost K h by positivity)
      nlinarith
    · simp only [ho, ite_false]
      exact mul_nonneg (mul_nonneg (oddRawSieve_nonneg h) (by positivity)) (by positivity)
  have he := weighted_rawClusterCost_sum oddRawSieve K 1
  simp only [one_mul] at he
  rw [he] at hpoint
  have hs := oddRawRamp_sum_le K ((Icc 1 K).filter (fun a => a % 2 = 1))
    (fun a ha => (Finset.mem_filter.mp ha).1) (89 / 72) (sum_inv_sq_odd_le K)
  exact hpoint.trans (by simpa [mul_assoc, mul_left_comm, mul_comm] using hs)

/-- Fourfold raw proper fractions have the same cubic cost as the twice-odd class. -/
theorem rawClusterCost_four_totient_sum_le (K : ℕ) :
    (∑ u ∈ Icc 1 K, (rawClusterCost K (2 * u) : ℝ) * Nat.totient (4 * u)) ≤
      (256 / 3675 * (89 / 72)) * (K : ℝ) ^ 3 +
        18030000 * (K : ℝ) ^ 2 * (1 + Real.log K) := by
  have hpoint : (∑ u ∈ Icc 1 K, (rawClusterCost K (2 * u) : ℝ) * Nat.totient (4 * u)) ≤
      ∑ u ∈ Icc 1 K, fourRawSieve u * u * (rawClusterCost K (2 * u) : ℝ) := by
    apply Finset.sum_le_sum
    intro u hu
    have hp := mul_le_mul_of_nonneg_left (four_totient_le_rawSieve u)
      (show (0 : ℝ) ≤ rawClusterCost K (2 * u) by positivity)
    nlinarith
  rw [weighted_rawClusterCost_sum] at hpoint
  have hs := fourRawRamp_double_sum_le K ((Icc 1 K).filter (fun a => a % 2 = 1))
    (fun a ha => (Finset.mem_filter.mp ha).1) (89 / 72) (sum_inv_sq_odd_le K)
  exact hpoint.trans (by simpa [mul_assoc, mul_left_comm, mul_comm] using hs)

/-- The raw polynomial-quotient tail is bounded by the ramp of step one. -/
theorem rawPolynomialTail_totient_sum_le (K : ℕ) :
    (∑ u ∈ Icc 1 K, ((K - u - 1 : ℕ) : ℝ) * Nat.totient (4 * u)) ≤
      1024 / 3675 * (K : ℝ) ^ 3 + 18030000 * (K : ℝ) ^ 2 := by
  have hpoint : (∑ u ∈ Icc 1 K, ((K - u - 1 : ℕ) : ℝ) * Nat.totient (4 * u)) ≤
      weightedNatRamp fourRawSieve K 1 := by
    unfold weightedNatRamp
    rw [← sum_Icc_eq_range_of_zero K _ (by simp)]
    apply Finset.sum_le_sum
    intro u hu
    have ht : ((K - u - 1 : ℕ) : ℝ) ≤ (K - u : ℕ) := by exact_mod_cast (show K - u - 1 ≤ K - u by omega)
    have hp := four_totient_le_rawSieve u
    simp only [one_mul]
    calc
      _ ≤ ((K - u : ℕ) : ℝ) * Nat.totient (4 * u) :=
        mul_le_mul_of_nonneg_right ht (by positivity)
      _ ≤ ((K - u : ℕ) : ℝ) * (u * fourRawSieve u) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by ring
  have hs := weightedNatRamp_le_all fourRawSieve (1024 / 1225) 10000 2000000
    (by norm_num) (by norm_num) (by norm_num)
    (fun N => (fourRawSieve_firstMoment_bounds N).2)
    (fun N => by convert (fourRawSieve_secondMoment_bounds N).1 using 1 <;> norm_num)
    K 1 (by omega)
  norm_num at hs
  exact hpoint.trans hs

end QCatalan
