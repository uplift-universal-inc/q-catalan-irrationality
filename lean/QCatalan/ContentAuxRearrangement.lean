import QCatalan.Defs

/-!
# The convex content-weight estimate

The manuscript obtains this rearrangement inequality by removing inversions.
Midpoint convexity gives a shorter equivalent proof: bound each summand by the
mean of its two diagonal terms, then use invariance of a finite sum under a
permutation. All weights are the exact natural-valued truncated quadratics.
-/

open Finset
namespace QCatalan

/-- The exact loss for entry index `k` in a size-`K` Hankel determinant. -/
def contentWeight (K k : ℕ) : ℕ := (K - k) * (K - k + 1)

lemma contentWeight_midpoint (K i j : ℕ) :
    2 * contentWeight K (i + j) ≤ contentWeight K (2 * i) + contentWeight K (2 * j) := by
  unfold contentWeight
  have h : 2 * (K - (i + j)) ≤ (K - 2 * i) + (K - 2 * j) := by omega
  have hs := Nat.mul_self_le_mul_self h
  have hd := sq_nonneg (((K - 2 * i : ℕ) : ℤ) - ((K - 2 * j : ℕ) : ℤ))
  zify at h hs ⊢
  nlinarith

/-- A permutation cannot exceed the diagonal sum of the convex content weights. -/
theorem sum_contentWeight_perm_le_diag (K : ℕ) (σ : Equiv.Perm (Fin K)) :
    ∑ i : Fin K, contentWeight K (i.val + (σ i).val) ≤
      ∑ i : Fin K, contentWeight K (2 * i.val) := by
  have h := sum_le_sum (s := (univ : Finset (Fin K)))
    (fun i _ => contentWeight_midpoint K i.val (σ i).val)
  rw [sum_add_distrib, ← mul_sum] at h
  have he := Equiv.sum_comp σ (fun i : Fin K => contentWeight K (2 * i.val))
  rw [he] at h
  omega

/-- Expanded form convenient when working directly from the definition of `cK`. -/
theorem sum_weight_perm_le_diag (K : ℕ) (σ : Equiv.Perm (Fin K)) :
    ∑ i : Fin K, (K - (i.val + (σ i).val)) * (K - (i.val + (σ i).val) + 1) ≤
      ∑ i : Fin K, (K - 2 * i.val) * (K - 2 * i.val + 1) :=
  sum_contentWeight_perm_le_diag K σ

end QCatalan
