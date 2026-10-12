import QCatalan.Defs
import QZeta3.Denominators

/-!
# A finite elementary bound for odd reciprocal squares

The first two odd terms are retained exactly.  All later terms are bounded by
`1/(4a(a+1))`, whose finite sum telescopes.  No asymptotic totient theorem or
value of the zeta function is used.
-/

open Finset
namespace QCatalan

lemma odd_reciprocal_square_le_telescope (a : ℕ) (ha : 0 < a) :
    (1:ℝ)/(2*(a:ℝ)+1)^2 ≤ 1/(4*(a:ℝ)) - 1/(4*((a:ℝ)+1)) := by
  have ha0 : (0:ℝ) < a := by exact_mod_cast ha
  have he : 1/(4*(a:ℝ)) - 1/(4*((a:ℝ)+1)) =
      1/(4*(a:ℝ)*((a:ℝ)+1)) := by field_simp; ring
  rw [he]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

lemma sum_odd_reciprocal_square_sharp (n : ℕ) :
    (∑ j ∈ range (n+2), (1:ℝ)/(2*(j:ℝ)+1)^2) ≤
      89/72 - 1/(4*((n:ℝ)+2)) := by
  induction n with
  | zero => norm_num [sum_range_succ]
  | succ n ih =>
    rw [show n+1+2 = (n+2)+1 by omega, sum_range_succ]
    have h := odd_reciprocal_square_le_telescope (n+2) (by omega)
    push_cast at h ⊢
    have he : ((n:ℝ)+1)+2 = ((n:ℝ)+2)+1 := by ring
    rw [he]
    linarith

/-- Every finite initial segment of the odd reciprocal-square series is bounded. -/
theorem sum_odd_reciprocal_square_le (N : ℕ) :
    (∑ j ∈ range N, (1:ℝ)/(2*(j:ℝ)+1)^2) ≤ 89/72 := by
  have hs := sum_odd_reciprocal_square_sharp N
  have hsub : range N ⊆ range (N+2) := range_mono (by omega)
  have hle : (∑ j ∈ range N, (1:ℝ)/(2*(j:ℝ)+1)^2) ≤
      ∑ j ∈ range (N+2), (1:ℝ)/(2*(j:ℝ)+1)^2 :=
    sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by positivity)
  have hz : (0:ℝ) ≤ 1/(4*((N:ℝ)+2)) := by positivity
  linarith

/-- The finite odd-index bound in the indexing used by the cyclotomic cost. -/
theorem sum_inv_sq_odd_le (N : ℕ) :
    (∑ a ∈ (Icc 1 N).filter (fun a => a%2=1), (1:ℝ)/(a:ℝ)^2) ≤ 89/72 := by
  let s := (Icc 1 N).filter (fun a => a%2=1)
  have hinj : Set.InjOn (fun a : ℕ => a/2) s := by
    intro a ha b hb hab
    change a/2=b/2 at hab
    have haodd := (mem_filter.mp ha).2
    have hbodd := (mem_filter.mp hb).2
    omega
  have hsub : s.image (fun a => (a/2:ℕ)) ⊆ range (N+1) := by
    intro j hj
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hj
    have haN := (mem_Icc.mp (mem_filter.mp ha).1).2
    exact mem_range.mpr (by omega)
  calc
    (∑ a ∈ s, (1:ℝ)/(a:ℝ)^2) =
        ∑ a ∈ s, (1:ℝ)/(2*((a/2:ℕ):ℝ)+1)^2 := by
      apply sum_congr rfl
      intro a ha
      have he : 2*(a/2)+1 = a := by have := (mem_filter.mp ha).2; omega
      have her : 2*((a/2:ℕ):ℝ)+1 = (a:ℝ) := by exact_mod_cast he
      rw [her]
    _ = ∑ j ∈ s.image (fun a => (a/2:ℕ)), (1:ℝ)/(2*(j:ℝ)+1)^2 :=
      (sum_image (f := fun j : ℕ => (1:ℝ)/(2*(j:ℝ)+1)^2) hinj).symm
    _ ≤ ∑ j ∈ range (N+1), (1:ℝ)/(2*(j:ℝ)+1)^2 :=
      sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by positivity)
    _ ≤ 89/72 := sum_odd_reciprocal_square_le (N+1)

/-- The companion harmonic estimate for the lower-order error. -/
theorem sum_inv_le_one_add_log (N : ℕ) (hN : 1 ≤ N) :
    ∑ a ∈ Icc 1 N, (1:ℝ)/(a:ℝ) ≤ 1+Real.log N :=
  QZeta3.sum_inv_le_one_add_log N hN

end QCatalan
