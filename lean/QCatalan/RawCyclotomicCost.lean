import QCatalan.RawDefs
import QZeta3.ClusterCounts

open Finset
namespace QCatalan

lemma twice_sum_sub_self (a : ℕ) :
    2*(∑ j ∈ range a, (a-j)) = a*(a+1) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [sum_range_succ']
    simp only [Nat.add_sub_add_right, Nat.sub_zero]
    nlinarith

lemma twice_sum_range_sub (a n : ℕ) (han : a ≤ n) :
    2*(∑ j ∈ range n, (a-j)) = a*(a+1) := by
  have he : (∑ j ∈ range a, (a-j)) = ∑ j ∈ range n, (a-j) := by
    apply sum_subset (range_mono han)
    intro j hj hja
    exact Nat.sub_eq_zero_of_le (by simpa using hja)
  rw [← he]
  exact twice_sum_sub_self a

lemma square_div_four (m : ℕ) : m^2/4 = (m/2)*(m-m/2) := by
  apply Nat.div_eq_of_lt_le <;>
    have h : m%2=0 ∨ m%2=1 := by omega
  · rcases h with h | h
    · have hm : m=2*(m/2) := by omega
      have ht : m-m/2=m/2 := by omega
      rw [ht]; nlinarith
    · have hm : m=2*(m/2)+1 := by omega
      have ht : m-m/2=m/2+1 := by omega
      rw [ht]; nlinarith
  · rcases h with h | h
    · have hm : m=2*(m/2) := by omega
      have ht : m-m/2=m/2 := by omega
      rw [ht]; nlinarith
    · have hm : m=2*(m/2)+1 := by omega
      have ht : m-m/2=m/2+1 := by omega
      rw [ht]; nlinarith

/-- Exact cost of complementary integer row and column weights. -/
theorem sum_raw_weights (m : ℕ) :
    (∑ j ∈ range m, ((m/2-j)+((m-1)/2-j))) = m^2/4 := by
  rw [sum_add_distrib, square_div_four]
  have h1 := twice_sum_range_sub (m/2) m (by omega)
  have h2 := twice_sum_range_sub ((m-1)/2) m (by omega)
  by_cases hm0 : m=0
  · simp [hm0]
  · have h : m%2=0 ∨ m%2=1 := by omega
    rcases h with h | h
    · have hm : m=2*(m/2) := by omega
      have hb : (m-1)/2+1=m/2 := by omega
      have ht : m-m/2=m/2 := by omega
      rw [ht]; nlinarith
    · have hm : m=2*(m/2)+1 := by omega
      have hb : (m-1)/2=m/2 := by omega
      have ht : m-m/2=m/2+1 := by omega
      rw [ht]; nlinarith

lemma sum_odd_indexed_ramp (m : ℕ) :
    (∑ j ∈ range m, (m-(2*j+1))) = m^2/4 := by
  induction m using Nat.twoStepInduction with
  | zero => simp
  | one => norm_num [sum_range_succ]
  | more m ih _ =>
    rw [show m+2=(m+1)+1 by omega, sum_range_succ']
    have he : (∑ j ∈ range (m+1), (m+2-(2*(j+1)+1))) =
        ∑ j ∈ range (m+1), (m-(2*j+1)) := by
      apply sum_congr rfl
      intro j hj
      omega
    rw [he, sum_range_succ, ih]
    have hz : m-(2*m+1)=0 := by omega
    have hfirst : m+1+1-(2*0+1)=m+1 := by omega
    rw [hz, hfirst, add_zero]
    have hs : (m+2)^2=m^2+4*(m+1) := by ring
    rw [show m+1+1=m+2 by omega, hs, Nat.add_mul_div_left _ _ (by decide)]

lemma sum_odd_truncated_ramp (m K : ℕ) (hmK : m ≤ K) :
    (∑ a ∈ (Icc 1 K).filter (fun a => a%2=1), (m-a)) = m^2/4 := by
  let s := (Icc 1 K).filter (fun a => a%2=1)
  have hinj : Set.InjOn (fun a : ℕ => a/2) s := by
    intro a ha b hb hab
    change a/2=b/2 at hab
    have := (mem_filter.mp ha).2
    have := (mem_filter.mp hb).2
    omega
  have hsub : s.image (fun a => a/2) ⊆ range K := by
    intro j hj
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hj
    have haN := mem_Icc.mp (mem_filter.mp ha).1
    exact mem_range.mpr (by omega)
  have hext : (∑ j ∈ s.image (fun a => a/2), (m-(2*j+1))) =
      ∑ j ∈ range K, (m-(2*j+1)) := by
    apply sum_subset hsub
    intro j hj hnot
    apply Nat.sub_eq_zero_of_le
    by_contra hh
    have hmem : 2*j+1 ∈ s := by
      apply mem_filter.mpr
      exact ⟨mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    apply hnot
    exact mem_image.mpr ⟨2*j+1,hmem,by omega⟩
  have hlarge : (∑ j ∈ range m, (m-(2*j+1))) =
      ∑ j ∈ range K, (m-(2*j+1)) := by
    apply sum_subset (range_mono hmK)
    intro j hj hjm
    exact Nat.sub_eq_zero_of_le (by simp only [mem_range, not_lt] at hjm; omega)
  calc
    (∑ a ∈ s, (m-a)) = ∑ a ∈ s, (m-(2*(a/2)+1)) := by
      apply sum_congr rfl
      intro a ha
      have := (mem_filter.mp ha).2
      congr 1
      omega
    _ = ∑ j ∈ s.image (fun a => a/2), (m-(2*j+1)) :=
      (sum_image (f := fun j : ℕ => m-(2*j+1)) hinj).symm
    _ = ∑ j ∈ range K, (m-(2*j+1)) := hext
    _ = m^2/4 := hlarge.symm.trans (sum_odd_indexed_ramp m)

/-- Summing a truncated ramp over balanced collision classes recovers the
single ramp at the full index length. -/
theorem sum_cluster_truncated_ramp (K h a : ℕ) (hh : 0 < h) :
    (∑ r ∈ range h, (QZeta3.Generic.clusterMultiplicity K h r-a)) = K-a*h := by
  have hsum := QZeta3.Generic.sum_clusterMultiplicity (K:=K) hh
  by_cases ha : a ≤ K/h
  · rw [sum_tsub_distrib]
    · simpa [hsum, mul_comm] using rfl
    · intro r hr
      rcases QZeta3.Generic.clusterMultiplicity_balanced (K:=K) hh (mem_range.mp hr) with he | he <;>
        rw [he] <;> omega
  · have hzero : ∀ r ∈ range h, (QZeta3.Generic.clusterMultiplicity K h r-a)=0 := by
      intro r hr
      rcases QZeta3.Generic.clusterMultiplicity_balanced (K:=K) hh (mem_range.mp hr) with he | he <;>
        rw [he] <;> omega
    rw [sum_eq_zero hzero]
    have hlt : K < a*h := (Nat.div_lt_iff_lt_mul hh).mp (by omega)
    omega

/-- The full collision cost is exactly the odd-ramp definition used by `rawE`. -/
theorem sum_cluster_square_div_four (K h : ℕ) (hh : 0 < h) :
    (∑ r ∈ range h, ((QZeta3.Generic.clusterMultiplicity K h r)^2/4)) =
      rawClusterCost K h := by
  have hbound (r : ℕ) : QZeta3.Generic.clusterMultiplicity K h r ≤ K := by
    unfold QZeta3.Generic.clusterMultiplicity QZeta3.Generic.clusterIndices
    exact (card_filter_le _ _).trans (by simp)
  simp_rw [← sum_odd_truncated_ramp _ K (hbound _)]
  rw [sum_comm]
  simp_rw [sum_cluster_truncated_ramp K h _ hh]
  simp [rawClusterCost, Finset.sum_filter]

end QCatalan
