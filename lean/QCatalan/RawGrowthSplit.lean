import QCatalan.RawDefs

open Finset
namespace QCatalan

lemma sum_Icc_four_step (f : ℕ → ℝ) (K : ℕ) :
    (∑ d ∈ Icc 1 (4*(K+1)), f d) = (∑ d ∈ Icc 1 (4*K), f d) +
      f (4*K+1) + f (4*K+2) + f (4*K+3) + f (4*K+4) := by
  rw [show 4*(K+1)=(((4*K+1)+1)+1)+1 by omega]
  repeat rw [sum_Icc_succ_top (by omega)]

lemma sum_Icc_two_step (f : ℕ → ℝ) (K : ℕ) :
    (∑ d ∈ Icc 1 (2*(K+1)), f d) = (∑ d ∈ Icc 1 (2*K), f d) +
      f (2*K+1) + f (2*K+2) := by
  rw [show 2*(K+1)=(2*K+1)+1 by omega]
  repeat rw [sum_Icc_succ_top (by omega)]

/-- Exact finite separation into odd, twice-odd, and fourfold orders. -/
theorem sum_Icc_four_classes (f : ℕ → ℝ) (K : ℕ) :
    (∑ d ∈ Icc 1 (4*K), f d) =
      (∑ d ∈ Icc 1 (4*K), if d%2=1 then f d else 0) +
      (∑ h ∈ Icc 1 (2*K), if h%2=1 then f (2*h) else 0) +
      ∑ u ∈ Icc 1 K, f (4*u) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_Icc_four_step, sum_Icc_four_step, sum_Icc_two_step,
      sum_Icc_succ_top (by omega), ih]
    have h41 : (4*K+1)%2=1 := by omega
    have h42 : (4*K+2)%2=0 := by omega
    have h43 : (4*K+3)%2=1 := by omega
    have h44 : (4*K+4)%2=0 := by omega
    have h21 : (2*K+1)%2=1 := by omega
    have h22 : (2*K+2)%2=0 := by omega
    simp only [h41,h42,h43,h44,h21,h22,ite_true,show (0:ℕ)≠1 by omega,ite_false]
    rw [show 2*(2*K+1)=4*K+2 by omega, show 4*(K+1)=4*K+4 by omega]
    ring

lemma rawE_odd_eq (K d : ℕ) (hd : d%2=1) : rawE K d = E K d := by
  unfold rawE E
  simp [hd]

lemma rawE_twice_odd (K h : ℕ) (hh : h%2=1) :
    rawE K (2*h) = rawClusterCost K h := by
  have h0 : 2*h ≠ 0 := by omega
  have hm2 : (2*h)%2 ≠ 1 := by omega
  have hm4 : (2*h)%4=2 := by omega
  simp [rawE,h0,hm2,hm4]

lemma rawE_four_mul (K u : ℕ) (hu : 0 < u) :
    rawE K (4*u) = rawClusterCost K (2*u) + (K-u-1) := by
  have h0 : 4*u ≠ 0 := by omega
  have hm2 : (4*u)%2 ≠ 1 := by omega
  have hm4 : (4*u)%4 ≠ 2 := by omega
  simp [rawE,h0,hm2,hm4]

/-- The odd exponents vanish above twice the determinant size. -/
lemma E_odd_gt_two_mul (K d : ℕ) (hd : d%2=1) (hKd : 2*K < d) : E K d = 0 := by
  simp [E,show d≠0 by omega,hd,show ¬ d≤K by omega,show ¬ d≤2*K by omega]

/-- Congruence-class decomposition of the exact raw totient cost. -/
theorem raw_totient_cost_split (K : ℕ) :
    (∑ d ∈ Icc 1 (4*K), (rawE K d : ℝ) * Nat.totient d) =
      (∑ d ∈ Icc 1 (2*K), if d%2=1 then (E K d:ℝ)*Nat.totient d else 0) +
      (∑ h ∈ Icc 1 (2*K), if h%2=1 then (rawClusterCost K h:ℝ)*Nat.totient h else 0) +
      ∑ u ∈ Icc 1 K, ((rawClusterCost K (2*u)+(K-u-1):ℕ):ℝ)*Nat.totient (4*u) := by
  rw [sum_Icc_four_classes]
  have ho : (∑ d ∈ Icc 1 (4*K), if d%2=1 then (rawE K d:ℝ)*Nat.totient d else 0) =
      ∑ d ∈ Icc 1 (2*K), if d%2=1 then (E K d:ℝ)*Nat.totient d else 0 := by
    have hs : Icc 1 (2*K) ⊆ Icc 1 (4*K) := Icc_subset_Icc le_rfl (by omega)
    calc
      _ = ∑ d ∈ Icc 1 (4*K), if d%2=1 then (E K d:ℝ)*Nat.totient d else 0 := by
        apply sum_congr rfl
        intro d hd
        split_ifs with hm
        · rw [rawE_odd_eq K d hm]
        · rfl
      _ = _ := by
        symm
        apply sum_subset hs
        intro d hd hnot
        have hgt : 2*K < d := by have := mem_Icc.mp hd; simp only [mem_Icc] at hnot; omega
        split_ifs with hm
        · rw [E_odd_gt_two_mul K d hm hgt]; simp
        · rfl
  rw [ho]
  congr 1
  · congr 1
    apply sum_congr rfl
    intro h hh
    split_ifs with hm
    · rw [rawE_twice_odd K h hm, Nat.totient_two_mul_of_odd (Nat.odd_iff.mpr hm)]
    · rfl
  · apply sum_congr rfl
    intro u hu
    rw [rawE_four_mul K u (mem_Icc.mp hu).1]

end QCatalan
