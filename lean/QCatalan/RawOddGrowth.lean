import QCatalan.Growth
import QCatalan.RawTotientSieve

open Finset
namespace QCatalan

theorem oddInnerTerm_low_raw (K d : ℕ) (hdK : d ≤ K) :
    oddInnerTerm K d ≤ oddLowCost K d * oddRawSieve d := by
  by_cases ho : d%2=1
  · have hd : 0 < d := by omega
    have hn : ¬ 2 ∣ d := by omega
    simp only [oddInnerTerm,ho,ite_true]
    calc
      (E K d:ℝ)*Nat.totient d ≤ (E K d:ℝ)*(d*oddRawSieve d) :=
        mul_le_mul_of_nonneg_left (odd_totient_le_rawSieve d hn) (by positivity)
      _ ≤ oddLowCost K d * oddRawSieve d := by
        have h := mul_le_mul_of_nonneg_right (E_odd_inner_weight_bound K d hd ho hdK)
          (oddRawSieve_nonneg d)
        simpa [oddLowCost,mul_assoc] using h
  · have he : 2 ∣ d := by omega
    simp [oddInnerTerm,oddRawSieve,ho,he]

theorem oddInnerTerm_high_raw (K d : ℕ) (hdK : d ≤ K) (hh : K < 3*d) :
    oddInnerTerm K d ≤ 2*K*d*oddRawSieve d := by
  by_cases ho : d%2=1
  · have hd : 0 < d := by omega
    have hn : ¬ 2 ∣ d := by omega
    simp only [oddInnerTerm,ho,ite_true,
      E_odd_inner_high K d hd ho hdK hh,Nat.cast_mul,Nat.cast_ofNat]
    have h := mul_le_mul_of_nonneg_left (odd_totient_le_rawSieve d hn)
      (show (0:ℝ) ≤ 2*K by positivity)
    simpa [mul_assoc] using h
  · have he : 2 ∣ d := by omega
    simp [oddInnerTerm,oddRawSieve,ho,he]

theorem oddLowCost_sum_raw (K M : ℕ) :
    (∑ d ∈ range M, oddLowCost K d * oddRawSieve d) =
      (K : ℝ) ^ 2 / 4 * (∑ d ∈ range M, oddRawSieve d) +
      K * (∑ d ∈ range M, oddRawSieve d * d) +
      17 / 16 * (∑ d ∈ range M, oddRawSieve d * (d : ℝ) ^ 2) := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  unfold oddLowCost
  ring

theorem oddInnerTerm_sum_sieve_raw (K : ℕ) :
    (∑ d ∈ range (K + 1), oddInnerTerm K d) ≤
      (∑ d ∈ range (K / 3 + 1), oddLowCost K d * oddRawSieve d) +
      2 * K * (∑ d ∈ range (K + 1), oddRawSieve d * d) -
      2 * K * (∑ d ∈ range (K / 3 + 1), oddRawSieve d * d) := by
  have hsplit : K + 1 = (K / 3 + 1) + ((K + 1) - (K / 3 + 1)) := by omega
  conv_lhs => rw [hsplit, Finset.sum_range_add]
  have hlo : (∑ d ∈ range (K / 3 + 1), oddInnerTerm K d) ≤
      ∑ d ∈ range (K / 3 + 1), oddLowCost K d * oddRawSieve d := by
    apply Finset.sum_le_sum
    intro d hd
    apply oddInnerTerm_low_raw
    have := Finset.mem_range.mp hd
    omega
  have hhi : (∑ i ∈ range ((K + 1) - (K / 3 + 1)), oddInnerTerm K (K / 3 + 1 + i)) ≤
      ∑ i ∈ range ((K + 1) - (K / 3 + 1)),
        2 * K * ((K / 3 + 1 + i : ℕ) : ℝ) * oddRawSieve (K / 3 + 1 + i) := by
    apply Finset.sum_le_sum
    intro i hi
    apply oddInnerTerm_high_raw
    · have := Finset.mem_range.mp hi; omega
    · omega
  have hh := Finset.sum_range_add (fun d => 2 * (K : ℝ) * d * oddRawSieve d)
    (K / 3 + 1) ((K + 1) - (K / 3 + 1))
  rw [← hsplit] at hh
  have heq (M : ℕ) : (∑ d ∈ range M, 2 * (K : ℝ) * d * oddRawSieve d) =
      2 * K * (∑ d ∈ range M, oddRawSieve d * d) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [heq, heq] at hh
  linarith

/-- The full inner odd-order contribution is bounded by a rational cubic. -/
theorem oddInnerTerm_sum_le_raw (K : ℕ) :
    (∑ d ∈ range (K + 1), oddInnerTerm K d) ≤
      43168 / 99225 * (K : ℝ) ^ 3 + 1000000000 * ((K : ℝ) + 1) ^ 2 := by
  have hs := oddInnerTerm_sum_sieve_raw K
  rw [oddLowCost_sum_raw] at hs
  let M := K / 3 + 1
  let N := K + 1
  have hm0 := mul_le_mul_of_nonneg_left (oddRawSieve_sum_bounds M).2
    (show (0 : ℝ) ≤ (K : ℝ) ^ 2 / 4 by positivity)
  have hm1 := mul_le_mul_of_nonneg_left (oddRawSieve_firstMoment_bounds M).1
    (show (0 : ℝ) ≤ K by positivity)
  have hm2 := mul_le_mul_of_nonneg_left (oddRawSieve_secondMoment_bounds M).2
    (show (0 : ℝ) ≤ 17 / 16 by norm_num)
  have hn1 := mul_le_mul_of_nonneg_left (oddRawSieve_firstMoment_bounds N).2
    (show (0 : ℝ) ≤ 2 * K by positivity)
  have hbound : (∑ d ∈ range (K + 1), oddInnerTerm K d) ≤
      (K : ℝ) ^ 2 / 4 * (512 / 1225 * M + 200) -
      K * (256 / 1225 * (M : ℝ) ^ 2 - 10000 * (M + 1)) +
      17 / 16 * (512 / 3675 * (M : ℝ) ^ 3 + 2000000 * (M + 1) ^ 2) +
      2 * K * (256 / 1225 * (N : ℝ) ^ 2 + 10000 * (N + 1)) := by
    dsimp [M, N] at *
    nlinarith only [hs, hm0, hm1, hm2, hn1]
  refine hbound.trans ?_
  dsimp [M, N]
  have hr : K % 3 < 3 := Nat.mod_lt K (by norm_num)
  have hK : (K : ℝ) = 3 * (K / 3 : ℕ) + (K % 3 : ℕ) := by
    exact_mod_cast (show K = 3 * (K / 3) + K % 3 by omega)
  have hq : (0 : ℝ) ≤ (K / 3 : ℕ) := by positivity
  push_cast
  rw [hK]
  interval_cases h : K % 3 <;> norm_num [h] <;> nlinarith

/-- The exact odd exponent in the collision-free outer interval. -/
theorem oddInnerTerm_outer_raw (K d : ℕ) (hKd : K < d) (hdK : d ≤ 2*K) :
    oddInnerTerm K d ≤ oddRawSieve d * (((2:ℝ)*K+1)*d-(d:ℝ)^2) := by
  by_cases ho : d%2=1
  · have hd0 : d ≠ 0 := by omega
    have hn : ¬ 2 ∣ d := by omega
    have hpos : (0:ℝ) ≤ 2*K+1-d := by
      have hdR : (d:ℝ) ≤ 2*(K:ℝ)+1 := by exact_mod_cast (show d ≤ 2*K+1 by omega)
      linarith
    have heN : 2*(K-(d-1)/2)+d=2*K+1 := by omega
    have heR : (2:ℝ)*((K-(d-1)/2:ℕ):ℝ) = 2*K+1-d := by
      have he : (2:ℝ)*((K-(d-1)/2:ℕ):ℝ)+(d:ℝ)=2*K+1 := by exact_mod_cast heN
      linarith
    simp only [oddInnerTerm,ho,ite_true,E,hd0,ite_false,show ¬d≤K by omega,hdK]
    rw [Nat.cast_mul,Nat.cast_ofNat,heR]
    have ht := mul_le_mul_of_nonneg_left (odd_totient_le_rawSieve d hn) hpos
    nlinarith only [ht]
  · have he : 2 ∣ d := by omega
    simp [oddInnerTerm,oddRawSieve,ho,he]

/-- Prefix-moment subtraction bounds the whole collision-free odd interval. -/
theorem oddInnerTerm_outer_sum_le_raw (K : ℕ) :
    (∑ i ∈ range K, oddInnerTerm K (K+1+i)) ≤
      1024/3675*(K:ℝ)^3 + 1000000000*((K:ℝ)+1)^2 := by
  let f : ℕ → ℝ := fun d => oddRawSieve d * (((2:ℝ)*K+1)*d-(d:ℝ)^2)
  have hs : (∑ i ∈ range K, oddInnerTerm K (K+1+i)) ≤
      ∑ i ∈ range K, f (K+1+i) := by
    apply sum_le_sum
    intro i hi
    exact oddInnerTerm_outer_raw K (K+1+i) (by omega) (by have := mem_range.mp hi; omega)
  have heq (M : ℕ) : (∑ d ∈ range M, f d) =
      (2*K+1)*(∑ d ∈ range M, oddRawSieve d*d) -
      ∑ d ∈ range M, oddRawSieve d*(d:ℝ)^2 := by
    rw [mul_sum,←sum_sub_distrib]
    apply sum_congr rfl
    intro d hd
    dsimp [f]
    ring
  have ht := sum_range_add f (K+1) K
  rw [show K+1+K=2*K+1 by omega,heq,heq] at ht
  have hM1 := (oddRawSieve_firstMoment_bounds (2*K+1)).2
  have hm1 := (oddRawSieve_firstMoment_bounds (K+1)).1
  have hM2 := (oddRawSieve_secondMoment_bounds (2*K+1)).1
  have hm2 := (oddRawSieve_secondMoment_bounds (K+1)).2
  have hm := mul_le_mul_of_nonneg_left (sub_le_sub hM1 hm1)
    (show (0:ℝ) ≤ 2*K+1 by positivity)
  push_cast at hm hM2 hm2
  have hbound : (∑ i ∈ range K, oddInnerTerm K (K+1+i)) ≤
      (2*K+1)*((256/1225)*((2:ℝ)*K+1)^2+10000*(2*K+1+1) -
        ((256/1225)*((K:ℝ)+1)^2-10000*(K+1+1))) -
      ((512/3675)*((2:ℝ)*K+1)^3-2000000*(2*K+1+1)^2) +
      ((512/3675)*((K:ℝ)+1)^3+2000000*(K+1+1)^2) := by
    nlinarith only [hs,ht,hm,hM2,hm2]
  refine hbound.trans ?_
  have hK : (0:ℝ) ≤ K := Nat.cast_nonneg _
  nlinarith [sq_nonneg (K:ℝ)]

/-- Complete odd-order contribution for the direct four-prime sieve. -/
theorem oddInnerTerm_sum_le_raw_full (K : ℕ) :
    (∑ d ∈ Icc 1 (2*K), oddInnerTerm K d) ≤
      70816/99225*(K:ℝ)^3 + 2000000000*((K:ℝ)+1)^2 := by
  have he : (∑ d ∈ Icc 1 (2*K), oddInnerTerm K d) =
      ∑ d ∈ range (2*K+1), oddInnerTerm K d := by
    have hset : range (2*K+1) = insert 0 (Icc 1 (2*K)) := by
      ext d
      simp only [mem_range,mem_insert,mem_Icc]
      omega
    rw [hset,sum_insert (by simp)]
    simp [oddInnerTerm]
  rw [he,show 2*K+1=(K+1)+K by omega,sum_range_add]
  have hi := oddInnerTerm_sum_le_raw K
  have ho := oddInnerTerm_outer_sum_le_raw K
  nlinarith only [hi,ho]

end QCatalan
