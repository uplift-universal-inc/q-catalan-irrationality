import QZeta3.TotientSieve

/-! A four-prime finite sieve with exact periodic moments. -/
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

open Finset
namespace QCatalan

noncomputable def oddRawSieve (n : ℕ) : ℝ :=
  if 2 ∣ n then 0 else
    (if 3 ∣ n then 2/3 else 1) * (if 5 ∣ n then 4/5 else 1) * (if 7 ∣ n then 6/7 else 1)

noncomputable def fourRawSieve (n : ℕ) : ℝ :=
  2 * ((if 3 ∣ n then 2/3 else 1) * (if 5 ∣ n then 4/5 else 1) * (if 7 ∣ n then 6/7 else 1))

noncomputable def rawSieve (n : ℕ) : ℝ :=
  (if 2 ∣ n then 1/2 else 1) *
    ((if 3 ∣ n then 2/3 else 1) * (if 5 ∣ n then 4/5 else 1) * (if 7 ∣ n then 6/7 else 1))

theorem totient_le_rawSieve (n : ℕ) : (Nat.totient n : ℝ) ≤ n * rawSieve n := by
  by_cases hn : n = 0
  · simp [hn]
  have hf : ∀ q ∈ n.primeFactors, (0 : ℚ) ≤ 1 - (q : ℚ)⁻¹ := by
    intro q hq
    have hq1 : (1 : ℚ) ≤ q := by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).one_le
    have hq0 : (0 : ℚ) < q := by linarith
    have := (inv_le_one₀ hq0).mpr hq1
    linarith
  have hs : ({2,3,5,7} : Finset ℕ).filter (fun q => q ∣ n) ⊆ n.primeFactors := by
    intro q hq
    obtain ⟨hq, hqn⟩ := Finset.mem_filter.mp hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl <;>
      exact Nat.mem_primeFactors.mpr ⟨by decide, hqn, hn⟩
  have hprod := Finset.prod_le_prod_of_subset_of_le_one₀ hs hf
    (fun q _ _ => sub_le_self (1 : ℚ) (by positivity : 0 ≤ (q : ℚ)⁻¹))
  have hbound : (Nat.totient n : ℚ) ≤ n *
      ((if 2 ∣ n then 1/2 else 1) *
        ((if 3 ∣ n then 2/3 else 1) * (if 5 ∣ n then 4/5 else 1) *
          (if 7 ∣ n then 6/7 else 1)) : ℚ) := by
    rw [Nat.totient_eq_mul_prod_factors]
    refine (mul_le_mul_of_nonneg_left hprod (by positivity)).trans_eq ?_
    congr 1
    rw [Finset.prod_filter]
    by_cases h2 : 2 ∣ n <;> by_cases h3 : 3 ∣ n <;> by_cases h5 : 5 ∣ n <;>
      by_cases h7 : 7 ∣ n <;> norm_num [h2, h3, h5, h7]
  have hr := (Rat.cast_le (K := ℝ)).mpr hbound
  push_cast at hr
  unfold rawSieve
  split_ifs at hr ⊢ <;> norm_num at hr ⊢ <;> exact hr

theorem odd_totient_le_rawSieve (n : ℕ) (hn : ¬ 2 ∣ n) :
    (Nat.totient n : ℝ) ≤ n * oddRawSieve n := by
  simpa only [rawSieve, oddRawSieve, if_neg hn, one_mul] using totient_le_rawSieve n

theorem four_totient_le_rawSieve (n : ℕ) :
    (Nat.totient (4*n) : ℝ) ≤ n * fourRawSieve n := by
  have h := totient_le_rawSieve (4*n)
  have h2 : 2 ∣ 4*n := by omega
  have h3 : 3 ∣ 4*n ↔ 3 ∣ n := by omega
  have h5 : 5 ∣ 4*n ↔ 5 ∣ n := by omega
  have h7 : 7 ∣ 4*n ↔ 7 ∣ n := by omega
  simp only [rawSieve, h2, ite_true, h3, h5, h7, Nat.cast_mul, Nat.cast_ofNat] at h
  convert h using 1
  unfold fourRawSieve
  ring

theorem oddRawSieve_nonneg (n : ℕ) : 0 ≤ oddRawSieve n := by
  unfold oddRawSieve
  split_ifs <;> norm_num

theorem fourRawSieve_nonneg (n : ℕ) : 0 ≤ fourRawSieve n := by
  unfold fourRawSieve
  split_ifs <;> norm_num

theorem oddRawSieve_le_one (n : ℕ) : oddRawSieve n ≤ 1 := by
  unfold oddRawSieve
  split_ifs <;> norm_num

theorem fourRawSieve_le_two (n : ℕ) : fourRawSieve n ≤ 2 := by
  unfold fourRawSieve
  split_ifs <;> norm_num

theorem oddRawSieve_period (n i : ℕ) : oddRawSieve (210*n+i) = oddRawSieve i := by
  simp [oddRawSieve, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod]

theorem fourRawSieve_period (n i : ℕ) : fourRawSieve (105*n+i) = fourRawSieve i := by
  simp [fourRawSieve, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod]

theorem oddRawSieve_block_moments :
    (∑ i ∈ range 210, oddRawSieve i) = 3072/35 ∧
    (∑ i ∈ range 210, oddRawSieve i * i) = 9216 ∧
    (∑ i ∈ range 210, oddRawSieve i * (i : ℝ)^2) = 1290240 := by
  norm_num [oddRawSieve, Finset.sum_range_succ]

theorem fourRawSieve_block_moments :
    (∑ i ∈ range 105, fourRawSieve i) = 6144/35 ∧
    (∑ i ∈ range 105, fourRawSieve i * i) = 9168 ∧
    (∑ i ∈ range 105, fourRawSieve i * (i : ℝ)^2) = 640080 := by
  norm_num [fourRawSieve, Finset.sum_range_succ]

private theorem sum_weight_shift_one (w : ℕ → ℝ) (L : ℕ) (x : ℝ) :
    (∑ i ∈ range L, w i * (x + i)) = x * (∑ i ∈ range L, w i) +
      ∑ i ∈ range L, w i * i := by
  simp_rw [mul_add]
  rw [sum_add_distrib, ← sum_mul]
  ring

private theorem sum_weight_shift_two (w : ℕ → ℝ) (L : ℕ) (x : ℝ) :
    (∑ i ∈ range L, w i * (x + i)^2) = x^2 * (∑ i ∈ range L, w i) +
      2*x*(∑ i ∈ range L, w i * i) + ∑ i ∈ range L, w i * (i : ℝ)^2 := by
  calc _ = ∑ i ∈ range L, (x^2*w i + 2*x*(w i*i) + w i*(i : ℝ)^2) := by
        apply sum_congr rfl
        intro i hi
        ring
    _ = _ := by simp only [sum_add_distrib, ← mul_sum]

theorem oddRawSieve_sum_blocks (n : ℕ) :
    (∑ i ∈ range (210*n), oddRawSieve i) = (3072/35)*(n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, sum_range_add, ih]
    simp_rw [oddRawSieve_period]
    rw [oddRawSieve_block_moments.1]
    push_cast
    ring

theorem oddRawSieve_firstMoment_blocks (n : ℕ) :
    (∑ i ∈ range (210*n), oddRawSieve i * i) = 9216*(n : ℝ)^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, sum_range_add, ih]
    simp_rw [oddRawSieve_period, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    rw [sum_weight_shift_one, oddRawSieve_block_moments.1, oddRawSieve_block_moments.2.1]
    push_cast
    ring

theorem oddRawSieve_secondMoment_blocks (n : ℕ) :
    (∑ i ∈ range (210*n), oddRawSieve i * (i : ℝ)^2) = 1290240*(n : ℝ)^3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, sum_range_add, ih]
    simp_rw [oddRawSieve_period, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    rw [sum_weight_shift_two, oddRawSieve_block_moments.1,
      oddRawSieve_block_moments.2.1, oddRawSieve_block_moments.2.2]
    push_cast
    ring

theorem fourRawSieve_sum_blocks (n : ℕ) :
    (∑ i ∈ range (105*n), fourRawSieve i) = (6144/35)*(n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, sum_range_add, ih]
    simp_rw [fourRawSieve_period]
    rw [fourRawSieve_block_moments.1]
    push_cast
    ring

theorem fourRawSieve_firstMoment_blocks (n : ℕ) :
    (∑ i ∈ range (105*n), fourRawSieve i * i) = 9216*(n : ℝ)^2 - 48*n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, sum_range_add, ih]
    simp_rw [fourRawSieve_period, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    rw [sum_weight_shift_one, fourRawSieve_block_moments.1, fourRawSieve_block_moments.2.1]
    push_cast
    ring

theorem fourRawSieve_secondMoment_blocks (n : ℕ) :
    (∑ i ∈ range (105*n), fourRawSieve i * (i : ℝ)^2) =
      645120*(n : ℝ)^3 - 5040*(n : ℝ)^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, sum_range_add, ih]
    simp_rw [fourRawSieve_period, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    rw [sum_weight_shift_two, fourRawSieve_block_moments.1,
      fourRawSieve_block_moments.2.1, fourRawSieve_block_moments.2.2]
    push_cast
    ring

private theorem moment_sandwich (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (L n j : ℕ) (hL : 0 < L) :
    (∑ i ∈ range (L*(n/L)), w i * (i : ℝ)^j) ≤
      ∑ i ∈ range n, w i * (i : ℝ)^j ∧
    (∑ i ∈ range n, w i * (i : ℝ)^j) ≤
      ∑ i ∈ range (L*(n/L+1)), w i * (i : ℝ)^j := by
  constructor <;> apply sum_le_sum_of_subset_of_nonneg
  · apply range_mono; exact Nat.mul_div_le n L
  · intro i _ _; exact mul_nonneg (hw i) (by positivity)
  · apply range_mono
    have h := Nat.mod_lt n hL
    have he := Nat.mod_add_div n L
    rw [Nat.mul_add, Nat.mul_one]
    omega
  · intro i _ _; exact mul_nonneg (hw i) (by positivity)

theorem oddRawSieve_sum_bounds (n : ℕ) :
    (512/1225)*(n : ℝ)-200 ≤ ∑ i ∈ range n, oddRawSieve i ∧
    (∑ i ∈ range n, oddRawSieve i) ≤ (512/1225)*(n : ℝ)+200 := by
  have hs := moment_sandwich oddRawSieve oddRawSieve_nonneg 210 n 0 (by norm_num)
  simp only [pow_zero, mul_one, oddRawSieve_sum_blocks] at hs
  have hn : (210 : ℝ)*(n/210 : ℕ) ≤ n := by exact_mod_cast Nat.mul_div_le n 210
  have hn' : (n : ℝ) ≤ 210*((n/210 : ℕ)+1) := by
    exact_mod_cast (show n ≤ 210*(n/210+1) by omega)
  push_cast at hs hn hn'
  constructor <;> linarith [hs.1, hs.2]

theorem fourRawSieve_sum_bounds (n : ℕ) :
    (2048/1225)*(n : ℝ)-400 ≤ ∑ i ∈ range n, fourRawSieve i ∧
    (∑ i ∈ range n, fourRawSieve i) ≤ (2048/1225)*(n : ℝ)+400 := by
  have hs := moment_sandwich fourRawSieve fourRawSieve_nonneg 105 n 0 (by norm_num)
  simp only [pow_zero, mul_one, fourRawSieve_sum_blocks] at hs
  have hn : (105 : ℝ)*(n/105 : ℕ) ≤ n := by exact_mod_cast Nat.mul_div_le n 105
  have hn' : (n : ℝ) ≤ 105*((n/105 : ℕ)+1) := by
    exact_mod_cast (show n ≤ 105*(n/105+1) by omega)
  push_cast at hs hn hn'
  constructor <;> linarith [hs.1, hs.2]

theorem oddRawSieve_firstMoment_bounds (n : ℕ) :
    (256/1225)*(n : ℝ)^2 - 10000*((n : ℝ)+1) ≤ ∑ i ∈ range n, oddRawSieve i * i ∧
    (∑ i ∈ range n, oddRawSieve i * i) ≤ (256/1225)*(n : ℝ)^2 + 10000*((n : ℝ)+1) := by
  have hs := moment_sandwich oddRawSieve oddRawSieve_nonneg 210 n 1 (by norm_num)
  simp only [pow_one, oddRawSieve_firstMoment_blocks] at hs
  have hn : (210 : ℝ)*(n/210 : ℕ) ≤ n := by exact_mod_cast Nat.mul_div_le n 210
  have hn' : (n : ℝ) ≤ 210*((n/210 : ℕ)+1) := by
    exact_mod_cast (show n ≤ 210*(n/210+1) by omega)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hq0 : (0 : ℝ) ≤ (n/210 : ℕ) := Nat.cast_nonneg _
  have hl2 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 210*(n/210 : ℕ)) hn 2
  have hr2 := pow_le_pow_left₀ hn0 hn' 2
  push_cast at hs
  constructor <;> nlinarith [hs.1, hs.2]

theorem fourRawSieve_firstMoment_bounds (n : ℕ) :
    (1024/1225)*(n : ℝ)^2 - 10000*((n : ℝ)+1) ≤ ∑ i ∈ range n, fourRawSieve i * i ∧
    (∑ i ∈ range n, fourRawSieve i * i) ≤ (1024/1225)*(n : ℝ)^2 + 10000*((n : ℝ)+1) := by
  have hs := moment_sandwich fourRawSieve fourRawSieve_nonneg 105 n 1 (by norm_num)
  simp only [pow_one, fourRawSieve_firstMoment_blocks] at hs
  have hn : (105 : ℝ)*(n/105 : ℕ) ≤ n := by exact_mod_cast Nat.mul_div_le n 105
  have hn' : (n : ℝ) ≤ 105*((n/105 : ℕ)+1) := by
    exact_mod_cast (show n ≤ 105*(n/105+1) by omega)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hq0 : (0 : ℝ) ≤ (n/105 : ℕ) := Nat.cast_nonneg _
  have hl2 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 105*(n/105 : ℕ)) hn 2
  have hr2 := pow_le_pow_left₀ hn0 hn' 2
  push_cast at hs
  constructor <;> nlinarith [hs.1, hs.2]

theorem oddRawSieve_secondMoment_bounds (n : ℕ) :
    (512/3675)*(n : ℝ)^3 - 2000000*((n : ℝ)+1)^2 ≤ ∑ i ∈ range n, oddRawSieve i * (i : ℝ)^2 ∧
    (∑ i ∈ range n, oddRawSieve i * (i : ℝ)^2) ≤ (512/3675)*(n : ℝ)^3 + 2000000*((n : ℝ)+1)^2 := by
  have hs := moment_sandwich oddRawSieve oddRawSieve_nonneg 210 n 2 (by norm_num)
  simp only [oddRawSieve_secondMoment_blocks] at hs
  have hn : (210 : ℝ)*(n/210 : ℕ) ≤ n := by exact_mod_cast Nat.mul_div_le n 210
  have hn' : (n : ℝ) ≤ 210*((n/210 : ℕ)+1) := by
    exact_mod_cast (show n ≤ 210*(n/210+1) by omega)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hq0 : (0 : ℝ) ≤ (n/210 : ℕ) := Nat.cast_nonneg _
  have hl2 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 210*(n/210 : ℕ)) hn 2
  have hl3 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 210*(n/210 : ℕ)) hn 3
  have hr3 := pow_le_pow_left₀ hn0 hn' 3
  push_cast at hs
  constructor <;> nlinarith [hs.1, hs.2, sq_nonneg (n : ℝ)]

theorem fourRawSieve_secondMoment_bounds (n : ℕ) :
    (2048/3675)*(n : ℝ)^3 - 2000000*((n : ℝ)+1)^2 ≤ ∑ i ∈ range n, fourRawSieve i * (i : ℝ)^2 ∧
    (∑ i ∈ range n, fourRawSieve i * (i : ℝ)^2) ≤ (2048/3675)*(n : ℝ)^3 + 2000000*((n : ℝ)+1)^2 := by
  have hs := moment_sandwich fourRawSieve fourRawSieve_nonneg 105 n 2 (by norm_num)
  simp only [fourRawSieve_secondMoment_blocks] at hs
  have hn : (105 : ℝ)*(n/105 : ℕ) ≤ n := by exact_mod_cast Nat.mul_div_le n 105
  have hn' : (n : ℝ) ≤ 105*((n/105 : ℕ)+1) := by
    exact_mod_cast (show n ≤ 105*(n/105+1) by omega)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hq0 : (0 : ℝ) ≤ (n/105 : ℕ) := Nat.cast_nonneg _
  have hl2 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 105*(n/105 : ℕ)) hn 2
  have hl3 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 105*(n/105 : ℕ)) hn 3
  have hr3 := pow_le_pow_left₀ hn0 hn' 3
  push_cast at hs
  constructor <;> nlinarith [hs.1, hs.2, sq_nonneg (n : ℝ)]

end QCatalan
