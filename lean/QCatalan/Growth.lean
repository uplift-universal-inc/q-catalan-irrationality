import QCatalan.Defs
import QZeta3.TotientSieve
import QZeta3.CyclotomicBounds

/-! # Elementary congruence-class bounds for cyclotomic growth

These bounds concern the actual Euler totients in the q-Catalan exponents.
They use only the prime factors 2 and 3 and retain the odd and fourfold order
classes separately.
-/

open Polynomial Finset Real

namespace QCatalan

noncomputable def oddSieve (n : ℕ) : ℝ :=
  if n % 2 = 1 then QZeta3.sieveWeight n else 0

noncomputable def fourSieve (n : ℕ) : ℝ :=
  if 3 ∣ n then 4 / 3 else 2

theorem oddSieve_nonneg (n : ℕ) : 0 ≤ oddSieve n := by
  unfold oddSieve
  split_ifs
  · exact QZeta3.sieveWeight_nonneg n
  · norm_num

theorem totient_odd_le_sieve (n : ℕ) :
    (if n % 2 = 1 then (Nat.totient n : ℝ) else 0) ≤ n * oddSieve n := by
  unfold oddSieve
  split_ifs
  · exact QZeta3.totient_le_sieveWeight n
  · simp

theorem totient_four_le_sieve (n : ℕ) :
    (Nat.totient (4 * n) : ℝ) ≤ n * fourSieve n := by
  have h := QZeta3.totient_le_sieveWeight (4 * n)
  have h3 : 3 ∣ 4 * n ↔ 3 ∣ n := by
    rw [Nat.prime_three.dvd_mul]
    norm_num
  have h2 : 2 ∣ 4 * n := dvd_mul_of_dvd_left (by norm_num) _
  simp only [QZeta3.sieveWeight, h2, ite_true, h3] at h
  unfold fourSieve
  split_ifs at h ⊢ <;> push_cast at h <;> nlinarith

theorem oddSieve_six_mul_add (n i : ℕ) : oddSieve (6 * n + i) = oddSieve i := by
  simp [oddSieve, QZeta3.sieveWeight, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod]

theorem oddSieve_sum_blocks (n : ℕ) :
    ∑ i ∈ range (6 * n), oddSieve i = 8 / 3 * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    simp_rw [oddSieve_six_mul_add]
    norm_num [oddSieve, QZeta3.sieveWeight, Finset.sum_range_succ]
    ring

theorem oddSieve_firstMoment_blocks (n : ℕ) :
    ∑ i ∈ range (6 * n), oddSieve i * (i : ℝ) = 8 * (n : ℝ) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    simp_rw [oddSieve_six_mul_add]
    norm_num [oddSieve, QZeta3.sieveWeight, Finset.sum_range_succ]
    ring

theorem oddSieve_secondMoment_blocks (n : ℕ) :
    ∑ i ∈ range (6 * n), oddSieve i * (i : ℝ) ^ 2 = 32 * (n : ℝ) ^ 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    simp_rw [oddSieve_six_mul_add]
    norm_num [oddSieve, QZeta3.sieveWeight, Finset.sum_range_succ]
    ring

theorem oddSieve_moment_sandwich (n j : ℕ) :
    (∑ i ∈ range (6 * (n / 6)), oddSieve i * (i : ℝ) ^ j) ≤
      ∑ i ∈ range n, oddSieve i * (i : ℝ) ^ j ∧
    (∑ i ∈ range n, oddSieve i * (i : ℝ) ^ j) ≤
      ∑ i ∈ range (6 * (n / 6 + 1)), oddSieve i * (i : ℝ) ^ j := by
  constructor <;> apply Finset.sum_le_sum_of_subset_of_nonneg
  · apply Finset.range_mono; omega
  · intro i _ _; exact mul_nonneg (oddSieve_nonneg i) (by positivity)
  · apply Finset.range_mono; omega
  · intro i _ _; exact mul_nonneg (oddSieve_nonneg i) (by positivity)

theorem oddSieve_firstMoment_bounds (n : ℕ) :
    2 / 9 * (n : ℝ) ^ 2 - 20 * ((n : ℝ) + 1) ≤
      ∑ i ∈ range n, oddSieve i * i ∧
    (∑ i ∈ range n, oddSieve i * i) ≤
      2 / 9 * (n : ℝ) ^ 2 + 20 * ((n : ℝ) + 1) := by
  have hs := oddSieve_moment_sandwich n 1
  simp only [pow_one, oddSieve_firstMoment_blocks] at hs
  have hr : n % 6 < 6 := Nat.mod_lt n (by norm_num)
  have hn : (n : ℝ) = 6 * (n / 6 : ℕ) + (n % 6 : ℕ) := by
    exact_mod_cast (show n = 6 * (n / 6) + n % 6 by omega)
  have hq : (0 : ℝ) ≤ (n / 6 : ℕ) := by positivity
  push_cast at hs
  rw [hn]
  interval_cases h : n % 6 <;> norm_num [h] <;> constructor <;> nlinarith [hs.1, hs.2]

theorem oddSieve_secondMoment_bounds (n : ℕ) :
    4 / 27 * (n : ℝ) ^ 3 - 100 * ((n : ℝ) + 1) ^ 2 ≤
      ∑ i ∈ range n, oddSieve i * (i : ℝ) ^ 2 ∧
    (∑ i ∈ range n, oddSieve i * (i : ℝ) ^ 2) ≤
      4 / 27 * (n : ℝ) ^ 3 + 100 * ((n : ℝ) + 1) ^ 2 := by
  have hs := oddSieve_moment_sandwich n 2
  simp only [oddSieve_secondMoment_blocks] at hs
  have hr : n % 6 < 6 := Nat.mod_lt n (by norm_num)
  have hn : (n : ℝ) = 6 * (n / 6 : ℕ) + (n % 6 : ℕ) := by
    exact_mod_cast (show n = 6 * (n / 6) + n % 6 by omega)
  have hq : (0 : ℝ) ≤ (n / 6 : ℕ) := by positivity
  push_cast at hs
  rw [hn]
  interval_cases h : n % 6 <;> norm_num [h] <;> constructor <;> nlinarith [hs.1, hs.2]

theorem fourSieve_nonneg (n : ℕ) : 0 ≤ fourSieve n := by
  unfold fourSieve
  split_ifs <;> norm_num

theorem fourSieve_three_mul_add (n i : ℕ) : fourSieve (3 * n + i) = fourSieve i := by
  simp [fourSieve, Nat.dvd_iff_mod_eq_zero, Nat.add_mod]

theorem fourSieve_firstMoment_blocks (n : ℕ) :
    ∑ i ∈ range (3 * n), fourSieve i * (i : ℝ) = 8 * (n : ℝ) ^ 2 - 2 * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    simp_rw [fourSieve_three_mul_add]
    norm_num [fourSieve, Finset.sum_range_succ]
    ring

theorem fourSieve_secondMoment_blocks (n : ℕ) :
    ∑ i ∈ range (3 * n), fourSieve i * (i : ℝ) ^ 2 = 16 * (n : ℝ) ^ 3 - 6 * (n : ℝ) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    simp_rw [fourSieve_three_mul_add]
    norm_num [fourSieve, Finset.sum_range_succ]
    ring

theorem fourSieve_moment_sandwich (n j : ℕ) :
    (∑ i ∈ range (3 * (n / 3)), fourSieve i * (i : ℝ) ^ j) ≤
      ∑ i ∈ range n, fourSieve i * (i : ℝ) ^ j ∧
    (∑ i ∈ range n, fourSieve i * (i : ℝ) ^ j) ≤
      ∑ i ∈ range (3 * (n / 3 + 1)), fourSieve i * (i : ℝ) ^ j := by
  constructor <;> apply Finset.sum_le_sum_of_subset_of_nonneg
  · apply Finset.range_mono; omega
  · intro i _ _; exact mul_nonneg (fourSieve_nonneg i) (by positivity)
  · apply Finset.range_mono; omega
  · intro i _ _; exact mul_nonneg (fourSieve_nonneg i) (by positivity)

theorem fourSieve_firstMoment_bounds (n : ℕ) :
    8 / 9 * (n : ℝ) ^ 2 - 20 * ((n : ℝ) + 1) ≤
      ∑ i ∈ range n, fourSieve i * i ∧
    (∑ i ∈ range n, fourSieve i * i) ≤
      8 / 9 * (n : ℝ) ^ 2 + 20 * ((n : ℝ) + 1) := by
  have hs := fourSieve_moment_sandwich n 1
  simp only [pow_one, fourSieve_firstMoment_blocks] at hs
  have hr : n % 3 < 3 := Nat.mod_lt n (by norm_num)
  have hn : (n : ℝ) = 3 * (n / 3 : ℕ) + (n % 3 : ℕ) := by
    exact_mod_cast (show n = 3 * (n / 3) + n % 3 by omega)
  have hq : (0 : ℝ) ≤ (n / 3 : ℕ) := by positivity
  push_cast at hs
  rw [hn]
  interval_cases h : n % 3 <;> norm_num [h] <;> constructor <;> nlinarith [hs.1, hs.2]

theorem fourSieve_secondMoment_bounds (n : ℕ) :
    16 / 27 * (n : ℝ) ^ 3 - 100 * ((n : ℝ) + 1) ^ 2 ≤
      ∑ i ∈ range n, fourSieve i * (i : ℝ) ^ 2 ∧
    (∑ i ∈ range n, fourSieve i * (i : ℝ) ^ 2) ≤
      16 / 27 * (n : ℝ) ^ 3 + 100 * ((n : ℝ) + 1) ^ 2 := by
  have hs := fourSieve_moment_sandwich n 2
  simp only [fourSieve_secondMoment_blocks] at hs
  have hr : n % 3 < 3 := Nat.mod_lt n (by norm_num)
  have hn : (n : ℝ) = 3 * (n / 3 : ℕ) + (n % 3 : ℕ) := by
    exact_mod_cast (show n = 3 * (n / 3) + n % 3 by omega)
  have hq : (0 : ℝ) ≤ (n / 3 : ℕ) := by positivity
  push_cast at hs
  rw [hn]
  interval_cases h : n % 3 <;> norm_num [h] <;> constructor <;> nlinarith [hs.1, hs.2]

/-- The odd summatory totient bound with explicit linear error. -/
theorem sum_totient_odd_le (N : ℕ) :
    (∑ d ∈ range N, if d % 2 = 1 then (Nat.totient d : ℝ) else 0) ≤
      2 / 9 * (N : ℝ) ^ 2 + 20 * ((N : ℝ) + 1) := by
  refine le_trans (Finset.sum_le_sum fun d _ => totient_odd_le_sieve d) ?_
  simpa [mul_comm] using (oddSieve_firstMoment_bounds N).2

/-- The fourfold summatory totient bound with explicit linear error. -/
theorem sum_totient_four_le (N : ℕ) :
    (∑ u ∈ range N, (Nat.totient (4 * u) : ℝ)) ≤
      8 / 9 * (N : ℝ) ^ 2 + 20 * ((N : ℝ) + 1) := by
  refine le_trans (Finset.sum_le_sum fun u _ => totient_four_le_sieve u) ?_
  simpa [mul_comm] using (fourSieve_firstMoment_bounds N).2

/-- A finite weighted linear ramp, before choosing the integer cutoff. -/
theorem oddSieve_ramp_le (N : ℕ) (K a : ℝ) (hK : 0 ≤ K) (ha : 0 ≤ a) :
    (∑ d ∈ range N, oddSieve d * d * (K - a * d)) ≤
      2 / 9 * K * (N : ℝ) ^ 2 - 4 / 27 * a * (N : ℝ) ^ 3 +
        20 * K * ((N : ℝ) + 1) + 100 * a * ((N : ℝ) + 1) ^ 2 := by
  have h₁ := mul_le_mul_of_nonneg_left (oddSieve_firstMoment_bounds N).2 hK
  have h₂ := mul_le_mul_of_nonneg_left (oddSieve_secondMoment_bounds N).1 ha
  have hs : (∑ d ∈ range N, oddSieve d * d * (K - a * d)) =
      K * (∑ d ∈ range N, oddSieve d * d) -
        a * (∑ d ∈ range N, oddSieve d * (d : ℝ) ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [hs]
  nlinarith

/-- Scaling removes divisions; the cubic maximum is exact. -/
theorem oddSieve_ramp_scaled_le (N : ℕ) (K a : ℝ) (hK : 0 ≤ K) (ha : 0 ≤ a) :
    a ^ 2 * (∑ d ∈ range N, oddSieve d * d * (K - a * d)) ≤
      2 / 27 * K ^ 3 +
        a ^ 2 * (20 * K * ((N : ℝ) + 1) + 100 * a * ((N : ℝ) + 1) ^ 2) := by
  have h := mul_le_mul_of_nonneg_left (oddSieve_ramp_le N K a hK ha) (sq_nonneg a)
  have hfac : 0 ≤ (a * (N : ℝ) - K) ^ 2 * (2 * a * N + K) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  nlinarith

/-- The floor defining the cluster cost has a uniform quadratic bound. -/
theorem clusterCost_le_quadratic (m : ℕ) :
    (clusterCost m : ℝ) ≤ ((m : ℝ) + 2) ^ 2 / 4 := by
  unfold clusterCost
  split_ifs with hm
  · subst m; norm_num
  · have h := Nat.div_mul_le_self ((m + 2) ^ 2) 4
    have h' : (((m + 2) ^ 2 / 4 : ℕ) : ℝ) * 4 ≤ ((m : ℝ) + 2) ^ 2 := by
      exact_mod_cast h
    linarith

/-- A uniform bound on the actual odd-order exponent, with no floor left over. -/
theorem E_odd_inner_weight_bound (K d : ℕ) (hd : 0 < d) (hodd : d % 2 = 1)
    (hdK : d ≤ K) :
    (E K d : ℝ) * d ≤ (K : ℝ) ^ 2 / 4 + K * d + 17 / 16 * (d : ℝ) ^ 2 := by
  have ht : K % d ≤ d := (Nat.mod_lt K hd).le
  have hqd : (K : ℝ) = (d : ℝ) * (K / d : ℕ) + (K % d : ℕ) := by
    exact_mod_cast (Nat.div_add_mod K d).symm
  have ht0 : (0 : ℝ) ≤ (K % d : ℕ) := by positivity
  have hdt0 : (0 : ℝ) ≤ (d : ℝ) - (K % d : ℕ) := by
    have : ((K % d : ℕ) : ℝ) ≤ d := by exact_mod_cast ht
    linarith
  have hc₀ := mul_le_mul_of_nonneg_left (clusterCost_le_quadratic (K / d)) hdt0
  have hc₁ := mul_le_mul_of_nonneg_left (clusterCost_le_quadratic (K / d + 1)) ht0
  have hc := mul_le_mul_of_nonneg_right (add_le_add hc₁ hc₀) (show (0 : ℝ) ≤ d by positivity)
  simp only [E, Nat.ne_of_gt hd, ite_false, hodd, ite_true, hdK,
    Nat.cast_add, Nat.cast_mul, Nat.cast_sub ht] at *
  rw [hqd]
  push_cast at hc
  nlinarith [sq_nonneg (2 * ((K % d : ℕ) : ℝ) - d)]

/-- The inner odd exponent is exactly linear throughout the large-order range. -/
theorem E_odd_inner_high (K d : ℕ) (hd : 0 < d) (hodd : d % 2 = 1)
    (hdK : d ≤ K) (hhigh : K < 3 * d) : E K d = 2 * K := by
  have hqlo : 1 ≤ K / d := (Nat.le_div_iff_mul_le hd).mpr (by simpa using hdK)
  have hqhi : K / d < 3 := (Nat.div_lt_iff_lt_mul hd).mpr (by simpa [Nat.mul_comm] using hhigh)
  have ht : K % d ≤ d := (Nat.mod_lt K hd).le
  have hqd := Nat.div_add_mod K d
  simp only [E, Nat.ne_of_gt hd, ite_false, hodd, ite_true, hdK]
  interval_cases hq : K / d <;> norm_num [hq, clusterCost] at * <;> omega

theorem log_CK_eq (p K : ℕ) (hp : 2 ≤ p) :
    Real.log (CK p K : ℝ) =
      ∑ d ∈ Icc 1 (4 * K), (E K d : ℝ) * Real.log (Phi p d : ℝ) := by
  unfold CK
  push_cast
  rw [Real.log_prod]
  · apply Finset.sum_congr rfl
    intro d hd
    rw [Real.log_pow]
  · intro d hd
    apply pow_ne_zero
    have hphi : (0 : ℝ) < Phi p d := by
      have : 0 < Phi p d := Polynomial.cyclotomic_pos' d
        (by exact_mod_cast (show 1 < p by omega))
      exact_mod_cast this
    exact ne_of_gt hphi

/-- Reduction of the logarithmic growth problem to two finite exponent sums. -/
theorem log_CK_le_weighted_totient (p K : ℕ) (hp : 2 ≤ p) :
    Real.log (CK p K : ℝ) ≤
      Real.log p * (∑ d ∈ Icc 1 (4 * K), (E K d : ℝ) * Nat.totient d) +
      2 * (∑ d ∈ Icc 1 (4 * K), (E K d : ℝ)) := by
  rw [log_CK_eq p K hp]
  calc
    _ ≤ (∑ d ∈ Icc 1 (4 * K), (E K d : ℝ) *
        ((Nat.totient d : ℝ) * Real.log p + 2)) := by
      apply Finset.sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have h := QZeta3.cyclotomic_error_bound hp d (Finset.mem_Icc.mp hd).1
      have hh := le_abs_self (Real.log (Phi p d : ℝ) - (Nat.totient d : ℝ) * Real.log p)
      change |Real.log (Phi p d : ℝ) - (Nat.totient d : ℝ) * Real.log p| ≤ 2 at h
      linarith
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      ring

theorem oddSieve_sum_bounds (n : ℕ) :
    4 / 9 * (n : ℝ) - 4 ≤ ∑ i ∈ range n, oddSieve i ∧
    (∑ i ∈ range n, oddSieve i) ≤ 4 / 9 * (n : ℝ) + 4 := by
  have hs := oddSieve_moment_sandwich n 0
  simp only [pow_zero, mul_one, oddSieve_sum_blocks] at hs
  have hn : (6 : ℝ) * (n / 6 : ℕ) ≤ n := by exact_mod_cast Nat.mul_div_le n 6
  have hn' : (n : ℝ) ≤ 6 * ((n / 6 : ℕ) + 1) := by
    exact_mod_cast (show n ≤ 6 * (n / 6 + 1) by omega)
  push_cast at hs hn hn'
  constructor <;> linarith [hs.1, hs.2]

noncomputable def oddInnerTerm (K d : ℕ) : ℝ :=
  if d % 2 = 1 then (E K d : ℝ) * Nat.totient d else 0

noncomputable def oddLowCost (K d : ℕ) : ℝ :=
  (K : ℝ) ^ 2 / 4 + K * d + 17 / 16 * (d : ℝ) ^ 2

theorem oddInnerTerm_low (K d : ℕ) (hdK : d ≤ K) :
    oddInnerTerm K d ≤ oddLowCost K d * oddSieve d := by
  by_cases ho : d % 2 = 1
  · have hd : 0 < d := by omega
    simp only [oddInnerTerm, oddSieve, ho, ite_true]
    calc
      (E K d : ℝ) * Nat.totient d ≤ (E K d : ℝ) * (d * QZeta3.sieveWeight d) :=
        mul_le_mul_of_nonneg_left (QZeta3.totient_le_sieveWeight d) (by positivity)
      _ ≤ oddLowCost K d * QZeta3.sieveWeight d := by
        have h := mul_le_mul_of_nonneg_right (E_odd_inner_weight_bound K d hd ho hdK)
          (QZeta3.sieveWeight_nonneg d)
        simpa [oddLowCost, mul_assoc] using h
  · simp [oddInnerTerm, oddSieve, ho]

theorem oddInnerTerm_high (K d : ℕ) (hdK : d ≤ K) (hh : K < 3 * d) :
    oddInnerTerm K d ≤ 2 * K * d * oddSieve d := by
  by_cases ho : d % 2 = 1
  · have hd : 0 < d := by omega
    simp only [oddInnerTerm, oddSieve, ho, ite_true,
      E_odd_inner_high K d hd ho hdK hh, Nat.cast_mul, Nat.cast_ofNat]
    have h := mul_le_mul_of_nonneg_left (QZeta3.totient_le_sieveWeight d)
      (show (0 : ℝ) ≤ 2 * K by positivity)
    simpa [mul_assoc] using h
  · simp [oddInnerTerm, oddSieve, ho]

theorem oddLowCost_sum (K M : ℕ) :
    (∑ d ∈ range M, oddLowCost K d * oddSieve d) =
      (K : ℝ) ^ 2 / 4 * (∑ d ∈ range M, oddSieve d) +
      K * (∑ d ∈ range M, oddSieve d * d) +
      17 / 16 * (∑ d ∈ range M, oddSieve d * (d : ℝ) ^ 2) := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  unfold oddLowCost
  ring

theorem oddInnerTerm_sum_sieve (K : ℕ) :
    (∑ d ∈ range (K + 1), oddInnerTerm K d) ≤
      (∑ d ∈ range (K / 3 + 1), oddLowCost K d * oddSieve d) +
      2 * K * (∑ d ∈ range (K + 1), oddSieve d * d) -
      2 * K * (∑ d ∈ range (K / 3 + 1), oddSieve d * d) := by
  have hsplit : K + 1 = (K / 3 + 1) + ((K + 1) - (K / 3 + 1)) := by omega
  conv_lhs => rw [hsplit, Finset.sum_range_add]
  have hlo : (∑ d ∈ range (K / 3 + 1), oddInnerTerm K d) ≤
      ∑ d ∈ range (K / 3 + 1), oddLowCost K d * oddSieve d := by
    apply Finset.sum_le_sum
    intro d hd
    apply oddInnerTerm_low
    have := Finset.mem_range.mp hd
    omega
  have hhi : (∑ i ∈ range ((K + 1) - (K / 3 + 1)), oddInnerTerm K (K / 3 + 1 + i)) ≤
      ∑ i ∈ range ((K + 1) - (K / 3 + 1)),
        2 * K * ((K / 3 + 1 + i : ℕ) : ℝ) * oddSieve (K / 3 + 1 + i) := by
    apply Finset.sum_le_sum
    intro i hi
    apply oddInnerTerm_high
    · have := Finset.mem_range.mp hi; omega
    · omega
  have hh := Finset.sum_range_add (fun d => 2 * (K : ℝ) * d * oddSieve d)
    (K / 3 + 1) ((K + 1) - (K / 3 + 1))
  rw [← hsplit] at hh
  have heq (M : ℕ) : (∑ d ∈ range M, 2 * (K : ℝ) * d * oddSieve d) =
      2 * K * (∑ d ∈ range M, oddSieve d * d) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [heq, heq] at hh
  linarith

/-- The full inner odd-order contribution is bounded by a rational cubic. -/
theorem oddInnerTerm_sum_le (K : ℕ) :
    (∑ d ∈ range (K + 1), oddInnerTerm K d) ≤
      1349 / 2916 * (K : ℝ) ^ 3 + 10000 * ((K : ℝ) + 1) ^ 2 := by
  have hs := oddInnerTerm_sum_sieve K
  rw [oddLowCost_sum] at hs
  let M := K / 3 + 1
  let N := K + 1
  have hm0 := mul_le_mul_of_nonneg_left (oddSieve_sum_bounds M).2
    (show (0 : ℝ) ≤ (K : ℝ) ^ 2 / 4 by positivity)
  have hm1 := mul_le_mul_of_nonneg_left (oddSieve_firstMoment_bounds M).1
    (show (0 : ℝ) ≤ K by positivity)
  have hm2 := mul_le_mul_of_nonneg_left (oddSieve_secondMoment_bounds M).2
    (show (0 : ℝ) ≤ 17 / 16 by norm_num)
  have hn1 := mul_le_mul_of_nonneg_left (oddSieve_firstMoment_bounds N).2
    (show (0 : ℝ) ≤ 2 * K by positivity)
  have hbound : (∑ d ∈ range (K + 1), oddInnerTerm K d) ≤
      (K : ℝ) ^ 2 / 4 * (4 / 9 * M + 4) -
      K * (2 / 9 * (M : ℝ) ^ 2 - 20 * (M + 1)) +
      17 / 16 * (4 / 27 * (M : ℝ) ^ 3 + 100 * (M + 1) ^ 2) +
      2 * K * (2 / 9 * (N : ℝ) ^ 2 + 20 * (N + 1)) := by
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

end QCatalan
