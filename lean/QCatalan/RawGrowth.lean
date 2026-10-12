import QCatalan.Growth
import QCatalan.RawDefs
import QCatalan.OddReciprocals
import QCatalan.RawOddGrowth
import QCatalan.RawClusterGrowth

/-! # Finite growth estimates for the conservative cyclotomic clearer -/

open Polynomial Finset Real

namespace QCatalan

private theorem sum_Icc_succ₁ (n : ℕ) (f : ℕ → ℝ) :
    (∑ d ∈ Icc 1 (n + 1), f d) = (∑ d ∈ Icc 1 n, f d) + f (n + 1) :=
  Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1) f

/-- Exact partition into odd, twice-odd, and fourfold cyclotomic orders. -/
theorem sum_Icc_four_classes_aux (K : ℕ) (f : ℕ → ℝ) :
    (∑ d ∈ Icc 1 (4 * K), f d) =
      (∑ d ∈ Icc 1 (4 * K), if d % 2 = 1 then f d else 0) +
      (∑ h ∈ Icc 1 (2 * K), if h % 2 = 1 then f (2 * h) else 0) +
      (∑ u ∈ Icc 1 K, f (4 * u)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have h4 : 4 * (K + 1) = 4 * K + 1 + 1 + 1 + 1 := by omega
    have h2 : 2 * (K + 1) = 2 * K + 1 + 1 := by omega
    simp only [h4, h2, sum_Icc_succ₁]
    norm_num [Nat.add_mod, Nat.mul_mod]
    rw [ih]
    have h₂ : 2 * (2 * K + 1) = 4 * K + 1 + 1 := by omega
    have h₄ : 4 * (K + 1) = 4 * K + 1 + 1 + 1 + 1 := by omega
    simp only [h₂]
    ring

theorem rawE_odd (K d : ℕ) (hd : d % 2 = 1) : rawE K d = E K d := by
  simp [rawE, E, hd]

theorem rawE_two_odd (K h : ℕ) (hh : h % 2 = 1) :
    rawE K (2 * h) = rawClusterCost K h := by
  have hh0 : h ≠ 0 := by omega
  have hmod : 2 * h % 4 = 2 := by omega
  simp [rawE, hh0, hmod]

theorem rawE_four (K u : ℕ) (hu : 0 < u) :
    rawE K (4 * u) = rawClusterCost K (2 * u) + (K - u - 1) := by
  have hu0 : u ≠ 0 := by omega
  simp [rawE, hu0, Nat.mul_mod]

theorem totient_two_odd (h : ℕ) (hh : h % 2 = 1) : Nat.totient (2 * h) = Nat.totient h := by
  have hcop : Nat.Coprime 2 h := by
    rw [Nat.coprime_two_left]
    exact Nat.odd_iff.mpr hh
  rw [Nat.totient_mul hcop]
  norm_num

/-- Class decomposition before applying any estimate. -/
theorem rawE_totient_split (K : ℕ) :
    (∑ d ∈ Icc 1 (4 * K), (rawE K d : ℝ) * Nat.totient d) =
      (∑ d ∈ Icc 1 (4 * K), oddInnerTerm K d) +
      (∑ h ∈ Icc 1 (2 * K), if h % 2 = 1 then
        (rawClusterCost K h : ℝ) * Nat.totient h else 0) +
      (∑ u ∈ Icc 1 K, ((rawClusterCost K (2 * u) : ℝ) + (K - u - 1 : ℕ)) *
        Nat.totient (4 * u)) := by
  rw [sum_Icc_four_classes_aux]
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro d hd
      by_cases ho : d % 2 = 1 <;> simp [oddInnerTerm, ho, rawE_odd K d]
    · apply Finset.sum_congr rfl
      intro h hh
      by_cases ho : h % 2 = 1 <;>
        simp [ho, rawE_two_odd K h, totient_two_odd h]
  · apply Finset.sum_congr rfl
    intro u hu
    rw [rawE_four K u (Finset.mem_Icc.mp hu).1, Nat.cast_add]

theorem oddInnerTerm_eq_zero_outer (K d : ℕ) (hd : 2 * K < d) :
    oddInnerTerm K d = 0 := by
  have hd0 : d ≠ 0 := by omega
  have hdK : ¬ d ≤ K := by omega
  have hdK2 : ¬ d ≤ 2 * K := by omega
  by_cases ho : d % 2 = 1 <;> simp [oddInnerTerm, ho, E, hd0, hdK, hdK2]

theorem oddInnerTerm_sum_restrict (K : ℕ) :
    (∑ d ∈ Icc 1 (4 * K), oddInnerTerm K d) =
      ∑ d ∈ Icc 1 (2 * K), oddInnerTerm K d := by
  symm
  apply Finset.sum_subset
  · intro d hd
    simp only [Finset.mem_Icc] at *
    omega
  · intro d hd hdnot
    have hgt : 2 * K < d := by
      simp only [Finset.mem_Icc] at *
      omega
    exact oddInnerTerm_eq_zero_outer K d hgt

theorem rawClusterCost_eq_zero (K h : ℕ) (hh : K ≤ h) : rawClusterCost K h = 0 := by
  unfold rawClusterCost
  apply Finset.sum_eq_zero
  intro a ha
  have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
  by_cases ho : a % 2 = 1
  · simp only [ho, ite_true]
    apply Nat.sub_eq_zero_of_le
    nlinarith
  · simp [ho]

theorem rawClusterCost_odd_sum_restrict (K : ℕ) :
    (∑ h ∈ Icc 1 (2 * K), if h % 2 = 1 then
      (rawClusterCost K h : ℝ) * Nat.totient h else 0) =
    (∑ h ∈ Icc 1 K, if h % 2 = 1 then
      (rawClusterCost K h : ℝ) * Nat.totient h else 0) := by
  symm
  apply Finset.sum_subset
  · intro h hh
    simp only [Finset.mem_Icc] at *
    omega
  · intro h hh hhnot
    have hle : K ≤ h := by
      simp only [Finset.mem_Icc] at *
      omega
    simp [rawClusterCost_eq_zero K h hle]

/-- A denominator-free bound sufficient for the lower-order exponent count. -/
theorem rawClusterCost_mul_le (K h : ℕ) (hh : 0 < h) :
    rawClusterCost K h * h ≤ K ^ 2 := by
  have hrange : (∑ a ∈ Icc 1 K, if a % 2 = 1 then K - a * h else 0) =
      ∑ a ∈ Icc 1 (K / h), if a % 2 = 1 then K - a * h else 0 := by
    symm
    apply Finset.sum_subset
    · intro a ha
      simp only [Finset.mem_Icc] at *
      have : K / h ≤ K := Nat.div_le_self _ _
      omega
    · intro a ha hanot
      have hag : K / h < a := by
        simp only [Finset.mem_Icc] at *
        omega
      have hmul : K < a * h := (Nat.div_lt_iff_lt_mul hh).mp hag
      simp [Nat.sub_eq_zero_of_le hmul.le]
  have hbound : rawClusterCost K h ≤ (K / h) * K := by
    unfold rawClusterCost
    rw [hrange]
    calc
      _ ≤ ∑ a ∈ Icc 1 (K / h), K := by
        apply Finset.sum_le_sum
        intro a ha
        split_ifs <;> omega
      _ = (K / h) * K := by simp
  have hquot := Nat.div_mul_le_self K h
  nlinarith

/-- All congruence classes admit a harmonic exponent bound. -/
theorem rawE_mul_order_le (K d : ℕ) (hd : 0 < d) :
    (rawE K d : ℝ) * d ≤ 2 * (K : ℝ) ^ 2 + 3 * K * d := by
  by_cases ho : d % 2 = 1
  · rw [rawE_odd K d ho]
    by_cases hdK : d ≤ K
    · have hh := E_odd_inner_weight_bound K d hd ho hdK
      have hbound : (d : ℝ) ≤ K := by exact_mod_cast hdK
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ d by positivity)
        (sub_nonneg.mpr hbound)]
    · have hE : E K d ≤ 2 * K := by
        simp only [E, Nat.ne_of_gt hd, ite_false, ho, ite_true, hdK]
        split_ifs <;> omega
      have hEr : (E K d : ℝ) ≤ 2 * K := by exact_mod_cast hE
      have h := mul_le_mul_of_nonneg_right hEr (show (0 : ℝ) ≤ d by positivity)
      nlinarith
  · by_cases h2 : d % 4 = 2
    · have hhalf : 0 < d / 2 := by omega
      have hd2 : d = 2 * (d / 2) := by omega
      have hhalfodd : (d / 2) % 2 = 1 := by omega
      have hh := rawClusterCost_mul_le K (d / 2) hhalf
      have hhr : (rawClusterCost K (d / 2) : ℝ) * (d / 2 : ℕ) ≤ (K : ℝ) ^ 2 := by
        exact_mod_cast hh
      rw [hd2, rawE_two_odd K (d / 2) hhalfodd]
      push_cast
      nlinarith
    · have hquarter : 0 < d / 4 := by omega
      have hd4 : d = 4 * (d / 4) := by omega
      have hh := rawClusterCost_mul_le K (2 * (d / 4)) (by omega)
      have hhr : (rawClusterCost K (2 * (d / 4)) : ℝ) * (2 * (d / 4 : ℕ)) ≤
          (K : ℝ) ^ 2 := by exact_mod_cast hh
      have htail : ((K - d / 4 - 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast (show K - d / 4 - 1 ≤ K by omega)
      have htail' := mul_le_mul_of_nonneg_right htail (show (0 : ℝ) ≤ (d / 4 : ℕ) by positivity)
      rw [hd4, rawE_four K (d / 4) hquarter]
      push_cast
      nlinarith

theorem rawE_le_harmonic (K d : ℕ) (hd : 0 < d) :
    (rawE K d : ℝ) ≤ 2 * (K : ℝ) ^ 2 / d + 3 * K := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h := rawE_mul_order_le K d hd
  have hh := (le_div_iff₀ hd0).mpr h
  convert hh using 1 <;> field_simp

/-- The unweighted exponent sum has only quadratic-logarithmic growth. -/
theorem sum_rawE_le (K : ℕ) :
    (∑ d ∈ Icc 1 (4 * K), (rawE K d : ℝ)) ≤
      20 * (K : ℝ) ^ 2 * (1 + Real.log K) := by
  by_cases hK : K = 0
  · subst K; simp
  have hK1 : 1 ≤ K := by omega
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK1)
  have hlog4 : Real.log (4 : ℝ) ≤ 3 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4) using 1 <;> norm_num
  have hsum := sum_inv_le_one_add_log (4 * K) (by omega)
  have hlogeq : Real.log (4 * (K : ℝ)) = Real.log 4 + Real.log K :=
    Real.log_mul (by norm_num) (ne_of_gt hK0)
  have hsum' : (∑ d ∈ Icc 1 (4 * K), (1 : ℝ) / d) ≤ 4 + Real.log K := by
    push_cast at hsum
    rw [hlogeq] at hsum
    linarith
  have hs : (∑ d ∈ Icc 1 (4 * K), (rawE K d : ℝ)) ≤
      2 * (K : ℝ) ^ 2 * (∑ d ∈ Icc 1 (4 * K), (1 : ℝ) / d) + 12 * K ^ 2 := by
    calc
      _ ≤ ∑ d ∈ Icc 1 (4 * K), (2 * (K : ℝ) ^ 2 / d + 3 * K) := by
        apply Finset.sum_le_sum
        intro d hd
        exact rawE_le_harmonic K d (Finset.mem_Icc.mp hd).1
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
        norm_num
        congr 1
        ring
  have hs' := mul_le_mul_of_nonneg_left hsum' (show (0 : ℝ) ≤ 2 * (K : ℝ) ^ 2 by positivity)
  nlinarith [mul_nonneg (sq_nonneg (K : ℝ)) hlogK]

/-- Complete finite weighted cost bound for the actual raw exponents. -/
theorem sum_rawE_totient_le (K : ℕ) (hK : 1 ≤ K) :
    (∑ d ∈ Icc 1 (4 * K), (rawE K d : ℝ) * Nat.totient d) ≤
      (rawCost : ℝ) * (K : ℝ) ^ 3 +
        9000000000 * (K : ℝ) ^ 2 * (1 + Real.log K) := by
  rw [rawE_totient_split, oddInnerTerm_sum_restrict, rawClusterCost_odd_sum_restrict]
  have hs₁ := oddInnerTerm_sum_le_raw_full K
  have hs₂ := rawClusterCost_odd_totient_sum_le K
  have hs₃ := rawClusterCost_four_totient_sum_le K
  have hs₄ := rawPolynomialTail_totient_sum_le K
  simp_rw [add_mul, Finset.sum_add_distrib]
  have hcoeff : (70816 / 99225 : ℝ) + 2 * (256 / 3675 * (89 / 72)) +
      1024 / 3675 = (rawCost : ℝ) := by norm_num [rawCost]
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hlog : 0 ≤ Real.log K := Real.log_nonneg hK1
  have hpos := mul_nonneg (sq_nonneg (K : ℝ)) hlog
  norm_num [rawCost] at hcoeff ⊢
  nlinarith [sq_nonneg ((K : ℝ) - 1)]

theorem log_rawCK_eq (p K : ℕ) (hp : 2 ≤ p) :
    Real.log (rawCK p K : ℝ) =
      ∑ d ∈ Icc 1 (4 * K), (rawE K d : ℝ) * Real.log (Phi p d : ℝ) := by
  unfold rawCK
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

theorem log_rawCK_le_weighted_totient (p K : ℕ) (hp : 2 ≤ p) :
    Real.log (rawCK p K : ℝ) ≤
      Real.log p * (∑ d ∈ Icc 1 (4 * K), (rawE K d : ℝ) * Nat.totient d) +
      2 * (∑ d ∈ Icc 1 (4 * K), (rawE K d : ℝ)) := by
  rw [log_rawCK_eq p K hp]
  calc
    _ ≤ (∑ d ∈ Icc 1 (4 * K), (rawE K d : ℝ) *
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

/-- A proved cubic cyclotomic growth bound below the analytic-content budget. -/
theorem log_rawCK_le {p : ℕ} (hp : 2 ≤ p) :
    ∃ c : ℝ, ∀ K : ℕ, 2 ≤ K →
      Real.log (rawCK p K : ℝ) ≤
        (rawCost : ℝ) * (K : ℝ) ^ 3 * Real.log p +
          c * (K : ℝ) ^ 2 * Real.log K := by
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(9000000000 * Real.log p + 40) * (1 + 1 / Real.log 2), fun K hK => ?_⟩
  have hcost := sum_rawE_totient_le K (by omega)
  have he := sum_rawE_le K
  have hlog := log_rawCK_le_weighted_totient p K hp
  have hweighted := mul_le_mul_of_nonneg_left hcost hlp.le
  have hb : Real.log (rawCK p K : ℝ) ≤
      (rawCost : ℝ) * (K : ℝ) ^ 3 * Real.log p +
        (9000000000 * Real.log p + 40) * (K : ℝ) ^ 2 * (1 + Real.log K) := by
    nlinarith
  have hlK : Real.log 2 ≤ Real.log K := Real.log_le_log (by norm_num) (by exact_mod_cast hK)
  have hdiv : 1 ≤ Real.log K / Real.log 2 := by
    rw [le_div_iff₀ hl2]
    simpa using hlK
  have hfactor : 1 + Real.log K ≤ (1 + 1 / Real.log 2) * Real.log K := by
    calc
      _ ≤ Real.log K / Real.log 2 + Real.log K := by
        simpa [add_comm] using add_le_add_right hdiv (Real.log K)
      _ = _ := by ring
  have hh := mul_le_mul_of_nonneg_left hfactor
    (show (0 : ℝ) ≤ (9000000000 * Real.log p + 40) * (K : ℝ) ^ 2 by positivity)
  nlinarith

end QCatalan
