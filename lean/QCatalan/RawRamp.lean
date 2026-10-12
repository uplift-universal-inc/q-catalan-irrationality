import QCatalan.Defs
import QCatalan.RawTotientSieve
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # Finite weighted ramp estimates

These generic finite-sum lemmas convert first and second moment estimates for
any real weight into the cubic reciprocal-square bound, with an explicit
quadratic reciprocal-linear error. They do not assume an asymptotic theorem.
-/

open Finset

namespace QCatalan

/-- The positive-part ramp over natural indices. -/
noncomputable def weightedNatRamp (w : ℕ → ℝ) (K a : ℕ) : ℝ :=
  ∑ d ∈ range (K + 1), w d * d * ((K - a * d : ℕ) : ℝ)

theorem weighted_ramp_le (w : ℕ → ℝ) (A C₁ C₂ : ℝ) (N : ℕ) (K a : ℝ)
    (hK : 0 ≤ K) (ha : 0 ≤ a)
    (h₁ : (∑ d ∈ range N, w d * d) ≤ A * (N : ℝ) ^ 2 + C₁ * ((N : ℝ) + 1))
    (h₂ : 2 * A / 3 * (N : ℝ) ^ 3 - C₂ * ((N : ℝ) + 1) ^ 2 ≤
      ∑ d ∈ range N, w d * (d : ℝ) ^ 2) :
    (∑ d ∈ range N, w d * d * (K - a * d)) ≤
      A * K * (N : ℝ) ^ 2 - 2 * A / 3 * a * (N : ℝ) ^ 3 +
        C₁ * K * ((N : ℝ) + 1) + C₂ * a * ((N : ℝ) + 1) ^ 2 := by
  have hh₁ := mul_le_mul_of_nonneg_left h₁ hK
  have hh₂ := mul_le_mul_of_nonneg_left h₂ ha
  have hs : (∑ d ∈ range N, w d * d * (K - a * d)) =
      K * (∑ d ∈ range N, w d * d) - a * (∑ d ∈ range N, w d * (d : ℝ) ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [hs]
  nlinarith

/-- The exact cubic maximum, with divisions cleared. -/
theorem weighted_ramp_scaled_le (w : ℕ → ℝ) (A C₁ C₂ : ℝ) (N : ℕ) (K a : ℝ)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (ha : 0 ≤ a)
    (h₁ : (∑ d ∈ range N, w d * d) ≤ A * (N : ℝ) ^ 2 + C₁ * ((N : ℝ) + 1))
    (h₂ : 2 * A / 3 * (N : ℝ) ^ 3 - C₂ * ((N : ℝ) + 1) ^ 2 ≤
      ∑ d ∈ range N, w d * (d : ℝ) ^ 2) :
    a ^ 2 * (∑ d ∈ range N, w d * d * (K - a * d)) ≤
      A / 3 * K ^ 3 +
        a ^ 2 * (C₁ * K * ((N : ℝ) + 1) + C₂ * a * ((N : ℝ) + 1) ^ 2) := by
  have h := mul_le_mul_of_nonneg_left (weighted_ramp_le w A C₁ C₂ N K a hK ha h₁ h₂)
    (sq_nonneg a)
  have hfac : 0 ≤ A * (a * (N : ℝ) - K) ^ 2 * (2 * a * N + K) :=
    mul_nonneg (mul_nonneg hA (sq_nonneg _)) (by positivity)
  nlinarith

/-- Truncating a natural ramp at the quotient removes exactly its zero tail. -/
theorem weightedNatRamp_eq (w : ℕ → ℝ) (K a : ℕ) (ha : 1 ≤ a) :
    weightedNatRamp w K a =
      ∑ d ∈ range (K / a + 1), w d * d * ((K : ℝ) - a * d) := by
  have hsub : range (K / a + 1) ⊆ range (K + 1) :=
    range_mono (by have := Nat.div_le_self K a; omega)
  unfold weightedNatRamp
  rw [← Finset.sum_subset hsub (fun d hd hnot => ?_)]
  · apply sum_congr rfl
    intro d hd
    have hd' : a * d ≤ K := by
      have hda : d ≤ K / a := by simpa using mem_range.mp hd
      have hh := (Nat.le_div_iff_mul_le (by omega : 0 < a)).mp hda
      simpa only [Nat.mul_comm] using hh
    rw [Nat.cast_sub hd', Nat.cast_mul]
  · have hda : K / a < d := by simpa using hnot
    have hdK : K < a * d := by
      have hh := (Nat.div_lt_iff_lt_mul (by omega : 0 < a)).mp hda
      simpa only [Nat.mul_comm] using hh
    simp [Nat.sub_eq_zero_of_le hdK.le]

/-- Uniform quotient-cutoff bound; its error is quadratic in `K` and harmonic in `a`. -/
theorem weightedNatRamp_le (w : ℕ → ℝ) (A C₁ C₂ : ℝ)
    (hA : 0 ≤ A) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (h₁ : ∀ N : ℕ, (∑ d ∈ range N, w d * d) ≤
      A * (N : ℝ) ^ 2 + C₁ * ((N : ℝ) + 1))
    (h₂ : ∀ N : ℕ, 2 * A / 3 * (N : ℝ) ^ 3 - C₂ * ((N : ℝ) + 1) ^ 2 ≤
      ∑ d ∈ range N, w d * (d : ℝ) ^ 2)
    (K a : ℕ) (ha : 1 ≤ a) (haK : a ≤ K) :
    weightedNatRamp w K a ≤ A / 3 * (K : ℝ) ^ 3 / (a : ℝ) ^ 2 +
      (3 * C₁ + 9 * C₂) * (K : ℝ) ^ 2 / a := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hKa : (a : ℝ) ≤ K := by exact_mod_cast haK
  let N : ℕ := K / a + 1
  have hfloor : (a : ℝ) * ((N : ℝ) + 1) ≤ 3 * K := by
    have h := Nat.mul_div_le K a
    have h' : (a : ℝ) * (K / a : ℕ) ≤ K := by exact_mod_cast h
    dsimp [N]
    push_cast
    nlinarith
  have hs := weighted_ramp_scaled_le w A C₁ C₂ N K a hA (by positivity) ha0.le
    (h₁ N) (h₂ N)
  have hfirst : (a : ℝ) ^ 2 * (C₁ * K * ((N : ℝ) + 1)) ≤
      3 * C₁ * a * (K : ℝ) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hfloor
      (show 0 ≤ C₁ * (a : ℝ) * K by positivity)
    nlinarith
  have hsecond : (a : ℝ) ^ 2 * (C₂ * a * ((N : ℝ) + 1) ^ 2) ≤
      9 * C₂ * a * (K : ℝ) ^ 2 := by
    have hsq := sq_le_sq₀ (by positivity : 0 ≤ (a : ℝ) * ((N : ℝ) + 1))
      (by positivity : 0 ≤ 3 * (K : ℝ))
    have h := mul_le_mul_of_nonneg_left (hsq.mpr hfloor)
      (show 0 ≤ C₂ * (a : ℝ) by positivity)
    nlinarith
  rw [weightedNatRamp_eq w K a ha]
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos ha0)).mp
  calc (a : ℝ) ^ 2 * (∑ d ∈ range (K / a + 1), w d * d * ((K : ℝ) - a * d))
      ≤ A / 3 * (K : ℝ) ^ 3 + (3 * C₁ + 9 * C₂) * a * (K : ℝ) ^ 2 := by
        dsimp [N] at hs hfirst hsecond
        nlinarith
    _ = (a : ℝ) ^ 2 * (A / 3 * (K : ℝ) ^ 3 / (a : ℝ) ^ 2 +
        (3 * C₁ + 9 * C₂) * (K : ℝ) ^ 2 / a) := by
      field_simp

/-- Any finite subset of the positive indices has the usual harmonic upper bound. -/
theorem sum_reciprocal_subset_le (s : Finset ℕ) (K : ℕ) (hs : s ⊆ Icc 1 K) :
    (∑ a ∈ s, (1 : ℝ) / a) ≤ 1 + Real.log K := by
  have hsub : (∑ a ∈ s, (1 : ℝ) / a) ≤ ∑ a ∈ Icc 1 K, (1 : ℝ) / a := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hs
    intro a ha hnot
    positivity
  apply hsub.trans
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
    using harmonic_le_one_add_log K

/-- A finite family of ramps, with its reciprocal-square coefficient kept explicit. -/
theorem weightedNatRamp_sum_le (w : ℕ → ℝ) (A C₁ C₂ : ℝ)
    (hA : 0 ≤ A) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (h₁ : ∀ N : ℕ, (∑ d ∈ range N, w d * d) ≤
      A * (N : ℝ) ^ 2 + C₁ * ((N : ℝ) + 1))
    (h₂ : ∀ N : ℕ, 2 * A / 3 * (N : ℝ) ^ 3 - C₂ * ((N : ℝ) + 1) ^ 2 ≤
      ∑ d ∈ range N, w d * (d : ℝ) ^ 2)
    (K : ℕ) (s : Finset ℕ) (hs : s ⊆ Icc 1 K) (R : ℝ)
    (hR : (∑ a ∈ s, (1 : ℝ) / (a : ℝ) ^ 2) ≤ R) :
    (∑ a ∈ s, weightedNatRamp w K a) ≤ A / 3 * (K : ℝ) ^ 3 * R +
      (3 * C₁ + 9 * C₂) * (K : ℝ) ^ 2 * (1 + Real.log K) := by
  have hpoint : (∑ a ∈ s, weightedNatRamp w K a) ≤
      ∑ a ∈ s, (A / 3 * (K : ℝ) ^ 3 / (a : ℝ) ^ 2 +
        (3 * C₁ + 9 * C₂) * (K : ℝ) ^ 2 / a) := by
    apply Finset.sum_le_sum
    intro a ha
    obtain ⟨ha1, haK⟩ := Finset.mem_Icc.mp (hs ha)
    exact weightedNatRamp_le w A C₁ C₂ hA hC₁ hC₂ h₁ h₂ K a ha1 haK
  have he : (∑ a ∈ s, (A / 3 * (K : ℝ) ^ 3 / (a : ℝ) ^ 2 +
        (3 * C₁ + 9 * C₂) * (K : ℝ) ^ 2 / a)) =
      A / 3 * (K : ℝ) ^ 3 * (∑ a ∈ s, (1 : ℝ) / (a : ℝ) ^ 2) +
        (3 * C₁ + 9 * C₂) * (K : ℝ) ^ 2 * (∑ a ∈ s, (1 : ℝ) / a) := by
    simp only [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro a ha
    ring
  rw [he] at hpoint
  exact hpoint.trans (add_le_add
    (mul_le_mul_of_nonneg_left hR (by positivity))
    (mul_le_mul_of_nonneg_left (sum_reciprocal_subset_le s K hs) (by positivity)))

theorem weightedNatRamp_eq_zero_of_lt (w : ℕ → ℝ) {K a : ℕ} (ha : K < a) :
    weightedNatRamp w K a = 0 := by
  unfold weightedNatRamp
  apply sum_eq_zero
  intro d hd
  by_cases hd0 : d = 0
  · simp [hd0]
  · have hda : a ≤ a * d := Nat.le_mul_of_pos_right a (Nat.pos_of_ne_zero hd0)
    simp [Nat.sub_eq_zero_of_le (ha.le.trans hda)]

/-- The same bound holds with no upper restriction on `a`, since the extra ramps vanish. -/
theorem weightedNatRamp_le_all (w : ℕ → ℝ) (A C₁ C₂ : ℝ)
    (hA : 0 ≤ A) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (h₁ : ∀ N : ℕ, (∑ d ∈ range N, w d * d) ≤
      A * (N : ℝ) ^ 2 + C₁ * ((N : ℝ) + 1))
    (h₂ : ∀ N : ℕ, 2 * A / 3 * (N : ℝ) ^ 3 - C₂ * ((N : ℝ) + 1) ^ 2 ≤
      ∑ d ∈ range N, w d * (d : ℝ) ^ 2)
    (K a : ℕ) (ha : 1 ≤ a) :
    weightedNatRamp w K a ≤ A / 3 * (K : ℝ) ^ 3 / (a : ℝ) ^ 2 +
      (3 * C₁ + 9 * C₂) * (K : ℝ) ^ 2 / a := by
  by_cases haK : a ≤ K
  · exact weightedNatRamp_le w A C₁ C₂ hA hC₁ hC₂ h₁ h₂ K a ha haK
  · rw [weightedNatRamp_eq_zero_of_lt w (by omega : K < a)]
    positivity

/-- Doubling the step divides the cubic cost by four. -/
theorem weightedNatRamp_double_le (w : ℕ → ℝ) (A C₁ C₂ : ℝ)
    (hA : 0 ≤ A) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (h₁ : ∀ N : ℕ, (∑ d ∈ range N, w d * d) ≤
      A * (N : ℝ) ^ 2 + C₁ * ((N : ℝ) + 1))
    (h₂ : ∀ N : ℕ, 2 * A / 3 * (N : ℝ) ^ 3 - C₂ * ((N : ℝ) + 1) ^ 2 ≤
      ∑ d ∈ range N, w d * (d : ℝ) ^ 2)
    (K a : ℕ) (ha : 1 ≤ a) :
    weightedNatRamp w K (2 * a) ≤ A / 12 * (K : ℝ) ^ 3 / (a : ℝ) ^ 2 +
      (3 * C₁ + 9 * C₂) * (K : ℝ) ^ 2 / a := by
  have h := weightedNatRamp_le_all w A C₁ C₂ hA hC₁ hC₂ h₁ h₂ K (2 * a) (by omega)
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have he : A / 3 * (K : ℝ) ^ 3 / ((2 * a : ℕ) : ℝ) ^ 2 +
      (3 * C₁ + 9 * C₂) * (K : ℝ) ^ 2 / ((2 * a : ℕ) : ℝ) =
      A / 12 * (K : ℝ) ^ 3 / (a : ℝ) ^ 2 +
      (3 * C₁ + 9 * C₂) * (K : ℝ) ^ 2 / a / 2 := by
    push_cast
    ring
  rw [he] at h
  have hn : 0 ≤ (3 * C₁ + 9 * C₂) * (K : ℝ) ^ 2 / a := by positivity
  linarith

/-- The double-step family with its reciprocal-square coefficient kept explicit. -/
theorem weightedNatRamp_double_sum_le (w : ℕ → ℝ) (A C₁ C₂ : ℝ)
    (hA : 0 ≤ A) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (h₁ : ∀ N : ℕ, (∑ d ∈ range N, w d * d) ≤
      A * (N : ℝ) ^ 2 + C₁ * ((N : ℝ) + 1))
    (h₂ : ∀ N : ℕ, 2 * A / 3 * (N : ℝ) ^ 3 - C₂ * ((N : ℝ) + 1) ^ 2 ≤
      ∑ d ∈ range N, w d * (d : ℝ) ^ 2)
    (K : ℕ) (s : Finset ℕ) (hs : s ⊆ Icc 1 K) (R : ℝ)
    (hR : (∑ a ∈ s, (1 : ℝ) / (a : ℝ) ^ 2) ≤ R) :
    (∑ a ∈ s, weightedNatRamp w K (2 * a)) ≤ A / 12 * (K : ℝ) ^ 3 * R +
      (3 * C₁ + 9 * C₂) * (K : ℝ) ^ 2 * (1 + Real.log K) := by
  have hpoint : (∑ a ∈ s, weightedNatRamp w K (2 * a)) ≤
      ∑ a ∈ s, (A / 12 * (K : ℝ) ^ 3 / (a : ℝ) ^ 2 +
        (3 * C₁ + 9 * C₂) * (K : ℝ) ^ 2 / a) := by
    apply Finset.sum_le_sum
    intro a ha
    exact weightedNatRamp_double_le w A C₁ C₂ hA hC₁ hC₂ h₁ h₂ K a
      (Finset.mem_Icc.mp (hs ha)).1
  have he : (∑ a ∈ s, (A / 12 * (K : ℝ) ^ 3 / (a : ℝ) ^ 2 +
        (3 * C₁ + 9 * C₂) * (K : ℝ) ^ 2 / a)) =
      A / 12 * (K : ℝ) ^ 3 * (∑ a ∈ s, (1 : ℝ) / (a : ℝ) ^ 2) +
        (3 * C₁ + 9 * C₂) * (K : ℝ) ^ 2 * (∑ a ∈ s, (1 : ℝ) / a) := by
    simp only [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro a ha
    ring
  rw [he] at hpoint
  exact hpoint.trans (add_le_add
    (mul_le_mul_of_nonneg_left hR (by positivity))
    (mul_le_mul_of_nonneg_left (sum_reciprocal_subset_le s K hs) (by positivity)))

theorem oddRawRamp_sum_le (K : ℕ) (s : Finset ℕ) (hs : s ⊆ Icc 1 K)
    (R : ℝ) (hR : (∑ a ∈ s, (1 : ℝ) / (a : ℝ) ^ 2) ≤ R) :
    (∑ a ∈ s, weightedNatRamp oddRawSieve K a) ≤
      256 / 3675 * (K : ℝ) ^ 3 * R + 18030000 * (K : ℝ) ^ 2 * (1 + Real.log K) := by
  have h := weightedNatRamp_sum_le oddRawSieve (256 / 1225) 10000 2000000
    (by norm_num) (by norm_num) (by norm_num)
    (fun N => (oddRawSieve_firstMoment_bounds N).2)
    (fun N => by convert (oddRawSieve_secondMoment_bounds N).1 using 1 <;> norm_num)
    K s hs R hR
  norm_num at h ⊢
  exact h

theorem fourRawRamp_double_sum_le (K : ℕ) (s : Finset ℕ) (hs : s ⊆ Icc 1 K)
    (R : ℝ) (hR : (∑ a ∈ s, (1 : ℝ) / (a : ℝ) ^ 2) ≤ R) :
    (∑ a ∈ s, weightedNatRamp fourRawSieve K (2 * a)) ≤
      256 / 3675 * (K : ℝ) ^ 3 * R + 18030000 * (K : ℝ) ^ 2 * (1 + Real.log K) := by
  have h := weightedNatRamp_double_sum_le fourRawSieve (1024 / 1225) 10000 2000000
    (by norm_num) (by norm_num) (by norm_num)
    (fun N => (fourRawSieve_firstMoment_bounds N).2)
    (fun N => by convert (fourRawSieve_secondMoment_bounds N).1 using 1 <;> norm_num)
    K s hs R hR
  norm_num at h ⊢
  exact h

end QCatalan
