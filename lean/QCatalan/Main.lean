import Mathlib.Analysis.Complex.Polynomial.Basic
import QCatalan.Normalization
import QCatalan.RawCyclotomic
import QCatalan.DenominatorDescent
import QCatalan.RawGrowth
import QCatalan.Asymptotics
import QCatalan.Nonvanishing

/-!
# Irrationality of the q-Catalan Lambert series

This module discharges every approximation hypothesis for the explicit q-Catalan
series at all natural bases at least two, including composite bases. It uses the
conservative cyclotomic normalization `rawPK`, not the sharper denominator in the
original manuscript. Its strictly positive cubic margin is `421/198450`.
-/

open Polynomial Finset
namespace QCatalan
variable {p : ℕ}

/-- Every coefficient of the concrete normalized determinant is an integer. -/
theorem rawPK_coeff_den (hp : 2 ≤ p) (K i : ℕ) :
    ((rawPK p K).coeff i).den = 1 := by
  rw [rawPK, Polynomial.coeff_mul_C]
  apply normalized_coefficient_den hp K i (rawCK p K)
  apply Generic.denominators_clear_of_cyclotomic_bounds (𝕜 := ℂ) hp K i
  intro d hd ω hω
  exact Generic.raw_cyclotomic_coeff_bound hω (mem_Icc.mp hd).1 K i

/-- The normalization does not increase the polynomial degree. -/
theorem natDegree_rawPK_le (p K : ℕ) : (rawPK p K).natDegree ≤ K :=
  (Polynomial.natDegree_mul_C_le _ _).trans (natDegree_Delta_le p K)

theorem aeval_rawPK (p K : ℕ) (x : ℝ) :
    aeval x (rawPK p K) = DeltaR p K x * ((rawCK p K : ℝ)/(p : ℝ)^cK K) := by
  simp [rawPK, DeltaR]

/-- Infinitely many of the actual normalized polynomial values are nonzero. -/
theorem rawPK_frequently_ne_zero (hp : 2 ≤ p) (N : ℕ) :
    ∃ K, N ≤ K ∧ aeval (xi p) (rawPK p K) ≠ 0 := by
  obtain ⟨K, hK, hne⟩ := frequently_ne_zero hp N
  refine ⟨K, hK, ?_⟩
  rw [aeval_rawPK]
  have hc : (0 : ℝ) < rawCK p K := by exact_mod_cast rawCK_pos hp K
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  exact mul_ne_zero hne (div_ne_zero hc.ne' (pow_ne_zero _ hp0))

/-- The main theorem, with no arithmetic, analytic, or nonvanishing hypotheses
beyond the stated range of the integer base. -/
theorem irrational_xi (hp : 2 ≤ p) : Irrational (xi p) := by
  obtain ⟨c, hC⟩ := log_rawCK_le hp
  exact QZeta3.irrational_of_poly_approx (xi p) (rawPK p)
    (natDegree_rawPK_le p) (rawPK_coeff_den hp) (rawEps p)
    (fun K _ => rawPK_eval_bound hp K)
    (tendsto_pow_mul_rawEps_of_cost hp (by norm_num [rawCost]) hC)
    (rawPK_frequently_ne_zero hp)

/-- Explicit statement of q-Catalan irrationality in the paper's Lambert-series
normalization, indexed from one by the shift `n+1`. -/
theorem irrational_qCatalan (p : ℕ) (hp : 2 ≤ p) :
    Irrational (∑' n : ℕ,
      ((n+1 : ℕ) : ℝ) * (p : ℝ)^(n+1) /
        ((p : ℝ)^(2*(n+1)) + 1)) := by
  simpa only [xi, term] using irrational_xi hp

/-- The equivalent reciprocal-q expression, with q=1/p. -/
theorem irrational_qBeta_two (p : ℕ) (hp : 2 ≤ p) :
    Irrational (∑' n : ℕ,
      ((n+1 : ℕ) : ℝ) * ((p : ℝ)⁻¹)^(n+1) /
        (1 + ((p : ℝ)⁻¹)^(2*(n+1)))) := by
  rw [(hasSum_reciprocal hp).tsum_eq]
  exact irrational_xi hp

end QCatalan
