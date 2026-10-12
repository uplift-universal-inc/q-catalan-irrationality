import QCatalan.Decay
import QCatalan.Budget
import QCatalan.RawDefs

/-!
# Decay after the conservative cyclotomic normalization

The cost parameter is explicit in these general implications.  The concrete
finite-sieve growth theorem supplies its strict `α < 7/6` hypothesis separately.
-/

open Polynomial Finset Filter Topology
namespace QCatalan

theorem rawCK_pos {p : ℕ} (hp : 2 ≤ p) (K : ℕ) : 0 < rawCK p K := by
  unfold rawCK
  apply prod_pos
  intro d hd
  exact pow_pos (QZeta3.Phi_pos hp d) _

/-- The explicit upper bound for the normalized determinant value. -/
noncomputable def rawEps (p K : ℕ) : ℝ :=
  (rawCK p K : ℝ) * analyticEnvelope p K / (p : ℝ) ^ cK K

theorem rawEps_pos {p K : ℕ} (hp : 2 ≤ p) (hK : 1 ≤ K) : 0 < rawEps p K := by
  have hc : (0 : ℝ) < rawCK p K := by exact_mod_cast rawCK_pos hp K
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  exact div_pos (mul_pos hc (analyticEnvelope_pos hp hK)) (pow_pos hp0 _)

/-- Arithmetic content, analytic decay, and denominator growth combined. -/
theorem log_pow_mul_rawEps_le_of_cost {p : ℕ} (hp : 2 ≤ p) {α c : ℝ}
    (hC : ∀ K : ℕ, 2 ≤ K → Real.log (rawCK p K : ℝ) ≤
      α * (K : ℝ) ^ 3 * Real.log p + c * (K : ℝ) ^ 2 * Real.log K)
    (b : ℕ) (hb : 0 < b) (K : ℕ) (hK : 2 ≤ K) :
    Real.log ((b : ℝ)^K * rawEps p K) ≤
      -((7/6-α)*Real.log p)*(K : ℝ)^3 + c*(K : ℝ)^2*Real.log K +
        (Real.log b + Real.log 12 + 2 + (5/2)*Real.log p)*(K : ℝ)^2 := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
  have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
  have hlogb : 0 ≤ Real.log (b : ℝ) := Real.log_natCast_nonneg b
  have hCK : (0 : ℝ) < rawCK p K := by exact_mod_cast rawCK_pos hp K
  have henv := analyticEnvelope_pos hp (show 1 ≤ K by omega)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have heps := rawEps_pos hp (show 1 ≤ K by omega)
  have hlog : Real.log ((b : ℝ)^K * rawEps p K) =
      K*Real.log b + Real.log (rawCK p K : ℝ) + Real.log (analyticEnvelope p K) -
        (cK K : ℝ)*Real.log p := by
    rw [Real.log_mul (pow_pos hb0 _).ne' heps.ne']
    unfold rawEps
    rw [Real.log_div (mul_pos hCK henv).ne' (pow_pos hp0 _).ne',
      Real.log_mul hCK.ne' henv.ne', Real.log_pow, Real.log_pow]
    ring
  have hc := mul_le_mul_of_nonneg_right (cK_cubic_bounds K).1 hlogp
  have ha := log_analyticEnvelope_le hp (show 1 ≤ K by omega)
  have hb1 : (K : ℝ)*Real.log b ≤ (K : ℝ)^2*Real.log b := by
    exact mul_le_mul_of_nonneg_right (by nlinarith) hlogb
  have hp1 : ((K : ℝ)+1)*Real.log p ≤ (K : ℝ)^2*Real.log p := by
    exact mul_le_mul_of_nonneg_right (by nlinarith) hlogp
  rw [hlog]
  nlinarith [hC K hK, hc, ha, hb1, hp1]

/-- Every fixed rational-denominator factor is dominated by the normalized
cubic decay, for any proved arithmetic cost strictly below `7/6`. -/
theorem tendsto_pow_mul_rawEps_of_cost {p : ℕ} (hp : 2 ≤ p) {α c : ℝ}
    (hα : α < 7/6)
    (hC : ∀ K : ℕ, 2 ≤ K → Real.log (rawCK p K : ℝ) ≤
      α*(K : ℝ)^3*Real.log p + c*(K : ℝ)^2*Real.log K)
    (b : ℕ) (hb : 0 < b) :
    Tendsto (fun K : ℕ => (b : ℝ)^K * rawEps p K) atTop (𝓝 0) := by
  let B : ℝ := Real.log 12 + 2 + (5/2)*Real.log p
  have hc : 0 < (7/6-α)*Real.log (p : ℝ) :=
    mul_pos (sub_pos.mpr hα) (Real.log_pos (by exact_mod_cast (show 1 < p by omega)))
  have ht := tendsto_pow_mul_cubicEnvelope hc c B b hb
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with K hK
    exact le_of_lt (mul_pos (pow_pos (by exact_mod_cast hb) _) (rawEps_pos hp hK))
  · filter_upwards [eventually_ge_atTop 2] with K hK
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [← Real.exp_log (rawEps_pos hp (by omega))]
    apply Real.exp_le_exp.mpr
    have h := log_pow_mul_rawEps_le_of_cost hp hC 1 (by norm_num) K hK
    simpa only [Nat.cast_one, one_pow, one_mul, Real.log_one, zero_add, B, cubicEnvelope] using h

/-- The declared normalized polynomial is bounded by the explicit envelope. -/
theorem rawPK_eval_bound {p : ℕ} (hp : 2 ≤ p) (K : ℕ) :
    |aeval (xi p) (rawPK p K)| ≤ rawEps p K := by
  have hCK : (0 : ℝ) < rawCK p K := by exact_mod_cast rawCK_pos hp K
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have he : aeval (xi p) (rawPK p K) =
      DeltaR p K (xi p) * ((rawCK p K : ℝ) / (p : ℝ)^cK K) := by
    simp [rawPK, DeltaR]
  rw [he, abs_mul, abs_of_pos (div_pos hCK (pow_pos hp0 _))]
  calc _ ≤ analyticEnvelope p K * ((rawCK p K : ℝ)/(p : ℝ)^cK K) :=
      mul_le_mul_of_nonneg_right (DeltaR_decay hp K) (div_pos hCK (pow_pos hp0 _)).le
    _ = rawEps p K := by unfold rawEps; ring

end QCatalan
