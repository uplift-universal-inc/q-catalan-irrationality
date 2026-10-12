import QCatalan.Defs
import QZeta3.Criterion

/-!
# The final numerical budget and irrationality criterion

These are proved, general analytic and arithmetic implications.  They do not
assert that the concrete q-Catalan determinants satisfy the required estimates.
-/

open Polynomial Filter Topology

namespace QCatalan

/-- The manuscript's claimed remaining cubic margin is strictly positive. -/
theorem margin_gt_rational : (41 / 1350 : ℝ) < margin := by
  have hpi : (9 : ℝ) < Real.pi ^ 2 := by nlinarith [Real.pi_gt_d2]
  have hden : (0 : ℝ) < 150 * Real.pi ^ 2 := by positivity
  have hquot : 1309 / (150 * Real.pi ^ 2) < (1309 / 1350 : ℝ) := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  unfold margin
  linarith

theorem margin_pos : 0 < margin := lt_trans (by norm_num) margin_gt_rational

theorem content_decay_minus_cost : (1 / 3 + 5 / 6 : ℝ) - cost = margin := by
  unfold cost margin
  ring

theorem cost_lt_budget : cost < (7 / 6 : ℝ) := by
  have := margin_pos
  rw [← content_decay_minus_cost] at this
  linarith

/-- The sufficient rational cost proposed for an elementary finite-sieve variant.
This identity alone does not prove a bound on the actual cyclotomic multiplier. -/
theorem rational_budget_identity : (7 / 6 - 1559 / 1350 : ℝ) = 8 / 675 := by
  norm_num

/-- A cubic decay envelope with the lower-order terms used in the paper. -/
noncomputable def cubicEnvelope (c A B : ℝ) (K : ℕ) : ℝ :=
  Real.exp (-c * (K : ℝ) ^ 3 + A * (K : ℝ) ^ 2 * Real.log K + B * (K : ℝ) ^ 2)

theorem cubicEnvelope_pos (c A B : ℝ) (K : ℕ) : 0 < cubicEnvelope c A B K :=
  Real.exp_pos _

/-- A positive cubic exponent beats every fixed rational-denominator cost. -/
theorem tendsto_pow_mul_cubicEnvelope {c : ℝ} (hc : 0 < c) (A B : ℝ)
    (b : ℕ) (hb : 0 < b) :
    Tendsto (fun K : ℕ => (b : ℝ) ^ K * cubicEnvelope c A B K) atTop (𝓝 0) := by
  let B' : ℝ := B + Real.log b
  have hf : Tendsto
      (fun K : ℕ => -c * (K : ℝ) ^ 3 + A * (K : ℝ) ^ 2 * Real.log K +
        B' * (K : ℝ) ^ 2) atTop atBot := by
    have h1 : Tendsto (fun K : ℕ => (K : ℝ) ^ 3) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun K : ℕ => Real.log (K : ℝ) / K) atTop (𝓝 0) := by
      simpa [Function.comp_def] using
        (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp tendsto_natCast_atTop_atTop
    have h3 : Tendsto (fun K : ℕ => B' / K) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat B'
    have h4 : Tendsto (fun K : ℕ => -c + A * (Real.log (K : ℝ) / K) + B' / K)
        atTop (𝓝 (-c)) := by
      simpa using ((h2.const_mul A).const_add (-c)).add h3
    refine (h1.atTop_mul_neg (neg_neg_of_pos hc) h4).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with K hK
    have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
    field_simp
  have hexp := Real.tendsto_exp_atBot.comp hf
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp ?_ ?_
  · filter_upwards [] with K
    exact le_of_lt (mul_pos (pow_pos (by exact_mod_cast hb) _) (cubicEnvelope_pos _ _ _ _))
  · filter_upwards [eventually_ge_atTop 1] with K hK
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    have hpow : (b : ℝ) ^ K = Real.exp ((K : ℝ) * Real.log b) := by
      rw [Real.exp_nat_mul, Real.exp_log hbR]
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have hKK : (K : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
    have hlogb : 0 ≤ Real.log (b : ℝ) := Real.log_natCast_nonneg b
    rw [hpow, cubicEnvelope, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [B']
    nlinarith [mul_le_mul_of_nonneg_right hKK hlogb]

/-- Complete irrationality criterion for an explicit family of integer-coefficient
polynomials.  Its hypotheses are intentionally visible: applying it to q-Catalan
still requires the arithmetic, analytic, and nonvanishing theorems of the paper. -/
theorem irrational_of_cubic_polynomial_approximations
    (ξ : ℝ) (P : ℕ → ℚ[X])
    (hdegree : ∀ K, (P K).natDegree ≤ K)
    (hinteger : ∀ K i, ((P K).coeff i).den = 1)
    (c A B : ℝ) (hc : 0 < c)
    (hbound : ∀ K, 1 ≤ K → |aeval ξ (P K)| ≤ cubicEnvelope c A B K)
    (hnonzero : ∀ N, ∃ K, N ≤ K ∧ aeval ξ (P K) ≠ 0) : Irrational ξ := by
  exact QZeta3.irrational_of_poly_approx ξ P hdegree hinteger
    (cubicEnvelope c A B) hbound (tendsto_pow_mul_cubicEnvelope hc A B) hnonzero

end QCatalan
