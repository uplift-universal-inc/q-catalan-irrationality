import QCatalan.Analytic
import QCatalan.Combinatorics

/-! Explicit cubic decay of the proved analytic envelope. -/

namespace QCatalan

/-- The completely explicit analytic envelope supplied by the determinant bound. -/
noncomputable def analyticEnvelope (p K : ℕ) : ℝ :=
  (K.factorial : ℝ) * (6 * (2 * (K : ℝ) - 1)) ^ K * ((p : ℝ)⁻¹) ^ bK K

theorem analyticEnvelope_pos {p K : ℕ} (hp : 2 ≤ p) (hK : 1 ≤ K) :
    0 < analyticEnvelope p K := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hfac : (0 : ℝ) < K.factorial := by exact_mod_cast K.factorial_pos
  have hscale : (0 : ℝ) < 6 * (2 * (K : ℝ) - 1) := by linarith
  exact mul_pos (mul_pos hfac (pow_pos hscale _)) (pow_pos (inv_base_pos hp) _)

/-- A uniform quadratic remainder in the actual logarithmic analytic estimate. -/
theorem log_analyticEnvelope_le {p K : ℕ} (hp : 2 ≤ p) (hK : 1 ≤ K) :
    Real.log (analyticEnvelope p K) ≤
      -(Real.log p / 3) * (K : ℝ) ^ 3 +
        (Real.log 12 + 2 + (3 / 2) * Real.log p) * (K : ℝ) ^ 2 := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have hlogK : Real.log (K : ℝ) ≤ K := by
    have := Real.log_le_sub_one_of_pos hKpos
    linarith
  have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
  have hlog12 : 0 ≤ Real.log (12 : ℝ) := Real.log_nonneg (by norm_num)
  have hfact : (0 : ℝ) < K.factorial := by exact_mod_cast K.factorial_pos
  have hscale : (0 : ℝ) < 6 * (2 * (K : ℝ) - 1) := by linarith
  have hfact_le : Real.log (K.factorial : ℝ) ≤ K * Real.log K := by
    have h1 : (K.factorial : ℝ) ≤ (K : ℝ) ^ K := by exact_mod_cast Nat.factorial_le_pow K
    calc _ ≤ Real.log ((K : ℝ) ^ K) := Real.log_le_log hfact h1
      _ = _ := Real.log_pow K K
  have hscale_le : Real.log (6 * (2 * (K : ℝ) - 1)) ≤ Real.log 12 + Real.log K := by
    calc _ ≤ Real.log (12 * (K : ℝ)) := Real.log_le_log hscale (by linarith)
      _ = _ := Real.log_mul (by norm_num) hKpos.ne'
  have hblog := mul_le_mul_of_nonneg_right (bK_cubic_bounds K).1 hlogp
  have hKsq : (K : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
  have hKlog : (K : ℝ) * Real.log K ≤ (K : ℝ) ^ 2 := by nlinarith
  have h12 := mul_le_mul_of_nonneg_left hKsq hlog12
  have hpconst := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ (K : ℝ) ^ 2 by nlinarith) hlogp
  have hscaleK := mul_le_mul_of_nonneg_left hscale_le hKpos.le
  have hlog : Real.log (analyticEnvelope p K) =
      Real.log (K.factorial : ℝ) + K * Real.log (6 * (2 * (K : ℝ) - 1)) -
        (bK K : ℝ) * Real.log p := by
    unfold analyticEnvelope
    rw [Real.log_mul (mul_pos hfact (pow_pos hscale _)).ne' (pow_pos (inv_base_pos hp) _).ne',
      Real.log_mul hfact.ne' (pow_pos hscale _).ne',
      Real.log_pow, Real.log_pow, Real.log_inv]
    ring
  rw [hlog]
  nlinarith [hfact_le, hscaleK, hKlog, h12, hpconst, hblog]


end QCatalan
