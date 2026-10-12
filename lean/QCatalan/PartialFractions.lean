import QCatalan.Polynomial
import QZeta3.DividedDifferences

open Polynomial Finset

namespace QCatalan

theorem F_eq_squared_base (p K : ℕ) : F p K = QZeta3.F (p ^ 2) K := by
  simp only [F, QZeta3.F, Nat.cast_pow, pow_mul]

theorem res_eq_squared_base (p K k a : ℕ) : res p K k a = QZeta3.res (p ^ 2) K k a := by
  simp only [res, QZeta3.res, F_eq_squared_base, Nat.cast_pow, pow_mul]

theorem nrm_eq_squared_base (p K : ℕ) : nrm p K = QZeta3.nrm (p ^ 2) K := by
  have hsum := QZeta3.sum_Icc_id_mul_two K
  have hAK : 2 * QZeta3.AK K = K * (K + 1) := by
    rw [← QZeta3.sum_Icc_id_eq_AK] at *
    omega
  simp only [nrm, QZeta3.nrm, Nat.cast_pow, ← pow_mul, hAK]

theorem partial_fraction_real {p : ℕ} (hp : 2 ≤ p) (K k : ℕ) (x : ℝ)
    (hx : ∀ a ∈ Icc 1 K, x ≠ (p : ℝ) ^ (2 * a)) :
    x ^ k / (F p K).eval₂ (Rat.castHom ℝ) x =
      (X ^ k /ₘ F p K).eval₂ (Rat.castHom ℝ) x +
      ∑ a ∈ Icc 1 K, (res p K k a : ℝ) / (x - (p : ℝ) ^ (2 * a)) := by
  have hp2 : 2 ≤ p ^ 2 := by nlinarith
  have h := QZeta3.partial_fraction_real hp2 K k x (by
    simpa only [Nat.cast_pow, ← pow_mul] using hx)
  simpa only [F_eq_squared_base, res_eq_squared_base, Nat.cast_pow, ← pow_mul] using h

theorem denominator_normalization {p : ℕ} (hp : 2 ≤ p) (K : ℕ) (x : ℝ) :
    (∏ a ∈ Icc 1 K, (1 - ((p : ℝ)⁻¹) ^ (2 * a) * x)) =
      (1 / (nrm p K : ℝ)) * (F p K).eval₂ (Rat.castHom ℝ) x := by
  have hp2 : 2 ≤ p ^ 2 := by nlinarith
  simpa only [nrm_eq_squared_base, F_eq_squared_base, Nat.cast_pow, ← inv_pow, ← pow_mul]
    using QZeta3.denominator_normalization hp2 K x

end QCatalan
