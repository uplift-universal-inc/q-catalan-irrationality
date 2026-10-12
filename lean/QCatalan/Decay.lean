import QCatalan.GramIdentity
import QCatalan.AnalyticAsymptotics

/-!
# The cubic determinant bound for the actual q-Catalan value

The weight and signed-functional bounds are proved in `QCatalan.Analytic`.
The determinant/functional identification is proved in `QCatalan.GramIdentity`.
This file gives the determinant-preserving basis change and assembles them.
-/

open Polynomial Finset Matrix

namespace QCatalan

theorem doubleRootPoly_expansion (q : ℝ) {K : ℕ} (i : Fin K) :
    doubleRootPoly q i.val =
      ∑ j : Fin K, (doubleRootChange q K i j) • (X : ℝ[X]) ^ j.val := by
  have h := (doubleRootPoly q i.val).as_sum_range_C_mul_X_pow'
    (show (doubleRootPoly q i.val).natDegree < K by rw [doubleRootPoly_natDegree]; exact i.isLt)
  rw [← Fin.sum_univ_eq_sum_range _ K] at h
  simpa only [doubleRootChange, Polynomial.smul_eq_C_mul] using h

/-- A monic triangular basis change preserves the real Gram determinant. -/
theorem doubleRootGram_eq_congruence {p : ℕ} (hp : 2 ≤ p) (K : ℕ) :
    doubleRootGram p K = doubleRootChange ((p : ℝ)⁻¹) K * gramR p K *
      (doubleRootChange ((p : ℝ)⁻¹) K).transpose := by
  let L := numeratorFunctional hp K
  have hmono (i j : Fin K) : L ((X : ℝ[X]) ^ (i.val + j.val)) = gramR p K i j := by
    simp only [L, numeratorFunctional, LinearMap.coe_mk, AddHom.coe_mk, gramR,
      Matrix.of_apply, Polynomial.eval_pow, Polynomial.eval_X]
  ext i j
  have hid : doubleRootGram p K i j =
      L (doubleRootPoly ((p : ℝ)⁻¹) i.val * doubleRootPoly ((p : ℝ)⁻¹) j.val) := by
    simp only [doubleRootGram, L, numeratorFunctional, LinearMap.coe_mk, AddHom.coe_mk,
      Polynomial.eval_mul]
  rw [hid, doubleRootPoly_expansion _ i, doubleRootPoly_expansion _ j]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    ← pow_add, map_sum, map_smul, smul_eq_mul, hmono]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  apply sum_congr rfl
  intro s hs
  apply sum_congr rfl
  intro r hr
  ring

theorem det_doubleRootGram {p : ℕ} (hp : 2 ≤ p) (K : ℕ) :
    (doubleRootGram p K).det = (gramR p K).det := by
  rw [doubleRootGram_eq_congruence hp]
  exact QZeta3.det_congruence_of_det_one _ _ (det_doubleRootChange _ _)

/-- Unconditional real-side estimate: the changed subcubic prefactor is a
conservative factorial bound; the cubic exponent is the manuscript's exact `bK`. -/
theorem DeltaR_decay {p : ℕ} (hp : 2 ≤ p) (K : ℕ) :
    |DeltaR p K (xi p)| ≤
      (K.factorial : ℝ) * (6 * (2 * (K : ℝ) - 1)) ^ K * ((p : ℝ)⁻¹) ^ bK K := by
  rw [← gram_det_eq hp K, ← det_doubleRootGram hp K]
  exact doubleRootGram_det_bound hp K

/-- The paper's cubic real-side decay, with all constants explicit and no
logarithm-of-zero convention needed. -/
theorem DeltaR_cubic_decay {p K : ℕ} (hp : 2 ≤ p) (hK : 1 ≤ K) :
    |DeltaR p K (xi p)| ≤ Real.exp
      (-(Real.log p / 3) * (K : ℝ) ^ 3 +
        (Real.log 12 + 2 + (3 / 2) * Real.log p) * (K : ℝ) ^ 2) := by
  calc _ ≤ analyticEnvelope p K := DeltaR_decay hp K
    _ = Real.exp (Real.log (analyticEnvelope p K)) := (Real.exp_log (analyticEnvelope_pos hp hK)).symm
    _ ≤ _ := Real.exp_le_exp.mpr (log_analyticEnvelope_le hp hK)

end QCatalan
