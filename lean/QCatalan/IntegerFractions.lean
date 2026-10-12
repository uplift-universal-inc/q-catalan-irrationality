import QCatalan.GenericSpecialization
import QZeta3.IntegerFractions

/-!
# Integral fractions before local cyclotomic cancellation

The q-Catalan moments use only integer polynomial numerators and monic
integer denominators. This supplies Gauss descent after local pole clearing.
-/

open Polynomial Finset
open QZeta3.Generic

namespace QCatalan.Generic

variable {𝕜 : Type*} [Field 𝕜]

/-- All q-Catalan finite denominators belong to the ring of fractions with
monic integer denominators, including the additional `1 + z^(2j)` factors. -/
theorem integerMonicFraction_localization (K : ℕ) :
    LocalizationData (integerMonicFractions (𝕜 := 𝕜)) RatFunc.X K where
  geom := QZeta3.Generic.integerMonicFraction_localization (4*K)
  inv_plus_mem j hj := by
    have hj0 : 2*j ≠ 0 := by have := (mem_Icc.mp hj).1; omega
    have hm : (X ^ (2*j) + 1 : ℤ[X]).Monic := by
      simpa only [C_1] using (Polynomial.monic_X_pow_add_C (a := (1 : ℤ)) hj0)
    have h := inverse_monic_mem (𝕜 := 𝕜) (X^(2*j)+1) hm
    simpa [intPolynomialMap, add_comm] using h

/-- Every coefficient of the actual generic determinant has a monic integer
denominator. No arbitrary rational constant denominators are introduced. -/
theorem Delta_coeff_integerMonicFraction (K i : ℕ) :
    (Delta (RatFunc.X : RatFunc 𝕜) K).coeff i ∈ integerMonicFractions :=
  (integerMonicFraction_localization (𝕜 := 𝕜) K).Delta_coeff_mem i

end QCatalan.Generic
