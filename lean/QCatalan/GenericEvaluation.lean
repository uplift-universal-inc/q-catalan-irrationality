import QCatalan.GenericSpecialization
import QZeta3.LocalEvaluation

open Polynomial Finset
open QZeta3.Generic

namespace QCatalan.Generic

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

theorem natCast_pow_ne_one {p n : ℕ} (hp : 2 ≤ p) (hn : 0 < n) :
    (p : 𝕜) ^ n ≠ 1 := by
  have hpn : 1 < p ^ n := Nat.one_lt_pow (by omega : n ≠ 0) (by omega : 1 < p)
  intro h
  have he : p ^ n = 1 := by exact_mod_cast h
  omega

theorem inv_plus_mem_regularAt (ω : 𝕜) (j : ℕ) (hj : 1 + ω ^ (2 * j) ≠ 0) :
    (1 + (RatFunc.X : RatFunc 𝕜) ^ (2 * j))⁻¹ ∈ regularAt ω := by
  have h := inv_polynomial_mem_regularAt ω (1 + X ^ (2 * j))
    (by simpa using hj)
  simpa using h

theorem localizationData_natCast {p : ℕ} (hp : 2 ≤ p) (K : ℕ) :
    LocalizationData (regularAt (p : 𝕜)) (RatFunc.X : RatFunc 𝕜) K := by
  refine ⟨⟨base_mem_regularAt _, inv_base_mem_regularAt _ ?_, ?_⟩, ?_⟩
  · exact_mod_cast (show p ≠ 0 by omega)
  · intro n hn
    exact inv_geometric_mem_regularAt _ n (natCast_pow_ne_one hp (mem_Icc.mp hn).1)
  · intro j hj
    apply inv_plus_mem_regularAt
    exact_mod_cast (show 1 + p ^ (2 * j) ≠ 0 by omega)

theorem Delta_coeff_mem_regularAt_natCast {p : ℕ} (hp : 2 ≤ p) (K i : ℕ) :
    (Delta (RatFunc.X : RatFunc 𝕜) K).coeff i ∈ regularAt (p : 𝕜) :=
  (localizationData_natCast hp K).Delta_coeff_mem i

/-- Generic specialization recovers exactly the actual rational determinant coefficients. -/
theorem eval_Delta_coeff_natCast {p : ℕ} (hp : 2 ≤ p) (K i : ℕ) :
    RatFunc.eval (RingHom.id 𝕜) (p : 𝕜) ((Delta (RatFunc.X : RatFunc 𝕜) K).coeff i) =
      ((QCatalan.Delta p K).coeff i : 𝕜) := by
  have he := Specialization.specialize_Delta_coeff
    (localizationData_natCast (𝕜 := 𝕜) hp K) (localEval (p : 𝕜)) i
  simp only [localEval_apply, RatFunc.eval_X] at he
  rw [he]
  have hm := congrArg (fun f : 𝕜[X] => f.coeff i)
    (Specialization.map_Delta (Rat.castHom 𝕜) (p : ℚ) K)
  simpa only [Polynomial.coeff_map, Rat.coe_castHom, Rat.cast_natCast, Delta_natCast] using hm.symm

/-- Outside zero and the finitely many relevant roots of unity, every generic
coefficient is regular. The plus denominators are included by squaring. -/
theorem Delta_coeff_regular_of_not_root (K i : ℕ) (ω : 𝕜) (hω : ω ≠ 0)
    (hgeom : ∀ n ∈ Icc 1 (4 * K), ω ^ n ≠ 1) :
    (Delta (RatFunc.X : RatFunc 𝕜) K).coeff i ∈ regularAt ω := by
  apply LocalizationData.Delta_coeff_mem (K := K)
  refine ⟨⟨base_mem_regularAt ω, inv_base_mem_regularAt ω hω,
    fun n hn => inv_geometric_mem_regularAt ω n (hgeom n hn)⟩, ?_⟩
  intro j hj
  apply inv_plus_mem_regularAt
  intro hplus
  have hj1 := (mem_Icc.mp hj).1
  have hjK := (mem_Icc.mp hj).2
  have hn : 4 * j ∈ Icc 1 (4 * K) := mem_Icc.mpr ⟨by omega, by omega⟩
  apply hgeom (4 * j) hn
  have he : ω ^ (2 * j) = -1 := by linear_combination hplus
  calc ω ^ (4 * j) = (ω ^ (2 * j)) ^ 2 := by rw [← pow_mul]; congr 1; omega
    _ = 1 := by rw [he]; ring

end QCatalan.Generic
