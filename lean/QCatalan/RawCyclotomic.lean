import QCatalan.CyclotomicAuxOdd
import QCatalan.RawEvenCyclotomic
import QCatalan.RawHighOddCyclotomic

/-! # Complete direct cyclotomic coefficient clearing

Every positive cyclotomic order is covered: low and high odd orders, orders twice
an odd number, and orders divisible by four. The fourth case uses direct cluster
weights and the polynomial-moment rank bound, so its proof has no formal tail
interpolation premise.
-/

namespace QCatalan.Generic
open QZeta3.Generic (uniformizer regularAt)
variable {k : Type*} [Field k] [CharZero k]

/-- All-order pole bound for every coefficient of the actual q-Catalan determinant. -/
theorem raw_cyclotomic_coeff_bound {ω : k} {d : ℕ}
    (hω : IsPrimitiveRoot ω d) (hd : 0 < d) (K i : ℕ) :
    uniformizer ω ^ rawE K d * (Delta (RatFunc.X : RatFunc k) K).coeff i ∈ regularAt ω := by
  have hω0 : ω ≠ 0 := (hω.isUnit (by omega)).ne_zero
  by_cases hodd : Odd d
  · by_cases hdK : d ≤ K
    · exact odd_low_Delta_coeff_mem hω hd hodd hω0 hdK i
    · exact odd_high_Delta_rawE_coeff_mem hω hd hodd hω0 (by omega) i
  · have heven : d % 2 = 0 := by
      have hn : ¬ d % 2 = 1 := fun h => hodd (Nat.odd_iff.mpr h)
      omega
    by_cases hf : d % 4 = 0
    · have he : d = 4 * (d / 4) := by omega
      have hu : 0 < d / 4 := by omega
      rw [he] at hω ⊢
      exact fourfold_Delta_rawE_coeff_mem hω hu K i
    · have he : d = 2 * (d / 2) := by omega
      have hh : 0 < d / 2 := by omega
      have ho : Odd (d / 2) := Nat.odd_iff.mpr (by omega)
      rw [he] at hω ⊢
      exact twice_odd_Delta_rawE_coeff_mem hω ho hh K i

end QCatalan.Generic
