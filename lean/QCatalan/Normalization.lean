import QCatalan.Content
import QCatalan.Polynomial

/-! Gluing the proved base-prime content with any proved integral Laurent clearer. -/
open Polynomial Finset
namespace QCatalan
variable {p : ℕ}

theorem den_eq_one_of_coprime {r : ℚ} (hp : 0 < p) (hcop : Nat.Coprime r.den p) {m : ℕ}
    (h : (r * (p : ℚ) ^ m).den = 1) : r.den = 1 := by
  set n : ℤ := (r * (p : ℚ) ^ m).num with hn
  have hr : r = (n : ℚ) / ((p ^ m : ℕ) : ℤ) := by
    have h1 : ((r * (p : ℚ) ^ m).num : ℚ) = r * (p : ℚ) ^ m := Rat.coe_int_num_of_den_eq_one h
    have hp0 : ((p : ℚ) ^ m) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne')
    rw [← hn] at h1
    push_cast
    rw [h1]
    field_simp
  have hdvd : (r.den : ℤ) ∣ ((p ^ m : ℕ) : ℤ) := by
    rw [hr, Rat.intCast_div_eq_divInt]
    exact Rat.den_dvd _ _
  have hdvd' : r.den ∣ p ^ m := by exact_mod_cast hdvd
  exact Nat.Coprime.eq_one_of_dvd (hcop.pow_right m) hdvd'

/-- Arithmetic gluing for the concrete q-Catalan determinant and any integer clearer.
The visible local-clearing hypothesis is discharged separately by the cyclotomic proof. -/
theorem normalized_coefficient_den (hp : 2 ≤ p) (K i : ℕ) (A : ℤ)
    (hclear : ∃ m : ℕ, ((A : ℚ) * (Delta p K).coeff i * (p : ℚ) ^ m).den = 1) :
    ((Delta p K).coeff i * ((A : ℚ) / (p : ℚ) ^ cK K)).den = 1 := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hrew : (Delta p K).coeff i * ((A : ℚ) / (p : ℚ) ^ cK K) =
      (A : ℚ) * ((Delta p K).coeff i / (p : ℚ) ^ cK K) := by ring
  rw [hrew]
  have hcop : Nat.Coprime ((A : ℚ) * ((Delta p K).coeff i / (p : ℚ) ^ cK K)).den p := by
    have hdvd := Rat.mul_den_dvd (A : ℚ) ((Delta p K).coeff i / (p : ℚ) ^ cK K)
    rw [Rat.den_intCast, one_mul] at hdvd
    exact Nat.Coprime.coprime_dvd_left hdvd (content_coeff hp K i)
  obtain ⟨m, hm⟩ := hclear
  have hm' :
      ((A : ℚ) * ((Delta p K).coeff i / (p : ℚ) ^ cK K) *
        (p : ℚ) ^ (m + cK K)).den = 1 := by
    have heq : (A : ℚ) * ((Delta p K).coeff i / (p : ℚ) ^ cK K) *
        (p : ℚ) ^ (m + cK K) =
        (A : ℚ) * (Delta p K).coeff i * (p : ℚ) ^ m := by
      have hpe : (p : ℚ) ^ cK K ≠ 0 := pow_ne_zero _ hp0
      rw [pow_add]
      field_simp
    rw [heq]
    exact hm
  exact den_eq_one_of_coprime (show 0 < p by omega) hcop hm'

end QCatalan
