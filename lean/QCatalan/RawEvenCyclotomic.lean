import QCatalan.RawCyclotomicWeights
import QCatalan.SquaredClusterBasis
import QCatalan.RawDefs
import QCatalan.RawCyclotomicCost
import QCatalan.CyclotomicAuxOdd

/-! # Actual even-order local bounds for the conservative clearer -/
open Polynomial Finset
namespace QCatalan.Generic
open QZeta3.Generic (regularAt uniformizer clusterMultiplicity clusterEquivFin)
variable {k : Type*} [Field k] [CharZero k]

noncomputable def squaredRowWeight (K h : ℕ) (hh : 0<h) (i : Fin K) : ℕ :=
  rawRowWeight (clusterMultiplicity K h ((clusterEquivFin K h hh).symm i).1.val)
    ((clusterEquivFin K h hh).symm i).2.val

noncomputable def squaredColWeight (K h : ℕ) (hh : 0<h) (i : Fin K) : ℕ :=
  rawColWeight (clusterMultiplicity K h ((clusterEquivFin K h hh).symm i).1.val)
    ((clusterEquivFin K h hh).symm i).2.val

/-- The actual complete proper matrix clears in the locally invertible squared
cluster basis at every even order. -/
theorem squaredTransport_proper_mem {ω : k} {d h : ℕ}
    (hω : IsPrimitiveRoot ω d) (hd : 2 ∣ d) (hsq : IsPrimitiveRoot (ω^2) h)
    (hh : 0<h) (hω0 : ω ≠ 0) (K : ℕ) (i j : Fin K) :
    C (uniformizer ω ^ (squaredRowWeight K h hh i + squaredColWeight K h hh j)) *
      (∑ a ∈ Icc 1 K, C
        ((squaredTransportPoly ω K h hh i * squaredTransportPoly ω K h hh j).eval
          (RatFunc.X^(2*a)) * (-1)^a /
          (RatFunc.X^(2*a) * (derivative (F (RatFunc.X : RatFunc k) K)).eval
            (RatFunc.X^(2*a)))) * (X-C (S (RatFunc.X : RatFunc k) (2*a)))) ∈
      Polynomial.liftsRing (regularAt ω).subtype := by
  let T := Polynomial.liftsRing (regularAt ω).subtype
  rw [Finset.mul_sum]
  apply T.sum_mem
  intro a ha
  apply (QZeta3.Generic.coeff_mem_iff_lifts (regularAt ω) _).mp
  intro l
  rw [← mul_assoc, ← map_mul, Polynomial.eval_mul, squaredTransportPoly_eq, squaredTransportPoly_eq]
  exact movingCluster_proper_term_mem_even_order hω hd hsq hh hω0 K
    ((clusterEquivFin K h hh).symm i).1.val ((clusterEquivFin K h hh).symm j).1.val
    ((clusterEquivFin K h hh).symm i).2.val ((clusterEquivFin K h hh).symm j).2.val a ha l

/-- Raw fourfold bound before rewriting the finite weight sum. -/
theorem fourfold_Delta_weighted_coeff_mem {ω : k} {u : ℕ}
    (hω : IsPrimitiveRoot ω (4*u)) (hu : 0<u) (K i : ℕ) :
    uniformizer ω ^ ((∑ j, squaredRowWeight K (2*u) (by omega) j) +
      (∑ j, squaredColWeight K (2*u) (by omega) j) + (K-u-1)) *
      (Delta (RatFunc.X : RatFunc k) K).coeff i ∈ regularAt ω := by
  have hh : 0 < 2*u := by omega
  have hsq : IsPrimitiveRoot (ω^2) (2*u) :=
    hω.pow (by omega) (by omega : 4*u=2*(2*u))
  have hω0 : ω ≠ 0 := hω.ne_zero (by omega)
  apply Delta_scaled_coeff_mem_of_gram ω K _ (squaredTransportPoly ω K (2*u) hh)
    (squaredTransportPoly_degree_lt ω K (2*u) hh)
    (squaredTransport_det_ne_zero hsq hh) (squaredTransport_det_inv_mem hsq hh)
  apply fourfold_gram_det_mem hω hω0 _
    (squaredTransportPoly_degree_lt ω K (2*u) hh)
    (squaredTransportPoly_coeff_mem ω K (2*u) hh)
  intro a b
  exact squaredTransport_proper_mem hω (by omega) hsq hh hω0 K a b


/-- The finite local weight sum equals the explicit odd-ramp exponent. -/
theorem sum_squared_weights (K h : ℕ) (hh : 0<h) :
    (∑ j, squaredRowWeight K h hh j) + (∑ j, squaredColWeight K h hh j) =
      rawClusterCost K h := by
  rw [← Finset.sum_add_distrib]
  have he := Equiv.sum_comp (clusterEquivFin K h hh).symm
    (fun i : QZeta3.Generic.ClusterIndex K h =>
      rawRowWeight (clusterMultiplicity K h i.1.val) i.2.val +
      rawColWeight (clusterMultiplicity K h i.1.val) i.2.val)
  change (∑ i : Fin K,
    (rawRowWeight (clusterMultiplicity K h ((clusterEquivFin K h hh).symm i).1.val)
      ((clusterEquivFin K h hh).symm i).2.val +
    rawColWeight (clusterMultiplicity K h ((clusterEquivFin K h hh).symm i).1.val)
      ((clusterEquivFin K h hh).symm i).2.val)) = _
  rw [he, Fintype.sum_sigma]
  have hi (r : Fin h) :
      (∑ j : Fin (clusterMultiplicity K h r.val),
        (rawRowWeight (clusterMultiplicity K h r.val) j.val +
        rawColWeight (clusterMultiplicity K h r.val) j.val)) =
      (clusterMultiplicity K h r.val)^2/4 := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
      rawRowWeight (clusterMultiplicity K h r.val) j + rawColWeight (clusterMultiplicity K h r.val) j)]
    exact sum_raw_weights _
  simp_rw [hi]
  rw [Fin.sum_univ_eq_sum_range (fun r : ℕ => (clusterMultiplicity K h r)^2/4)]
  exact sum_cluster_square_div_four K h hh

/-- The exact conservative pole bound at every primitive root of order `4u`. -/
theorem fourfold_Delta_raw_coeff_mem {ω : k} {u : ℕ}
    (hω : IsPrimitiveRoot ω (4*u)) (hu : 0<u) (K i : ℕ) :
    uniformizer ω ^ (rawClusterCost K (2*u) + (K-u-1)) *
      (Delta (RatFunc.X : RatFunc k) K).coeff i ∈ regularAt ω := by
  have h := fourfold_Delta_weighted_coeff_mem hω hu K i
  rwa [sum_squared_weights K (2*u) (by omega)] at h

/-- The complete denominator matrix is regular after the raw cluster weights
at an order twice an odd integer. -/
theorem twice_odd_Delta_raw_coeff_mem {ω : k} {h : ℕ}
    (hω : IsPrimitiveRoot ω (2*h)) (hhodd : Odd h) (hh : 0<h) (K i : ℕ) :
    uniformizer ω ^ rawClusterCost K h *
      (Delta (RatFunc.X : RatFunc k) K).coeff i ∈ regularAt ω := by
  have hsq : IsPrimitiveRoot (ω^2) h := hω.pow (by omega) rfl
  have hω0 : ω ≠ 0 := hω.ne_zero (by omega)
  have hdet := gram_det_mem_of_regular_moments ω K (squaredTransportPoly ω K h hh)
    (squaredTransportPoly_coeff_mem ω K h hh)
    (fun j => mu_mem_regularAt_twice_odd_order ω h j hω hhodd)
    (squaredRowWeight K h hh) (squaredColWeight K h hh)
    (squaredTransport_proper_mem hω (by omega) hsq hh hω0 K)
  rw [sum_squared_weights K h hh] at hdet
  exact Delta_scaled_coeff_mem_of_gram ω K _ (squaredTransportPoly ω K h hh)
    (squaredTransportPoly_degree_lt ω K h hh)
    (squaredTransport_det_ne_zero hsq hh) (squaredTransport_det_inv_mem hsq hh) hdet i

/-- Specialization to the shared raw exponent definition at orders divisible by four. -/
theorem fourfold_Delta_rawE_coeff_mem {ω : k} {u : ℕ}
    (hω : IsPrimitiveRoot ω (4*u)) (hu : 0<u) (K i : ℕ) :
    uniformizer ω ^ rawE K (4*u) *
      (Delta (RatFunc.X : RatFunc k) K).coeff i ∈ regularAt ω := by
  have hd0 : 4*u ≠ 0 := by omega
  have hd2 : (4*u)%2=0 := by omega
  simpa [rawE, hd0, hd2, Nat.mul_div_cancel_left, Nat.mul_mod_right] using
    fourfold_Delta_raw_coeff_mem hω hu K i

/-- Specialization to the shared raw exponent definition at orders twice odd. -/
theorem twice_odd_Delta_rawE_coeff_mem {ω : k} {h : ℕ}
    (hω : IsPrimitiveRoot ω (2*h)) (hhodd : Odd h) (hh : 0<h) (K i : ℕ) :
    uniformizer ω ^ rawE K (2*h) *
      (Delta (RatFunc.X : RatFunc k) K).coeff i ∈ regularAt ω := by
  have hd0 : 2*h ≠ 0 := by omega
  have hd4 : (2*h)%4=2 := by obtain ⟨a, ha⟩ := hhodd; omega
  simpa [rawE, hd0, hd4, Nat.mul_div_cancel_left, Nat.mul_mod_right] using
    twice_odd_Delta_raw_coeff_mem hω hhodd hh K i

end QCatalan.Generic
