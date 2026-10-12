import QCatalan.CyclotomicAuxOdd

/-! # The outer odd-order cyclotomic range

There are no collisions when `K < d`. In the adapted basis only rows whose
node tail reaches the first possible pole require the two-pole allowance.
-/

open Polynomial Finset
namespace QCatalan

open QZeta3.Generic (clusterMultiplicity ClusterIndex clusterEquivFin)

/-- Weighted counting of the actual nodes through the cluster reindexing. -/
theorem sum_cluster_index_weight (K d : ℕ) (hd : 0<d) (w : ℕ → ℕ) :
    (∑ i : ClusterIndex K d, w i.1.val) = ∑ a ∈ Icc 1 K, w (a%d) := by
  rw [Fintype.sum_sigma]
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun r => clusterMultiplicity K d r * w r)]
  have hf := Finset.sum_fiberwise_of_maps_to'
    (s := Icc 1 K) (t := range d) (g := fun a : ℕ => a%d)
    (fun a _ => mem_range.mpr (Nat.mod_lt a hd)) w
  simpa [QZeta3.Generic.clusterMultiplicity, QZeta3.Generic.clusterIndices] using hf

/-- Exactly the tails reaching index `d` need the double-pole allowance. -/
theorem sum_high_odd_weights (K d : ℕ) (hd : 0<d) (hKd : K<d) :
    (∑ i : ClusterIndex K d, if d ≤ 2*i.1.val then 2 else 0) =
      2*(K-(d-1)/2) := by
  rw [sum_cluster_index_weight K d hd (fun a : ℕ => if d ≤ 2*a then 2 else 0)]
  have hm (a : ℕ) (ha : a ∈ Icc 1 K) : a%d=a :=
    Nat.mod_eq_of_lt (lt_of_le_of_lt (mem_Icc.mp ha).2 hKd)
  rw [Finset.sum_congr rfl (fun a ha => by rw [hm a ha])]
  rw [← Finset.sum_filter]
  have hf : ((Icc 1 K).filter (fun a => d ≤ 2*a)) = Icc ((d+1)/2) K := by
    ext a
    simp only [mem_filter, mem_Icc]
    omega
  rw [hf, sum_const, Nat.card_Icc]
  simp only [smul_eq_mul]
  have he : K+1-(d+1)/2 = K-(d-1)/2 := by omega
  rw [he, mul_comm]

namespace Generic
open QZeta3.Generic (regularAt uniformizer collisionCount movingClusterPoly)
variable {k : Type*} [Field k] [CharZero k]

/-- In the outer range every actual node derivative is locally a unit. -/
theorem collisionCount_high_odd_zero {ω : k} {K d a : ℕ}
    (hω : IsPrimitiveRoot ω d) (hd : 0<d) (hodd : Odd d) (hKd : K<d)
    (ha : a ∈ Icc 1 K) : collisionCount (ω^2) K a = 0 := by
  rw [QZeta3.Generic.collisionCount_eq_clusterMultiplicity_sub_one
    (primitive_square_odd hω hodd) hd K a ha]
  have hb := QZeta3.Generic.clusterMultiplicity_balanced (K := K) hd (Nat.mod_lt a hd)
  have hdiv : K/d=0 := Nat.div_eq_of_lt hKd
  rcases hb with hb | hb <;> rw [hdiv] at hb <;> omega

/-- An outer-range proper summand clears by a row weight alone. -/
theorem high_odd_proper_term_mem {ω : k} {K d : ℕ}
    (hω : IsPrimitiveRoot ω d) (hd : 0<d) (hodd : Odd d) (hω0 : ω ≠ 0)
    (hKd : K<d) (r s j l a : ℕ) (ha : a ∈ Icc 1 K) (i : ℕ) :
    (C (uniformizer ω ^ (if d ≤ 2*r then 2 else 0) *
      ((movingClusterPoly ((RatFunc.X : RatFunc k)^2) (RatFunc.C (ω^2)) K d r j).eval
          (RatFunc.X^(2*a)) *
        (movingClusterPoly ((RatFunc.X : RatFunc k)^2) (RatFunc.C (ω^2)) K d s l).eval
          (RatFunc.X^(2*a)) * (-1)^a /
        (RatFunc.X^(2*a) * (derivative (F (RatFunc.X : RatFunc k) K)).eval
          (RatFunc.X^(2*a))))) * (X-C (S (RatFunc.X : RatFunc k) (2*a)))).coeff i ∈ regularAt ω := by
  by_cases har : a%d=r
  · have haeq : a=r := by
      rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (mem_Icc.mp ha).2 hKd)] at har
      exact har
    have hconst : RatFunc.C (ω^2) ∈ regularAt ω := by
      simpa only [RatFunc.algebraMap_C] using
        QZeta3.Generic.polynomial_mem_regularAt ω (C (ω^2))
    have hG := QZeta3.Generic.movingClusterPoly_coeff_mem (regularAt ω)
      ((RatFunc.X : RatFunc k)^2) (RatFunc.C (ω^2))
      ((regularAt ω).pow_mem (QZeta3.Generic.base_mem_regularAt ω) 2) hconst K d r j
    have hH := QZeta3.Generic.movingClusterPoly_coeff_mem (regularAt ω)
      ((RatFunc.X : RatFunc k)^2) (RatFunc.C (ω^2))
      ((regularAt ω).pow_mem (QZeta3.Generic.base_mem_regularAt ω) 2) hconst K d s l
    have hN :
        ((movingClusterPoly ((RatFunc.X : RatFunc k)^2) (RatFunc.C (ω^2)) K d r j).eval
          (RatFunc.X^(2*a)) *
        (movingClusterPoly ((RatFunc.X : RatFunc k)^2) (RatFunc.C (ω^2)) K d s l).eval
          (RatFunc.X^(2*a))) / uniformizer ω^0 ∈ regularAt ω := by
      simp only [pow_zero, div_one]
      exact (regularAt ω).mul_mem
        (QZeta3.Generic.eval_mem_regularAt ω _ hG _
          ((regularAt ω).pow_mem (QZeta3.Generic.base_mem_regularAt ω) (2*a)))
        (QZeta3.Generic.eval_mem_regularAt ω _ hH _
          ((regularAt ω).pow_mem (QZeta3.Generic.base_mem_regularAt ω) (2*a)))
    by_cases ht : d ≤ 2*r
    · rw [ite_eq_left ht]
      apply proper_term_coeff_mem ω hω0 K a ha _ 0 2 2 hN
      · exact uniformizer_sq_mul_S_mem ω hω0 (2*a)
      · rw [collisionCount_high_odd_zero hω hd hodd hKd ha]
    · rw [ite_eq_right ht]
      apply proper_term_coeff_mem_of_tail_regular ω hω0 K a ha _ 0 0 hN
      · exact S_mem_regularAt_below_order ω d (2*a) hω (by omega)
      · rw [collisionCount_high_odd_zero hω hd hodd hKd ha]
  · have hz := QZeta3.Generic.movingClusterPoly_eval_zero
      ((RatFunc.X : RatFunc k)^2) (RatFunc.C (ω^2)) K d r j a ha har
    simp only [← pow_mul] at hz
    rw [hz]
    simp

/-- Exact local coefficient clearing in the entire high odd-order range. -/
theorem odd_high_Delta_rawE_coeff_mem {ω : k} {K d : ℕ}
    (hω : IsPrimitiveRoot ω d) (hd : 0<d) (hodd : Odd d) (hω0 : ω ≠ 0)
    (hKd : K<d) (i : ℕ) :
    uniformizer ω ^ rawE K d * (Delta (RatFunc.X : RatFunc k) K).coeff i ∈ regularAt ω := by
  let e := (clusterEquivFin K d hd).symm
  let G := squaredTransportPoly ω K d hd
  let r := fun j : Fin K => if d ≤ 2*(e j).1.val then 2 else 0
  have hproper (j l : Fin K) :
      C (uniformizer ω ^ (r j + 0)) *
      (∑ a ∈ Icc 1 K, C ((G j * G l).eval (RatFunc.X^(2*a)) * (-1)^a /
        (RatFunc.X^(2*a) * (derivative (F (RatFunc.X : RatFunc k) K)).eval
          (RatFunc.X^(2*a)))) * (X-C (S (RatFunc.X : RatFunc k) (2*a)))) ∈
        Polynomial.liftsRing (regularAt ω).subtype := by
    let T := Polynomial.liftsRing (regularAt ω).subtype
    rw [Finset.mul_sum]
    apply T.sum_mem
    intro a ha
    apply (QZeta3.Generic.coeff_mem_iff_lifts (regularAt ω) _).mp
    intro n
    rw [← mul_assoc, ← map_mul, Polynomial.eval_mul]
    simp only [G, squaredTransportPoly_eq, add_zero]
    exact high_odd_proper_term_mem hω hd hodd hω0 hKd
      (e j).1.val (e l).1.val (e j).2.val (e l).2.val a ha n
  have hdet := gram_det_mem_of_regular_moments ω K G
    (squaredTransportPoly_coeff_mem ω K d hd)
    (fun j => mu_mem_regularAt_odd_order ω d j hω hodd) r (fun _ => 0) hproper
  have he : (∑ j : Fin K, r j) + (∑ _j : Fin K, 0) = rawE K d := by
    simp only [Finset.sum_const_zero, add_zero]
    change (∑ j : Fin K, (fun x : ClusterIndex K d => if d ≤ 2*x.1.val then 2 else 0) (e j)) = _
    rw [e.sum_comp (fun x : ClusterIndex K d => if d ≤ 2*x.1.val then 2 else 0),
      sum_high_odd_weights K d hd hKd]
    simp only [rawE, ite_eq_right (by omega : d ≠ 0), Nat.odd_iff.mp hodd,
      ite_true, ite_eq_right (by omega : ¬d≤K)]
    split_ifs with hh
    · rfl
    · have he : K-(d-1)/2=0 := by omega
      rw [he, mul_zero]
  rw [he] at hdet
  exact Delta_scaled_coeff_mem_of_gram ω K _ G (squaredTransportPoly_degree_lt ω K d hd)
    (squaredTransport_det_ne_zero (primitive_square_odd hω hodd) hd)
    (squaredTransport_det_inv_mem (primitive_square_odd hω hodd) hd) hdet i

end Generic
end QCatalan
