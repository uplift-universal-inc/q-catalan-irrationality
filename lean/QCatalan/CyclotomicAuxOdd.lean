import QCatalan.RawCyclotomicWeights
import QCatalan.SquaredClusterBasis
import QCatalan.RawCyclotomicCost

/-! # Odd-order local denominator bounds for the actual q-Catalan determinant -/

open Polynomial Finset Matrix
namespace QCatalan

def oddRowWeight (m j : ℕ) : ℕ := (m + 2) / 2 - j
def oddColWeight (m j : ℕ) : ℕ := (m + 1) / 2 - j

theorem odd_weights_clear (m j k : ℕ) :
    m + 1 ≤ oddRowWeight m j + oddColWeight m k + (j + k) := by
  unfold oddRowWeight oddColWeight
  omega

/-- The odd-order integer weights have exactly the paper's cluster cost. -/
theorem sum_odd_weights (m : ℕ) :
    (∑ j ∈ range m, (oddRowWeight m j + oddColWeight m j)) = clusterCost m := by
  by_cases hm : m = 0
  · simp [hm, clusterCost]
  · unfold clusterCost
    rw [ite_eq_right hm]
    calc
      (∑ j ∈ range m, (oddRowWeight m j + oddColWeight m j)) =
          ∑ j ∈ range (m+2), ((m+2)/2-j + ((m+2-1)/2-j)) := by
        unfold oddRowWeight oddColWeight
        have hsub : m+2-1=m+1 := by omega
        rw [hsub]
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro j hj hj'
        simp only [Finset.mem_range] at hj hj'
        have h1 : (m+2)/2-j = 0 := by omega
        have h2 : (m+1)/2-j = 0 := by omega
        omega
      _ = _ := sum_raw_weights (m+2)

/-- Summation of any function of the balanced cluster cardinalities. -/
theorem sum_function_clusterMultiplicity (K d : ℕ) (hd : 0 < d) (f : ℕ → ℕ) :
    (∑ r ∈ range d, f (QZeta3.Generic.clusterMultiplicity K d r)) =
      (K % d) * f (K / d + 1) + (d - K % d) * f (K / d) := by
  classical
  let q := K / d
  let A := (range d).filter (fun r => QZeta3.Generic.clusterMultiplicity K d r = q+1)
  let B := (range d).filter (fun r => ¬QZeta3.Generic.clusterMultiplicity K d r = q+1)
  have hcard : A.card + B.card = d := by
    simpa [A, B] using Finset.card_filter_add_card_filter_not (s := range d)
      (fun r => QZeta3.Generic.clusterMultiplicity K d r = q+1)
  have he (r : ℕ) (hr : r ∈ range d) :
      QZeta3.Generic.clusterMultiplicity K d r =
        if QZeta3.Generic.clusterMultiplicity K d r = q+1 then q+1 else q := by
    split_ifs with h
    · exact h
    · rcases QZeta3.Generic.clusterMultiplicity_balanced (K := K) hd (mem_range.mp hr) with hq | hq
      · exact hq
      · exact False.elim (h hq)
  have hsum : K = A.card * (q+1) + B.card * q := by
    rw [← QZeta3.Generic.sum_clusterMultiplicity (K := K) hd]
    calc (∑ r ∈ range d, QZeta3.Generic.clusterMultiplicity K d r) =
        ∑ r ∈ range d,
          if QZeta3.Generic.clusterMultiplicity K d r = q+1 then q+1 else q :=
            Finset.sum_congr rfl he
      _ = _ := by rw [Finset.sum_ite]; simp [A, B]
  have hA : A.card = K % d := by
    have hdiv := Nat.mod_add_div K d
    dsimp [q] at hsum
    nlinarith
  have hB : B.card = d - K % d := by omega
  calc (∑ r ∈ range d, f (QZeta3.Generic.clusterMultiplicity K d r)) =
      ∑ r ∈ range d,
        if QZeta3.Generic.clusterMultiplicity K d r = q+1 then f (q+1) else f q := by
          apply Finset.sum_congr rfl
          intro r hr
          simpa only [apply_ite] using congrArg f (he r hr)
    _ = A.card * f (q+1) + B.card * f q := by rw [Finset.sum_ite]; simp [A, B]
    _ = _ := by rw [hA, hB]

/-- Exact total odd-order clearing cost. -/
theorem sum_odd_cluster_cost (K d : ℕ) (hd : 0 < d) :
    (∑ i : QZeta3.Generic.ClusterIndex K d,
      (oddRowWeight (QZeta3.Generic.clusterMultiplicity K d i.1.val) i.2.val +
       oddColWeight (QZeta3.Generic.clusterMultiplicity K d i.1.val) i.2.val)) =
      (K % d) * clusterCost (K / d + 1) + (d - K % d) * clusterCost (K / d) := by
  have hi (r : Fin d) : (∑ j : Fin (QZeta3.Generic.clusterMultiplicity K d r.val),
      (oddRowWeight (QZeta3.Generic.clusterMultiplicity K d r.val) j.val +
       oddColWeight (QZeta3.Generic.clusterMultiplicity K d r.val) j.val)) =
        clusterCost (QZeta3.Generic.clusterMultiplicity K d r.val) := by
    rw [Fin.sum_univ_eq_sum_range (fun j =>
      oddRowWeight (QZeta3.Generic.clusterMultiplicity K d r.val) j +
      oddColWeight (QZeta3.Generic.clusterMultiplicity K d r.val) j)
      (QZeta3.Generic.clusterMultiplicity K d r.val)]
    exact sum_odd_weights _
  rw [Fintype.sum_sigma]
  simp_rw [hi]
  rw [Fin.sum_univ_eq_sum_range (fun r => clusterCost (QZeta3.Generic.clusterMultiplicity K d r)) d]
  exact sum_function_clusterMultiplicity K d hd clusterCost

namespace Generic
open QZeta3.Generic (regularAt uniformizer collisionCount clusterMultiplicity
  movingClusterPoly movingClusterComplement ClusterIndex clusterEquivFin)
variable {k : Type*} [Field k] [CharZero k]

/-- At odd cyclotomic orders, squaring does not change the collision spacing. -/
theorem primitive_square_odd {ω : k} {d : ℕ} (hω : IsPrimitiveRoot ω d) (hd : Odd d) :
    IsPrimitiveRoot (ω ^ 2) d := hω.pow_of_coprime 2 hd.coprime_two_left

theorem Lpoly_mem_of_mu_mem (ω : k) (f : (RatFunc k)[X])
    (hf : ∀ j, f.coeff j ∈ regularAt ω)
    (hmu : ∀ j, mu (RatFunc.X : RatFunc k) j ∈ regularAt ω) :
    Lpoly (RatFunc.X : RatFunc k) f ∈ regularAt ω := by
  unfold Lpoly
  exact (regularAt ω).sum_mem fun j hj => (regularAt ω).mul_mem (hf j) (hmu j)

/-- The finite tail before the first possible geometric root is regular. -/
theorem S_mem_regularAt_below_order (ω : k) (d N : ℕ)
    (hω : IsPrimitiveRoot ω d) (hN : N < d) :
    S (RatFunc.X : RatFunc k) N ∈ regularAt ω := by
  unfold S
  apply (regularAt ω).sum_mem
  intro b hb
  have hbω : ω ^ b ≠ 1 := hω.pow_ne_one_of_pos_of_lt
    (by have := (mem_Icc.mp hb).1; omega) (by have := (mem_Icc.mp hb).2; omega)
  have hden : ((1 - (RatFunc.X : RatFunc k) ^ b) ^ 2)⁻¹ ∈ regularAt ω := by
    have hp := QZeta3.Generic.inv_polynomial_mem_regularAt ω ((1 - Polynomial.X ^ b) ^ 2)
      (by simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_one,
        Polynomial.eval_X]; exact pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hbω)))
    simpa only [map_pow, map_sub, map_one, RatFunc.algebraMap_X] using hp
  apply (regularAt ω).mul_mem (intCast_mem (regularAt ω) (QCatalan.chi b))
  unfold g2
  rw [div_eq_mul_inv]
  exact (regularAt ω).mul_mem ((regularAt ω).pow_mem (QZeta3.Generic.base_mem_regularAt ω) b) hden

/-- Direct odd-order weights clear every actual proper summand. -/
theorem movingCluster_proper_term_mem_odd {ω : k} {d : ℕ}
    (hω : IsPrimitiveRoot ω d) (hd : 0 < d) (hodd : Odd d) (hω0 : ω ≠ 0)
    (K r s j l a : ℕ) (ha : a ∈ Icc 1 K) (i : ℕ) :
    (C (uniformizer ω ^ (oddRowWeight (clusterMultiplicity K d r) j +
      oddColWeight (clusterMultiplicity K d s) l) *
      ((movingClusterPoly ((RatFunc.X : RatFunc k)^2) (RatFunc.C (ω^2)) K d r j).eval
          (RatFunc.X^(2*a)) *
        (movingClusterPoly ((RatFunc.X : RatFunc k)^2) (RatFunc.C (ω^2)) K d s l).eval
          (RatFunc.X^(2*a)) * (-1)^a /
        (RatFunc.X^(2*a) * (derivative (F (RatFunc.X : RatFunc k) K)).eval
          (RatFunc.X^(2*a))))) * (X-C (S (RatFunc.X : RatFunc k) (2*a)))).coeff i ∈ regularAt ω := by
  have hsq := primitive_square_odd hω hodd
  by_cases har : a % d = r
  · by_cases has : a % d = s
    · have hrs : s = r := has.symm.trans har
      rw [hrs]
      apply proper_term_coeff_mem ω hω0 K a ha _ (j+l) 2
      · exact QZeta3.Generic.product_div_uniformizer_pow_mem ω _ _ j l
          (movingClusterPoly_eval_div_mem hsq K r j a har)
          (movingClusterPoly_eval_div_mem hsq K r l a har)
      · exact uniformizer_sq_mul_S_mem ω hω0 (2*a)
      · rw [QZeta3.Generic.collisionCount_eq_clusterMultiplicity_sub_one hsq hd K a ha, har]
        have hm : 0 < clusterMultiplicity K d r := by
          apply Finset.card_pos.mpr
          exact ⟨a, Finset.mem_filter.mpr ⟨ha, har⟩⟩
        have hw := odd_weights_clear (clusterMultiplicity K d r) j l
        omega
    · have hz := QZeta3.Generic.movingClusterPoly_eval_zero
        ((RatFunc.X : RatFunc k)^2) (RatFunc.C (ω^2)) K d s l a ha has
      simp only [← pow_mul] at hz
      rw [hz]
      simp
  · have hz := QZeta3.Generic.movingClusterPoly_eval_zero
      ((RatFunc.X : RatFunc k)^2) (RatFunc.C (ω^2)) K d r j a ha har
    simp only [← pow_mul] at hz
    rw [hz]
    simp

/-- Any regular polynomial moments can be added after clearing the proper entries. -/
theorem gram_det_mem_of_regular_moments (ω : k) (K : ℕ)
    (G : Fin K → (RatFunc k)[X]) (hGcoeff : ∀ i j, (G i).coeff j ∈ regularAt ω)
    (hmu : ∀ j, mu (RatFunc.X : RatFunc k) j ∈ regularAt ω)
    (r c : Fin K → ℕ)
    (hproper : ∀ i j, C (uniformizer ω ^ (r i + c j)) *
      (∑ a ∈ Icc 1 K, C ((G i * G j).eval (RatFunc.X ^ (2 * a)) * (-1) ^ a /
        (RatFunc.X ^ (2 * a) * (derivative (F (RatFunc.X : RatFunc k) K)).eval
          (RatFunc.X ^ (2 * a)))) *
        (X - C (S (RatFunc.X : RatFunc k) (2 * a)))) ∈
          Polynomial.liftsRing (regularAt ω).subtype) :
    C (uniformizer ω) ^ ((∑ i, r i) + (∑ i, c i)) *
      (unnormalizedGram RatFunc.X K G).det ∈ Polynomial.liftsRing (regularAt ω).subtype := by
  let R := regularAt ω
  let T := Polynomial.liftsRing R.subtype
  apply QZeta3.det_weighted_mem_subring
  intro i j
  have hprod : ∀ t, (G i * G j).coeff t ∈ R := by
    apply (QZeta3.Generic.coeff_mem_iff_lifts R _).mpr
    exact T.mul_mem ((QZeta3.Generic.coeff_mem_iff_lifts R _).mp (hGcoeff i))
      ((QZeta3.Generic.coeff_mem_iff_lifts R _).mp (hGcoeff j))
  have hquot := quotient_coeff_mem_subring R RatFunc.X
    (QZeta3.Generic.base_mem_regularAt ω) K (G i * G j) hprod
  have hpoly := Lpoly_mem_of_mu_mem ω _ hquot hmu
  change C (uniformizer ω) ^ (r i+c j) * momentPolynomial RatFunc.X K (G i * G j) ∈ T
  unfold momentPolynomial
  rw [← map_pow, mul_sub]
  apply T.sub_mem
  · rw [← map_mul]
    exact QZeta3.Generic.C_mem_lifts_regularAt ω _
      (R.mul_mem (R.pow_mem (QZeta3.Generic.uniformizer_mem ω) _) hpoly)
  · exact hproper i j

/-- Low odd-order denominator bound, with the exact sum of integer cluster weights. -/
theorem odd_gram_det_mem {ω : k} {K d : ℕ}
    (hω : IsPrimitiveRoot ω d) (hd : 0 < d) (hodd : Odd d) (hω0 : ω ≠ 0)
    (e : Fin K ≃ ClusterIndex K d) :
    let G := fun i : Fin K => movingClusterPoly ((RatFunc.X : RatFunc k)^2) (RatFunc.C (ω^2))
      K d (e i).1.val (e i).2.val
    let r := fun i : Fin K => oddRowWeight (clusterMultiplicity K d (e i).1.val) (e i).2.val
    let c := fun i : Fin K => oddColWeight (clusterMultiplicity K d (e i).1.val) (e i).2.val
    C (uniformizer ω)^((∑ i, r i)+(∑ i, c i)) *
      (unnormalizedGram RatFunc.X K G).det ∈ Polynomial.liftsRing (regularAt ω).subtype := by
  intro G r c
  have hc : RatFunc.C (ω^2) ∈ regularAt ω := by
    simpa only [RatFunc.algebraMap_C] using QZeta3.Generic.polynomial_mem_regularAt ω (C (ω^2))
  apply gram_det_mem_of_regular_moments ω K G
  · intro i j
    exact QZeta3.Generic.movingClusterPoly_coeff_mem (regularAt ω) _ _
      ((regularAt ω).pow_mem (QZeta3.Generic.base_mem_regularAt ω) 2) hc _ _ _ _ _
  · intro j
    exact mu_mem_regularAt_odd_order ω d j hω hodd
  · intro i j
    rw [Finset.mul_sum]
    apply (Polynomial.liftsRing (regularAt ω).subtype).sum_mem
    intro a ha
    apply (QZeta3.Generic.coeff_mem_iff_lifts (regularAt ω) _).mp
    intro l
    rw [← mul_assoc, ← map_mul, Polynomial.eval_mul]
    exact movingCluster_proper_term_mem_odd hω hd hodd hω0 K
      (e i).1.val (e j).1.val (e i).2.val (e j).2.val a ha l

/-- The complete low odd-order coefficient bound for the actual determinant. -/
theorem odd_low_Delta_coeff_mem {ω : k} {K d : ℕ}
    (hω : IsPrimitiveRoot ω d) (hd : 0 < d) (hodd : Odd d) (hω0 : ω ≠ 0)
    (hdK : d ≤ K) (i : ℕ) :
    uniformizer ω ^ rawE K d * (Delta (RatFunc.X : RatFunc k) K).coeff i ∈ regularAt ω := by
  let e := (clusterEquivFin K d hd).symm
  let G := squaredTransportPoly ω K d hd
  let r := fun j : Fin K => oddRowWeight (clusterMultiplicity K d (e j).1.val) (e j).2.val
  let c := fun j : Fin K => oddColWeight (clusterMultiplicity K d (e j).1.val) (e j).2.val
  have he : (∑ j, r j) + (∑ j, c j) = rawE K d := by
    rw [← Finset.sum_add_distrib]
    change (∑ j : Fin K, (fun x : ClusterIndex K d =>
      oddRowWeight (clusterMultiplicity K d x.1.val) x.2.val +
      oddColWeight (clusterMultiplicity K d x.1.val) x.2.val) (e j)) = _
    have heq := e.sum_comp (fun x : ClusterIndex K d =>
      oddRowWeight (clusterMultiplicity K d x.1.val) x.2.val +
      oddColWeight (clusterMultiplicity K d x.1.val) x.2.val)
    rw [heq, sum_odd_cluster_cost K d hd]
    simp only [rawE, ite_eq_right (by omega : d ≠ 0), Nat.odd_iff.mp hodd, ite_true, hdK]
  have hdet := odd_gram_det_mem hω hd hodd hω0 e
  change C (uniformizer ω)^((∑ j, r j)+(∑ j, c j)) *
    (unnormalizedGram RatFunc.X K (fun j => movingClusterPoly ((RatFunc.X : RatFunc k)^2)
      (RatFunc.C (ω^2)) K d (e j).1.val (e j).2.val)).det ∈ _ at hdet
  have hG : G = fun j => movingClusterPoly ((RatFunc.X : RatFunc k)^2)
      (RatFunc.C (ω^2)) K d (e j).1.val (e j).2.val := by
    funext j
    exact squaredTransportPoly_eq ω K d hd j
  rw [← hG, he] at hdet
  exact Delta_scaled_coeff_mem_of_gram ω K (rawE K d) G
    (squaredTransportPoly_degree_lt ω K d hd)
    (squaredTransport_det_ne_zero (primitive_square_odd hω hodd) hd)
    (squaredTransport_det_inv_mem (primitive_square_odd hω hodd) hd) hdet i

end Generic
end QCatalan
