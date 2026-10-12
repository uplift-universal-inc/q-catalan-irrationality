import QCatalan.Cyclotomic
import QZeta3.MovingProper

/-!
# Direct cluster clearing for regular q-Catalan tails

At even cyclotomic orders every finite tail is regular. Integer row and column
weights clear each individual proper-fraction summand. This conservative route
does not need interpolation of the tails or their double-zero residue.
-/

open Polynomial Finset

namespace QCatalan

/-- Integer row weights for a cluster of size `m`. -/
def rawRowWeight (m j : ℕ) : ℕ := m / 2 - j
/-- Complementary integer column weights. -/
def rawColWeight (m j : ℕ) : ℕ := (m-1) / 2 - j

theorem raw_weights_clear (m j k : ℕ) :
    m-1 ≤ rawRowWeight m j + rawColWeight m k + (j+k) := by
  unfold rawRowWeight rawColWeight
  omega

namespace Generic

open QZeta3.Generic (regularAt uniformizer collisionCount clusterMultiplicity
  movingClusterPoly movingClusterComplement)
variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- Derivative factorization at the step-two nodes. -/
theorem derivative_F_eval_eq_prod (z : 𝕜) (K a : ℕ) (ha : a ∈ Icc 1 K) :
    (derivative (F z K)).eval (z^(2*a)) =
      ∏ b ∈ (Icc 1 K).erase a, (z^(2*a)-z^(2*b)) := by
  change (derivative (Lagrange.nodal (Icc 1 K) (fun b => z^(2*b)))).eval (z^(2*a)) = _
  rw [Lagrange.eval_nodal_derivative_eval_node_eq (v := fun b => z^(2*b)) ha,
    Lagrange.eval_nodal]

/-- Each colliding derivative factor costs exactly one possible uniformizer. -/
theorem uniformizer_pow_div_derivative_mem (ω : 𝕜) (hω : ω ≠ 0)
    (K a : ℕ) (ha : a ∈ Icc 1 K) :
    uniformizer ω ^ collisionCount (ω^2) K a /
      (derivative (F (RatFunc.X : RatFunc 𝕜) K)).eval (RatFunc.X^(2*a)) ∈ regularAt ω := by
  classical
  have hprod : (∏ b ∈ (Icc 1 K).erase a,
      (if (ω^2)^a = (ω^2)^b then uniformizer ω else 1) /
        ((RatFunc.X : RatFunc 𝕜)^(2*a)-RatFunc.X^(2*b))) ∈ regularAt ω := by
    apply (regularAt ω).prod_mem
    intro b hb
    by_cases hab : (ω^2)^a = (ω^2)^b
    · rw [ite_eq_left hab]
      apply QZeta3.Generic.uniformizer_div_difference_mem ω hω
      have := (mem_erase.mp hb).1
      omega
    · rw [ite_eq_right hab, one_div]
      apply QZeta3.Generic.inv_difference_mem_regularAt
      simpa only [pow_mul] using hab
  rw [Finset.prod_div_distrib] at hprod
  have hnum : (∏ b ∈ (Icc 1 K).erase a,
      if (ω^2)^a = (ω^2)^b then uniformizer ω else 1) =
      uniformizer ω ^ collisionCount (ω^2) K a := by
    rw [← Finset.prod_filter]
    simp [collisionCount]
  rw [hnum, ← derivative_F_eval_eq_prod RatFunc.X K a ha] at hprod
  exact hprod

/-- Pole bookkeeping for the actual signed proper term with a tail pole
allowance `e`. This single statement handles both odd and even orders. -/
theorem proper_term_coeff_mem (ω : 𝕜) (hω : ω ≠ 0)
    (K a : ℕ) (ha : a ∈ Icc 1 K) (N : RatFunc 𝕜) (v e w : ℕ)
    (hN : N / uniformizer ω^v ∈ regularAt ω)
    (hS : uniformizer ω^e * S (RatFunc.X : RatFunc 𝕜) (2*a) ∈ regularAt ω)
    (hw : collisionCount (ω^2) K a + e ≤ w+v) (i : ℕ) :
    (C (uniformizer ω^w *
      (N * (-1)^a / (RatFunc.X^(2*a) *
        (derivative (F (RatFunc.X : RatFunc 𝕜) K)).eval (RatFunc.X^(2*a))))) *
      (X-C (S (RatFunc.X : RatFunc 𝕜) (2*a)))).coeff i ∈ regularAt ω := by
  let D : RatFunc 𝕜 := RatFunc.X^(2*a) *
    (derivative (F (RatFunc.X : RatFunc 𝕜) K)).eval (RatFunc.X^(2*a))
  have hD : uniformizer ω ^ collisionCount (ω^2) K a / D ∈ regularAt ω := by
    have h := (regularAt ω).mul_mem (uniformizer_pow_div_derivative_mem ω hω K a ha)
      ((regularAt ω).pow_mem (QZeta3.Generic.inv_base_mem_regularAt ω hω) (2*a))
    convert h using 1
    simp only [D, div_eq_mul_inv, mul_inv, inv_pow]
    ring
  have hs := (regularAt ω).pow_mem ((regularAt ω).neg_mem (regularAt ω).one_mem) a
  have hN' : (N * (-1)^a) / uniformizer ω^v ∈ regularAt ω := by
    convert (regularAt ω).mul_mem hN hs using 1
    ring
  have hscalar := QZeta3.Generic.scaled_ratio_mem ω (N*(-1)^a) D v
    (collisionCount (ω^2) K a) w hN' hD (by omega)
  have hconstant := QZeta3.Generic.scaled_ratio_mul_mem ω (N*(-1)^a) D
    (S (RatFunc.X : RatFunc 𝕜) (2*a)) v (collisionCount (ω^2) K a) e w hN' hD hS hw
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_sub]
  by_cases hi0 : i = 0
  · subst i
    simpa only [Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub, mul_neg]
      using (regularAt ω).neg_mem hconstant
  · by_cases hi1 : i = 1
    · subst i
      simpa using hscalar
    · simp [Polynomial.coeff_X, Polynomial.coeff_C, hi0, Ne.symm hi1]

/-- A regular signed tail contributes no extra denominator beyond the node
collisions. This statement concerns the actual complete proper-pole factor. -/
theorem proper_term_coeff_mem_of_tail_regular (ω : 𝕜) (hω : ω ≠ 0)
    (K a : ℕ) (ha : a ∈ Icc 1 K) (N : RatFunc 𝕜) (v w : ℕ)
    (hN : N / uniformizer ω^v ∈ regularAt ω)
    (hS : S (RatFunc.X : RatFunc 𝕜) (2*a) ∈ regularAt ω)
    (hw : collisionCount (ω^2) K a ≤ w+v) (i : ℕ) :
    (C (uniformizer ω^w *
      (N * (-1)^a / (RatFunc.X^(2*a) *
        (derivative (F (RatFunc.X : RatFunc 𝕜) K)).eval (RatFunc.X^(2*a))))) *
      (X-C (S (RatFunc.X : RatFunc 𝕜) (2*a)))).coeff i ∈ regularAt ω := by
  let D : RatFunc 𝕜 := RatFunc.X^(2*a) *
    (derivative (F (RatFunc.X : RatFunc 𝕜) K)).eval (RatFunc.X^(2*a))
  have hD : uniformizer ω ^ collisionCount (ω^2) K a / D ∈ regularAt ω := by
    have h := (regularAt ω).mul_mem (uniformizer_pow_div_derivative_mem ω hω K a ha)
      ((regularAt ω).pow_mem (QZeta3.Generic.inv_base_mem_regularAt ω hω) (2*a))
    convert h using 1
    simp only [D, div_eq_mul_inv, mul_inv, inv_pow]
    ring
  have hscalar := QZeta3.Generic.scaled_ratio_mem ω N D v (collisionCount (ω^2) K a) w hN hD hw
  have hsign := (regularAt ω).mul_mem hscalar
    ((regularAt ω).pow_mem ((regularAt ω).neg_mem (regularAt ω).one_mem) a)
  have hscalar' : uniformizer ω^w * (N * (-1)^a / D) ∈ regularAt ω := by
    convert hsign using 1
    ring
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_sub]
  by_cases hi0 : i = 0
  · subst i
    simpa only [Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub, mul_neg]
      using (regularAt ω).neg_mem ((regularAt ω).mul_mem hscalar' hS)
  · by_cases hi1 : i = 1
    · subst i
      simpa using hscalar'
    · simp [Polynomial.coeff_X, Polynomial.coeff_C, hi0, Ne.symm hi1]

/-- The actual squared-node cluster polynomials have their expected vanishing
orders at every node of their own class. -/
theorem movingClusterPoly_eval_div_mem {ω : 𝕜} {h : ℕ}
    (hω : IsPrimitiveRoot (ω^2) h) (K r j a : ℕ) (har : a%h = r) :
    (movingClusterPoly ((RatFunc.X : RatFunc 𝕜)^2) (RatFunc.C (ω^2)) K h r j).eval
      (RatFunc.X^(2*a)) / uniformizer ω^j ∈ regularAt ω := by
  have hpow : ω^(2*a) = (ω^2)^r := by
    rw [pow_mul, pow_eq_pow_mod a hω.pow_eq_one, har]
  have hV := QZeta3.Generic.movingClusterComplement_coeff_mem (regularAt ω)
    ((RatFunc.X : RatFunc 𝕜)^2)
    ((regularAt ω).pow_mem (QZeta3.Generic.base_mem_regularAt ω) 2) K h r
  have hnum := QZeta3.Generic.cluster_numerator_eval_div_mem ω ((ω^2)^r) (2*a) j hpow
    (movingClusterComplement ((RatFunc.X : RatFunc 𝕜)^2) K h r) hV
  simpa only [movingClusterPoly, map_pow] using hnum

/-- Actual weighted proper entries: no interpolation/cancellation hypothesis. -/
theorem movingCluster_proper_term_mem {ω : 𝕜} {h : ℕ}
    (hω : IsPrimitiveRoot (ω^2) h) (hh : 0 < h) (hω0 : ω ≠ 0)
    (K r s j k a : ℕ) (ha : a ∈ Icc 1 K)
    (hS : S (RatFunc.X : RatFunc 𝕜) (2*a) ∈ regularAt ω) (i : ℕ) :
    (C (uniformizer ω ^ (rawRowWeight (clusterMultiplicity K h r) j +
      rawColWeight (clusterMultiplicity K h s) k) *
      ((movingClusterPoly ((RatFunc.X : RatFunc 𝕜)^2) (RatFunc.C (ω^2)) K h r j).eval
          (RatFunc.X^(2*a)) *
        (movingClusterPoly ((RatFunc.X : RatFunc 𝕜)^2) (RatFunc.C (ω^2)) K h s k).eval
          (RatFunc.X^(2*a)) * (-1)^a /
        (RatFunc.X^(2*a) * (derivative (F (RatFunc.X : RatFunc 𝕜) K)).eval
          (RatFunc.X^(2*a))))) * (X-C (S (RatFunc.X : RatFunc 𝕜) (2*a)))).coeff i ∈ regularAt ω := by
  by_cases har : a%h = r
  · by_cases has : a%h = s
    · have hrs : s=r := has.symm.trans har
      rw [hrs]
      apply proper_term_coeff_mem_of_tail_regular ω hω0 K a ha _ (j+k)
      · exact QZeta3.Generic.product_div_uniformizer_pow_mem ω _ _ j k
          (movingClusterPoly_eval_div_mem hω K r j a har)
          (movingClusterPoly_eval_div_mem hω K r k a har)
      · exact hS
      · rw [QZeta3.Generic.collisionCount_eq_clusterMultiplicity_sub_one hω hh K a ha, har]
        exact raw_weights_clear _ _ _
    · have hz := QZeta3.Generic.movingClusterPoly_eval_zero
        ((RatFunc.X : RatFunc 𝕜)^2) (RatFunc.C (ω^2)) K h s k a ha has
      simp only [← pow_mul] at hz
      rw [hz]
      simp
  · have hz := QZeta3.Generic.movingClusterPoly_eval_zero
      ((RatFunc.X : RatFunc 𝕜)^2) (RatFunc.C (ω^2)) K h r j a ha har
    simp only [← pow_mul] at hz
    rw [hz]
    simp

/-- At every even-order root, all properly weighted proper-fraction entries
are regular, including orders divisible by four. -/
theorem movingCluster_proper_term_mem_even_order {ω : 𝕜} {d h : ℕ}
    (hω : IsPrimitiveRoot ω d) (hd : 2 ∣ d)
    (hsq : IsPrimitiveRoot (ω^2) h) (hh : 0 < h) (hω0 : ω ≠ 0)
    (K r s j k a : ℕ) (ha : a ∈ Icc 1 K) (i : ℕ) :
    (C (uniformizer ω ^ (rawRowWeight (clusterMultiplicity K h r) j +
      rawColWeight (clusterMultiplicity K h s) k) *
      ((movingClusterPoly ((RatFunc.X : RatFunc 𝕜)^2) (RatFunc.C (ω^2)) K h r j).eval
          (RatFunc.X^(2*a)) *
        (movingClusterPoly ((RatFunc.X : RatFunc 𝕜)^2) (RatFunc.C (ω^2)) K h s k).eval
          (RatFunc.X^(2*a)) * (-1)^a /
        (RatFunc.X^(2*a) * (derivative (F (RatFunc.X : RatFunc 𝕜) K)).eval
          (RatFunc.X^(2*a))))) * (X-C (S (RatFunc.X : RatFunc 𝕜) (2*a)))).coeff i ∈ regularAt ω :=
  movingCluster_proper_term_mem hsq hh hω0 K r s j k a ha
    (S_mem_regularAt_even_order ω d (2*a) hω hd) i

end Generic
end QCatalan
