import QCatalan.CyclotomicAuxGeneric
import QZeta3.GenericSpecialization

open Polynomial Finset
open QZeta3.Generic.Specialization

namespace QCatalan.Generic
variable {𝕜 𝕝 : Type*} [Field 𝕜] [Field 𝕝]

/-- The finite denominators needed by the q-Catalan construction. -/
structure LocalizationData (R : Subring 𝕜) (z : 𝕜) (K : ℕ) : Prop where
  geom : QZeta3.Generic.LocalizationData R z (4*K)
  inv_plus_mem : ∀ j ∈ Icc 1 K, (1+z^(2*j))⁻¹ ∈ R

namespace LocalizationData
variable {R : Subring 𝕜} {z : 𝕜} {K : ℕ} (h : LocalizationData R z K)
include h

theorem squared : QZeta3.Generic.LocalizationData R (z^2) K where
  base_mem := R.pow_mem h.geom.base_mem 2
  inv_base_mem := by simpa only [← inv_pow] using R.pow_mem h.geom.inv_base_mem 2
  inv_geom_mem n hn := by
    have hb := h.geom.inv_geom_mem (2*n) (mem_Icc.mpr ⟨by have := (mem_Icc.mp hn).1; omega,
      by have := (mem_Icc.mp hn).2; omega⟩)
    simpa only [pow_mul] using hb

theorem inverse_derivative_mem (a : ℕ) (ha : a ∈ Icc 1 K) :
    ((derivative (F z K)).eval (z^(2*a)))⁻¹ ∈ R := by
  simpa only [F_eq_square_base, pow_mul] using h.squared.inverse_derivative_mem a ha

theorem inv_one_sub_mem (b : ℕ) (hb : b ∈ Icc 1 (4*K)) : (1-z^b)⁻¹ ∈ R := by
  have he : 1-z^b = -(z^b-1) := by ring
  rw [he, inv_neg]
  exact R.neg_mem (h.geom.inv_geom_mem b hb)
end LocalizationData

namespace Specialization
variable {R : Subring 𝕜} {φ : R →+* 𝕝} {z : 𝕜} {w : 𝕝} {K : ℕ}

theorem maps_intCast (n : ℤ) : Maps φ (n : 𝕜) (n : 𝕝) :=
  ⟨(n : R), by simp, by simp⟩

theorem maps_F (hz : Maps φ z w) (K : ℕ) : MapsPolynomial φ (F z K) (F w K) := by
  apply MapsPolynomial.prod
  intro a ha
  exact MapsPolynomial.X.sub (MapsPolynomial.C (hz.pow (2*a)))

theorem maps_res (h : LocalizationData R z K) (hz : Maps φ z w) (k a : ℕ)
    (ha : a ∈ Icc 1 K) : Maps φ (res z K k a) (res w K k a) := by
  unfold res
  simp only [div_eq_mul_inv]
  exact (hz.pow _).mul (((maps_F hz K).derivative.eval (hz.pow (2*a))).inv
    (h.inverse_derivative_mem a ha))

theorem maps_S (h : LocalizationData R z K) (hz : Maps φ z w) (a : ℕ) (ha : a ≤ 4*K) :
    Maps φ (S z a) (S w a) := by
  apply Maps.sum
  intro b hb
  simp only [g2, div_eq_mul_inv, ← inv_pow]
  exact maps_intCast _ |>.mul ((hz.pow b).mul (((Maps.one.sub (hz.pow b)).inv
    (h.inv_one_sub_mem b (mem_Icc.mpr ⟨(mem_Icc.mp hb).1, (mem_Icc.mp hb).2.trans ha⟩))).pow 2))

theorem maps_mu (h : LocalizationData R z K) (hz : Maps φ z w) (j : ℕ) (hj : j ≤ K) :
    Maps φ (mu z j) (mu w j) := by
  by_cases hzero : j=0
  · subst j
    simpa only [mu, Nat.cast_zero, zero_mul, zero_div] using (Maps.zero (φ := φ))
  · simp only [mu, div_eq_mul_inv]
    exact ((Maps.natCast j).mul (hz.pow j)).mul (((Maps.one.add (hz.pow (2*j))).inv
      (h.inv_plus_mem j (mem_Icc.mpr ⟨by omega, hj⟩))))

theorem maps_mLin (h : LocalizationData R z K) (hz : Maps φ z w) (k : ℕ) :
    Maps φ (mLin z K k) (mLin w K k) := by
  apply Maps.neg
  apply Maps.sum
  intro a ha
  simp only [div_eq_mul_inv, ← inv_pow]
  exact ((maps_res h hz k a ha).mul ((Maps.one.neg).pow a)).mul
    ((hz.inv h.geom.inv_base_mem).pow (2*a))

theorem Lpoly_eq_sum_range (z : 𝕜) (f : 𝕜[X]) (n : ℕ) (hn : f.natDegree < n) :
    Lpoly z f = ∑ j ∈ range n, f.coeff j * mu z j := by
  change f.sum (fun j c => c * mu z j) = _
  exact f.sum_over_range' (f := fun j c => c * mu z j) (fun j => zero_mul (mu z j)) n hn

theorem maps_quotient_moment (h : LocalizationData R z K) (hz : Maps φ z w)
    (k : ℕ) (hk : k ≤ 2*K) :
    Maps φ (Lpoly z (X^k /ₘ F z K)) (Lpoly w (X^k /ₘ F w K)) := by
  have hd (v : 𝕜) : (X^k /ₘ F v K).natDegree < K+1 := by
    rw [Polynomial.natDegree_divByMonic _ (F_monic v K), Polynomial.natDegree_X_pow, F_natDegree]
    omega
  have hw : (X^k /ₘ F w K).natDegree < K+1 := by
    rw [Polynomial.natDegree_divByMonic _ (F_monic w K), Polynomial.natDegree_X_pow, F_natDegree]
    omega
  rw [Lpoly_eq_sum_range z _ (K+1) (hd z), Lpoly_eq_sum_range w _ (K+1) hw]
  apply Maps.sum
  intro j hj
  exact (((MapsPolynomial.X.pow k).divByMonic (maps_F hz K) (F_monic z K)).coeff j).mul
    (maps_mu h hz j (by have := mem_range.mp hj; omega))

theorem maps_mConst (h : LocalizationData R z K) (hz : Maps φ z w)
    (k : ℕ) (hk : k ≤ 2*K) : Maps φ (mConst z K k) (mConst w K k) := by
  apply Maps.add (maps_quotient_moment h hz k hk)
  apply Maps.sum
  intro a ha
  simp only [div_eq_mul_inv, ← inv_pow]
  exact (((maps_res h hz k a ha).mul ((Maps.one.neg).pow a)).mul
    (maps_S h hz (2*a) (by have := (mem_Icc.mp ha).2; omega))).mul
    ((hz.inv h.geom.inv_base_mem).pow (2*a))

theorem maps_nrm (hz : Maps φ z w) (K : ℕ) : Maps φ (nrm z K) (nrm w K) :=
  ((Maps.one.neg).pow K).mul (hz.pow (K*(K+1)))

theorem maps_Delta (h : LocalizationData R z K) (hz : Maps φ z w) :
    MapsPolynomial φ (Delta z K) (Delta w K) := by
  apply MapsPolynomial.det
  intro i j
  exact (MapsPolynomial.X.mul (MapsPolynomial.C
    ((maps_nrm hz K).mul (maps_mLin h hz (i.val+j.val))))).add
    (MapsPolynomial.C ((maps_nrm hz K).mul (maps_mConst h hz (i.val+j.val)
      (by have := i.isLt; have := j.isLt; omega))))
end Specialization

namespace LocalizationData
variable {R : Subring 𝕜} {z : 𝕜} {K : ℕ}

theorem Delta_coeff_mem (h : LocalizationData R z K) (i : ℕ) : (Delta z K).coeff i ∈ R := by
  obtain ⟨a, ha, _⟩ := (Specialization.maps_Delta h
    (Maps.of_mem (φ := R.subtype) h.geom.base_mem)).coeff i
  exact ha ▸ a.property
end LocalizationData

namespace Specialization
variable {R : Subring 𝕜} {z : 𝕜} {K : ℕ}

theorem specialize_Delta_coeff (h : LocalizationData R z K) (φ : R →+* 𝕝) (i : ℕ) :
    φ ⟨(Delta z K).coeff i, h.Delta_coeff_mem i⟩ =
      (Delta (φ ⟨z, h.geom.base_mem⟩) K).coeff i :=
  ((maps_Delta h (Maps.of_mem h.geom.base_mem)).coeff i).value (h.Delta_coeff_mem i)

theorem map_Delta (f : 𝕜 →+* 𝕝) (z : 𝕜) (K : ℕ) :
    (Delta z K).map f = Delta (f z) K := by
  let h : LocalizationData (⊤ : Subring 𝕜) z K :=
    ⟨⟨by trivial, by trivial, by intros; trivial⟩, by intros; trivial⟩
  ext i
  simpa using specialize_Delta_coeff h (f.comp (⊤ : Subring 𝕜).subtype) i
end Specialization
end QCatalan.Generic
