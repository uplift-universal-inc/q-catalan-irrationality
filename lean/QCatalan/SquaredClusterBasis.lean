import QCatalan.CyclotomicAuxGeneric
import QCatalan.CyclotomicAuxBasis
import QZeta3.LocalClusterTransport

/-! # The invertible cluster basis for squared geometric nodes -/

open Polynomial Finset
namespace QCatalan.Generic

open QZeta3.Generic (regularAt localEval localBase clusterMultiplicity ClusterIndex
  movingClusterPoly movingClusterComplement clusterEquivFin)

variable {k : Type*} [Field k]

noncomputable def squaredLocalCenter (ω : k) (r : ℕ) : regularAt ω :=
  ⟨RatFunc.C ((ω^2)^r), by
    simpa only [RatFunc.algebraMap_C] using QZeta3.Generic.polynomial_mem_regularAt ω (C ((ω^2)^r))⟩

@[simp] theorem localEval_squaredLocalCenter (ω : k) (r : ℕ) :
    localEval ω (squaredLocalCenter ω r) = (ω^2)^r := by
  change RatFunc.eval (RingHom.id k) ω (RatFunc.C ((ω^2)^r)) = _
  simp only [RatFunc.eval_C, RingHom.id_apply]

noncomputable def squaredLocalClusterPoly (ω : k) (K h : ℕ) (i : ClusterIndex K h) :
    (regularAt ω)[X] :=
  movingClusterComplement ((localBase ω)^2) K h i.1.val *
    (X-C (squaredLocalCenter ω i.1.val))^i.2.val

theorem squaredLocalClusterPoly_reduction (ω : k) (K h : ℕ) (hh : 0<h)
    (hω : (ω^2)^h=1) (i : ClusterIndex K h) :
    (squaredLocalClusterPoly ω K h i).map (localEval ω) =
      QZeta3.clusterBasis (fun r : Fin h => (ω^2)^r.val)
        (fun r : Fin h => clusterMultiplicity K h r.val) i := by
  simp only [squaredLocalClusterPoly, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, localEval_squaredLocalCenter]
  have hcomp : (movingClusterComplement ((localBase ω)^2) K h i.1.val).map (localEval ω) =
      movingClusterComplement (ω^2) K h i.1.val := by
    rw [movingClusterComplement, Polynomial.map_prod]
    apply Finset.prod_congr rfl
    intro a ha
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    change X-C (localEval ω (((localBase ω)^2)^a)) = X-C ((ω^2)^a)
    rw [(localEval ω).map_pow, (localEval ω).map_pow, QZeta3.Generic.localEval_localBase]
  rw [hcomp, QZeta3.Generic.movingClusterComplement_reduction (ω^2) K h hh hω]
  rfl

noncomputable def squaredLocalClusterMatrix (ω : k) (K h : ℕ) :
    Matrix (Fin (Fintype.card (ClusterIndex K h))) (Fin (Fintype.card (ClusterIndex K h)))
      (regularAt ω) :=
  Matrix.of fun i j =>
    (squaredLocalClusterPoly ω K h ((Fintype.equivFin (ClusterIndex K h)).symm i)).coeff j.val

theorem squaredLocalClusterMatrix_det_isUnit {ω : k} {K h : ℕ}
    (hω : IsPrimitiveRoot (ω^2) h) (hh : 0<h) :
    IsUnit (squaredLocalClusterMatrix ω K h).det := by
  apply QZeta3.Generic.isUnit_of_localEval_ne_zero
  have hmap : (squaredLocalClusterMatrix ω K h).map (localEval ω) =
      QZeta3.clusterBasisMatrix (fun r : Fin h => (ω^2)^r.val)
        (fun r : Fin h => clusterMultiplicity K h r.val) := by
    ext i j
    change localEval ω
      ((squaredLocalClusterPoly ω K h ((Fintype.equivFin (ClusterIndex K h)).symm i)).coeff j.val) = _
    rw [← Polynomial.coeff_map, squaredLocalClusterPoly_reduction ω K h hh hω.pow_eq_one]
    rfl
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap]
  apply QCatalan.clusterBasisMatrix_det_ne_zero
  intro r s h
  exact Fin.ext (hω.pow_inj r.isLt s.isLt h)

noncomputable def squaredTransportPoly (ω : k) (K h : ℕ) (hh : 0<h) (i : Fin K) :
    (RatFunc k)[X] :=
  (squaredLocalClusterPoly ω K h ((clusterEquivFin K h hh).symm i)).map (regularAt ω).subtype

theorem squaredTransportPoly_eq (ω : k) (K h : ℕ) (hh : 0<h) (i : Fin K) :
    squaredTransportPoly ω K h hh i =
      movingClusterPoly ((RatFunc.X : RatFunc k)^2) (RatFunc.C (ω^2)) K h
        ((clusterEquivFin K h hh).symm i).1.val ((clusterEquivFin K h hh).symm i).2.val := by
  simp [squaredTransportPoly, squaredLocalClusterPoly, squaredLocalCenter, movingClusterPoly,
    movingClusterComplement, QZeta3.Generic.localBase, Polynomial.map_prod]

theorem squaredTransportPoly_coeff_mem (ω : k) (K h : ℕ) (hh : 0<h) (i : Fin K) (j : ℕ) :
    (squaredTransportPoly ω K h hh i).coeff j ∈ regularAt ω := by
  unfold squaredTransportPoly
  rw [Polynomial.coeff_map]
  exact ((squaredLocalClusterPoly ω K h ((clusterEquivFin K h hh).symm i)).coeff j).property

theorem squaredTransportPoly_degree_lt (ω : k) (K h : ℕ) (hh : 0<h) (i : Fin K) :
    (squaredTransportPoly ω K h hh i).natDegree < K := by
  rw [squaredTransportPoly_eq, movingClusterPoly]
  rw [Polynomial.natDegree_mul (QZeta3.Generic.movingClusterComplement_monic _ _ _ _).ne_zero
      (((monic_X_sub_C _).pow _).ne_zero), QZeta3.Generic.movingClusterComplement_natDegree,
    Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  have hj := ((clusterEquivFin K h hh).symm i).2.isLt
  have hm : clusterMultiplicity K h ((clusterEquivFin K h hh).symm i).1.val ≤ K := by
    have := Finset.card_filter_le (s := Icc 1 K)
      (p := fun a => a%h=((clusterEquivFin K h hh).symm i).1.val)
    simpa [clusterMultiplicity, QZeta3.Generic.clusterIndices] using this
  omega

theorem squaredTransport_det_eq (ω : k) (K h : ℕ) (hh : 0<h) :
    (polynomialChange K (squaredTransportPoly ω K h hh)).det =
      ((squaredLocalClusterMatrix ω K h).det : RatFunc k) := by
  let e := finCongr (QZeta3.Generic.clusterIndex_card K h hh)
  have he : polynomialChange K (squaredTransportPoly ω K h hh) =
      ((squaredLocalClusterMatrix ω K h).reindex e e).map (regularAt ω).subtype := by
    ext i j
    simp [polynomialChange, squaredTransportPoly, squaredLocalClusterMatrix,
      clusterEquivFin, Matrix.reindex, Matrix.submatrix, e]
  have hmap := (RingHom.map_det (regularAt ω).subtype
    ((squaredLocalClusterMatrix ω K h).reindex e e)).symm
  change (((squaredLocalClusterMatrix ω K h).reindex e e).map (regularAt ω).subtype).det =
    (((squaredLocalClusterMatrix ω K h).reindex e e).det : RatFunc k) at hmap
  rw [he, hmap, Matrix.det_reindex_self]

theorem squaredTransport_det_ne_zero {ω : k} {K h : ℕ}
    (hω : IsPrimitiveRoot (ω^2) h) (hh : 0<h) :
    (polynomialChange K (squaredTransportPoly ω K h hh)).det ≠ 0 := by
  rw [squaredTransport_det_eq]
  exact (IsUnit.map (regularAt ω).subtype
    (squaredLocalClusterMatrix_det_isUnit hω hh)).ne_zero

theorem squaredTransport_det_inv_mem {ω : k} {K h : ℕ}
    (hω : IsPrimitiveRoot (ω^2) h) (hh : 0<h) :
    (polynomialChange K (squaredTransportPoly ω K h hh)).det⁻¹ ∈ regularAt ω := by
  rw [squaredTransport_det_eq]
  apply QZeta3.Generic.inv_mem_regularAt_of_eval_ne_zero
  exact (IsUnit.map (localEval ω) (squaredLocalClusterMatrix_det_isUnit hω hh)).ne_zero

end QCatalan.Generic
