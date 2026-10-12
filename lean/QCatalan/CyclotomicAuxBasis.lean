import QZeta3.ClusterBasis

/-! # Cluster independence permitting empty classes

Empty residue classes contribute no basis vectors, so the Chinese remainder
argument does not require every class to be populated. This also covers the
cyclotomic orders larger than the determinant size.
-/

open Polynomial Finset
namespace QCatalan
variable {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]

/-- Chinese remainder independence with arbitrary nonnegative multiplicities. -/
theorem clusterBasis_linearIndependent (a : ι → k) (ha : Function.Injective a) (m : ι → ℕ) :
    LinearIndependent k (QZeta3.clusterBasis a m) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  let Q : ι → k[X] := fun r => QZeta3.clusterCombination (a r) (m r) (fun j => c ⟨r,j⟩)
  have hsum : ∑ r, QZeta3.clusterComplement a m r * Q r = 0 := by
    simpa only [Q, QZeta3.clusterBasis, QZeta3.clusterCombination, Fintype.sum_sigma,
      Polynomial.smul_eq_C_mul, Finset.mul_sum, mul_left_comm, mul_assoc] using hc
  have hdvd : QZeta3.clusterFactor a m i.1 ∣
      ∑ s ∈ univ.erase i.1, QZeta3.clusterComplement a m s * Q s := by
    apply Finset.dvd_sum
    intro s hs
    exact dvd_mul_of_dvd_left
      (QZeta3.clusterFactor_dvd_complement a m (Finset.mem_erase.mp hs).1.symm) _
  have he := Finset.sum_erase_add univ (fun s => QZeta3.clusterComplement a m s * Q s)
    (mem_univ i.1)
  rw [hsum] at he
  have heq : QZeta3.clusterComplement a m i.1 * Q i.1 =
      -(∑ s ∈ univ.erase i.1, QZeta3.clusterComplement a m s * Q s) := by
    linear_combination he
  have hterm : QZeta3.clusterFactor a m i.1 ∣ QZeta3.clusterComplement a m i.1 * Q i.1 := by
    rw [heq]
    exact dvd_neg.mpr hdvd
  have hdiv := (QZeta3.clusterFactor_coprime_complement a ha m i.1).dvd_of_dvd_mul_left hterm
  have hm : 0 < m i.1 := Nat.zero_lt_of_lt i.2.isLt
  have hzero : Q i.1 = 0 := by
    apply Polynomial.eq_zero_of_dvd_of_natDegree_lt hdiv
    simpa [QZeta3.clusterFactor] using
      QZeta3.clusterCombination_degree (a i.1) (m i.1) hm (fun j => c ⟨i.1,j⟩)
  exact QZeta3.clusterCombination_zero (a i.1) (m i.1) _ hzero i.2

/-- The complete coefficient determinant remains nonzero when some clusters are empty. -/
theorem clusterBasisMatrix_det_ne_zero (a : ι → k) (ha : Function.Injective a) (m : ι → ℕ) :
    (QZeta3.clusterBasisMatrix a m).det ≠ 0 := by
  apply QZeta3.coeffMatrix_det_ne_zero
  · intro i
    simpa only [Fintype.card_sigma, Fintype.card_fin] using
      QZeta3.clusterBasis_natDegree_lt a m ((Fintype.equivFin (Σ r, Fin (m r))).symm i)
  · exact (clusterBasis_linearIndependent a ha m).comp _ (Equiv.injective _)

end QCatalan
