import QCatalan.CyclotomicAuxGeneric
import QZeta3.PolynomialMomentRank
import QZeta3.ClusterCounts
import QZeta3.LocalGramBounds
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The double-zero saving in the q-Catalan cyclotomic argument

These are algebraic statements about the specific residue profile in the paper,
including arbitrary formal local units.  The separate interpolation statement
identifying the regularized finite character tails with this profile is not
asserted here.  In particular this module does not assert the global denominator
clearing proposition.
-/

open Finset Matrix

namespace QCatalan

section ResidueIdentity
variable {k : Type*} [Field k] [CharZero k]

/-- The rational identity responsible for the two vanishing residue rows. -/
theorem residue_double_zero_identity (x ε : k) (u : ℕ)
    (hε : ε ^ 2 = 1) (hden : 1 + x ^ (2 * u) ≠ 0) :
    x ^ u / (1 + x ^ (2 * u)) - ε / 2 =
      -ε * (x ^ u - ε) ^ 2 / (2 * (1 + x ^ (2 * u))) := by
  have hpow : x ^ (2 * u) = (x ^ u) ^ 2 := by rw [mul_comm 2 u, pow_mul]
  rw [hpow] at hden ⊢
  field_simp
  linear_combination (ε - 2 * x ^ u) * hε

/-- Formal expansion of the residue profile at a collision center `ρ`. -/
noncomputable def localResidue (u : ℕ) (ρ ε : k) : PowerSeries k :=
  (PowerSeries.C ρ + PowerSeries.X) ^ u *
    (1 + (PowerSeries.C ρ + PowerSeries.X) ^ (2 * u))⁻¹ - PowerSeries.C (ε / 2)

theorem localResidue_factor (u : ℕ) (ρ ε : k) (hρ : ρ ^ u = ε) (hε : ε ^ 2 = 1) :
    localResidue u ρ ε =
      -PowerSeries.C (ε / 2) *
        ((PowerSeries.C ρ + PowerSeries.X) ^ u - PowerSeries.C ε) ^ 2 *
        (1 + (PowerSeries.C ρ + PowerSeries.X) ^ (2 * u))⁻¹ := by
  let A : PowerSeries k := (PowerSeries.C ρ + PowerSeries.X) ^ u
  have hpow : (PowerSeries.C ρ + PowerSeries.X : PowerSeries k) ^ (2 * u) = A ^ 2 := by
    dsimp [A]
    rw [mul_comm 2 u, pow_mul]
  have he : (PowerSeries.C ε : PowerSeries k) ^ 2 = 1 := by
    rw [← map_pow, hε, map_one]
  have hconst : PowerSeries.constantCoeff (1 + A ^ 2) ≠ 0 := by
    simp [A, hρ, hε]
  have hinv := PowerSeries.mul_inv_cancel (1 + A ^ 2) hconst
  have htwo : (2 : k) ≠ 0 := by norm_num
  have hehalf : PowerSeries.C (ε / 2) * 2 = (PowerSeries.C ε : PowerSeries k) := by
    rw [← map_ofNat (PowerSeries.C (R := k)) 2, ← map_mul]
    congr 1
    field_simp
  unfold localResidue
  rw [hpow]
  change A * (1 + A ^ 2)⁻¹ - PowerSeries.C (ε / 2) = _
  have hcore : A - PowerSeries.C (ε / 2) * (1 + A ^ 2) =
      -PowerSeries.C (ε / 2) * (A - PowerSeries.C ε) ^ 2 := by
    have hehalfε : PowerSeries.C (ε / 2) * PowerSeries.C ε * 2 = (1 : PowerSeries k) := by
      calc _ = (PowerSeries.C (ε / 2) * 2) * PowerSeries.C ε := by ring
        _ = 1 := by rw [hehalf, ← sq, he]
    calc A - PowerSeries.C (ε / 2) * (1 + A ^ 2) =
        A - PowerSeries.C (ε / 2) * (1 + A ^ 2) := rfl
      _ = -PowerSeries.C (ε / 2) * (A - PowerSeries.C ε) ^ 2 := by
        linear_combination -A * hehalfε + PowerSeries.C (ε / 2) * he
  calc A * (1 + A ^ 2)⁻¹ - PowerSeries.C (ε / 2) =
      (A - PowerSeries.C (ε / 2) * (1 + A ^ 2)) * (1 + A ^ 2)⁻¹ := by
        rw [sub_mul, mul_assoc, hinv, mul_one]
    _ = _ := by rw [hcore]

/-- The residue has a formal double zero, including after multiplication by any
local power series (in particular by the units in a confluent divided difference). -/
theorem X_sq_dvd_localResidue_mul (u : ℕ) (ρ ε : k)
    (hρ : ρ ^ u = ε) (hε : ε ^ 2 = 1) (U : PowerSeries k) :
    (PowerSeries.X : PowerSeries k) ^ 2 ∣ localResidue u ρ ε * U := by
  have hd : (PowerSeries.X : PowerSeries k) ∣
      (PowerSeries.C ρ + PowerSeries.X) ^ u - PowerSeries.C ε := by
    rw [PowerSeries.X_dvd_iff]
    simp [hρ]
  obtain ⟨V, hV⟩ := hd
  rw [localResidue_factor u ρ ε hρ hε, hV]
  refine ⟨-PowerSeries.C (ε / 2) * V ^ 2 *
    (1 + (PowerSeries.C ρ + PowerSeries.X) ^ (2 * u))⁻¹ * U, ?_⟩
  ring

end ResidueIdentity

section ConfluentRank
variable {k : Type*} [Field k]

/-- The confluent divided-difference pairing at a cluster of size `m`: the
residue is the coefficient of local degree `m-1`, after the basis powers. -/
noncomputable def confluentResidueMatrix (m : ℕ) (H U : PowerSeries k) :
    Matrix (Fin m) (Fin m) k :=
  fun i j => PowerSeries.coeff (m - 1)
    ((PowerSeries.X : PowerSeries k) ^ (i.val + j.val) * (H * U))

theorem confluentResidueMatrix_entry_zero {m : ℕ} (H U : PowerSeries k)
    (hH : (PowerSeries.X : PowerSeries k) ^ 2 ∣ H)
    (i j : Fin m) (hij : m - 1 < i.val + j.val + 2) :
    confluentResidueMatrix m H U i j = 0 := by
  obtain ⟨V, hV⟩ := hH
  unfold confluentResidueMatrix
  rw [hV]
  have he : (PowerSeries.X : PowerSeries k) ^ (i.val + j.val) *
      (PowerSeries.X ^ 2 * V * U) = PowerSeries.X ^ (i.val + j.val + 2) * (V * U) := by
    rw [pow_add]
    ring
  rw [he, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

/-- A double zero kills the final two rows of the entire confluent residue
pairing, for every cluster size, including the sizes zero, one, and two. -/
theorem rank_confluentResidueMatrix_le (m : ℕ) (H U : PowerSeries k)
    (hH : (PowerSeries.X : PowerSeries k) ^ 2 ∣ H) :
    (confluentResidueMatrix m H U).rank ≤ m - 2 := by
  classical
  by_cases hm : 2 < m
  · let a : Fin m := ⟨m - 2, by omega⟩
    have hh := Matrix.rank_le_card_of_support_subset (confluentResidueMatrix m H U)
      (Iio a) (by
        rw [Function.support_subset_iff']
        intro i hi
        ext j
        apply confluentResidueMatrix_entry_zero H U hH i j
        have hia : ¬i < a := by simpa using hi
        change ¬i.val < m - 2 at hia
        omega)
    simpa [Fin.card_Iio, a] using hh
  · have hz : confluentResidueMatrix m H U = 0 := by
      ext i j
      apply confluentResidueMatrix_entry_zero H U hH i j
      have := i.isLt
      omega
    rw [hz, Matrix.rank_zero]
    omega

/-- The rank saving applies to the paper's concrete residue rational function. -/
theorem rank_localResidue_le [CharZero k] (m u : ℕ) (ρ ε : k)
    (hρ : ρ ^ u = ε) (hε : ε ^ 2 = 1) (U : PowerSeries k) :
    (confluentResidueMatrix m (localResidue u ρ ε) U).rank ≤ m - 2 := by
  apply rank_confluentResidueMatrix_le
  simpa using X_sq_dvd_localResidue_mul u ρ ε hρ hε (1 : PowerSeries k)

end ConfluentRank

section ClusterCount

/-- Removing two rows in each balanced collision class removes exactly `2d`
rows overall, with natural subtraction handling the short-cluster case. -/
theorem sum_cluster_double_zero_cost (K d : ℕ) (hd : 0 < d) :
    (∑ r ∈ range d, (QZeta3.Generic.clusterMultiplicity K d r - 2)) = K - 2 * d := by
  by_cases hlarge : 2 * d ≤ K
  · have hmin (r : ℕ) (hr : r ∈ range d) :
        2 ≤ QZeta3.Generic.clusterMultiplicity K d r := by
      have hq : 2 ≤ K / d := (Nat.le_div_iff_mul_le hd).mpr hlarge
      rcases QZeta3.Generic.clusterMultiplicity_balanced (K := K) hd (mem_range.mp hr) with h | h <;>
        omega
    rw [Finset.sum_tsub_distrib (range d) hmin, QZeta3.Generic.sum_clusterMultiplicity hd]
    simp [mul_comm]
  · have hsmall (r : ℕ) (hr : r ∈ range d) :
        QZeta3.Generic.clusterMultiplicity K d r ≤ 2 := by
      have hq : K / d < 2 := (Nat.div_lt_iff_lt_mul hd).mpr (by omega)
      rcases QZeta3.Generic.clusterMultiplicity_balanced (K := K) hd (mem_range.mp hr) with h | h <;>
        omega
    have hz : (∑ r ∈ range d, (QZeta3.Generic.clusterMultiplicity K d r - 2)) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      exact Nat.sub_eq_zero_of_le (hsmall r hr)
    rw [hz]
    omega

/-- The proper-residue contribution at order `4u` is exactly the claimed
combinatorial upper bound `(K-4u)₊`. -/
theorem sum_fourfold_cluster_double_zero_cost (K u : ℕ) (hu : 0 < u) :
    (∑ r ∈ range (2 * u), (QZeta3.Generic.clusterMultiplicity K (2 * u) r - 2)) =
      K - 4 * u := by
  simpa [← Nat.mul_assoc] using sum_cluster_double_zero_cost K (2 * u) (by omega)

end ClusterCount

section PolynomialResidue
variable {k : Type*} [Field k]

/-- Residue of the polynomial functional, allowing all singular moments rather
than replacing the q-Catalan poles by a single q-zeta moment. -/
noncomputable def residuePolynomialFunctional (r : ℕ → k) (f : Polynomial k) : k :=
  ∑ t ∈ f.support, f.coeff t * r t

noncomputable def quotientResidueMatrix (F : Polynomial k) (K : ℕ) (r : ℕ → k) :
    Matrix (Fin K) (Fin K) k :=
  fun i j => residuePolynomialFunctional r
    ((Polynomial.X ^ (i.val + j.val)) /ₘ F)

/-- Every degree at most `u` belongs to the radical when the first singular
polynomial moment has index `u`. -/
theorem quotientResidueMatrix_row_zero {F : Polynomial k} (hF : F.Monic)
    {K u : ℕ} (hdegree : F.natDegree = K) (r : ℕ → k)
    (hr : ∀ t, t < u → r t = 0) (i : Fin K) (hi : i.val ≤ u) (j : Fin K) :
    quotientResidueMatrix F K r i j = 0 := by
  unfold quotientResidueMatrix residuePolynomialFunctional
  apply Finset.sum_eq_zero
  intro t ht
  by_cases htu : t < u
  · rw [hr t htu, mul_zero]
  · rw [QZeta3.Generic.quotient_moment_monomial_zero hF hdegree (by omega) j.isLt,
      zero_mul]

/-- The complete polynomial residue has rank at most `(K-u-1)₊`, even when
several moments with odd multiples of `u` are singular. -/
theorem rank_quotientResidueMatrix_le {F : Polynomial k} (hF : F.Monic)
    {K u : ℕ} (hdegree : F.natDegree = K) (r : ℕ → k)
    (hr : ∀ t, t < u → r t = 0) :
    (quotientResidueMatrix F K r).rank ≤ K - u - 1 := by
  classical
  by_cases hu : u < K
  · let a : Fin K := ⟨u, hu⟩
    have h := Matrix.rank_le_card_of_support_subset (quotientResidueMatrix F K r)
      (Ioi a) (by
        rw [Function.support_subset_iff']
        intro i hi
        ext j
        apply quotientResidueMatrix_row_zero hF hdegree r hr i _ j
        have hia : ¬a < i := by simpa using hi
        change ¬u < i.val at hia
        omega)
    simp only [Fin.card_Ioi] at h
    dsimp [a] at h
    omega
  · have hz : quotientResidueMatrix F K r = 0 := by
      ext i j
      apply quotientResidueMatrix_row_zero hF hdegree r hr i _ j
      have := i.isLt
      omega
    rw [hz, Matrix.rank_zero]
    omega

/-- The same rank bound in any polynomial basis below degree `K`. -/
theorem rank_quotientResidueMatrix_basis_le {F : Polynomial k} (hF : F.Monic)
    {K u : ℕ} (hdegree : F.natDegree = K) (r : ℕ → k)
    (hr : ∀ t, t < u → r t = 0) (G : Fin K → Polynomial k)
    (hG : ∀ i, (G i).natDegree < K) :
    (Matrix.of fun i j => residuePolynomialFunctional r ((G i * G j) /ₘ F)).rank ≤
      K - u - 1 := by
  classical
  let U : Matrix (Fin K) (Fin K) k := fun i j => (G i).coeff j.val
  let L : Polynomial k →ₗ[k] k :=
    (Polynomial.lsum (fun j => LinearMap.mulRight k (r j))).comp (Polynomial.divByMonicHom F)
  have hexp (i : Fin K) : G i = ∑ j : Fin K, U i j • (Polynomial.X : Polynomial k)^j.val := by
    have h := (G i).as_sum_range_C_mul_X_pow' (hG i)
    rw [← Fin.sum_univ_eq_sum_range _ K] at h
    simpa only [U, Polynomial.smul_eq_C_mul] using h
  have hmono (i j : Fin K) : L ((Polynomial.X : Polynomial k)^(i.val+j.val)) =
      quotientResidueMatrix F K r i j := rfl
  have heq : (Matrix.of fun i j => residuePolynomialFunctional r ((G i*G j) /ₘ F)) =
      U * quotientResidueMatrix F K r * U.transpose := by
    ext i j
    change L (G i * G j) = _
    rw [hexp i, hexp j]
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
      ← pow_add, map_sum, map_smul, smul_eq_mul, hmono]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    apply sum_congr rfl
    intro a ha
    apply sum_congr rfl
    intro b hb
    ring
  rw [heq]
  exact (Matrix.rank_mul_le_left _ _).trans
    ((Matrix.rank_mul_le_right _ _).trans (rank_quotientResidueMatrix_le hF hdegree r hr))

end PolynomialResidue

section RootGeometry
variable {k : Type*} [Field k] [CharZero k]

/-- At a primitive order-`4u` root, the half-order power is minus one. -/
theorem primitive_fourfold_half_power {ω : k} {u : ℕ}
    (hω : IsPrimitiveRoot ω (4 * u)) (hu : 0 < u) : ω ^ (2 * u) = -1 := by
  have hsq : (ω ^ (2 * u)) ^ 2 = 1 := by
    rw [← pow_mul]
    convert hω.pow_eq_one using 1 <;> congr 1 <;> omega
  exact (sq_eq_one_iff.mp hsq).resolve_left
    (hω.pow_ne_one_of_pos_of_lt (by omega) (by omega))

/-- The center and the alternating partial-fraction sign satisfy precisely the
hypothesis needed by the double-zero residue formula. -/
theorem primitive_fourfold_center_sign {ω : k} {u : ℕ}
    (hω : IsPrimitiveRoot ω (4 * u)) (hu : 0 < u) (a : ℕ) :
    (ω ^ (2 * a)) ^ u = (-1 : k) ^ a := by
  calc
    (ω ^ (2 * a)) ^ u = (ω ^ (2 * u)) ^ a := by
      simp only [← pow_mul]
      congr 1
      ring
    _ = (-1 : k) ^ a := by rw [primitive_fourfold_half_power hω hu]

/-- No polynomial moment below index `u` is singular at order `4u`. -/
theorem primitive_fourfold_moment_den_ne_zero {ω : k} {u j : ℕ}
    (hω : IsPrimitiveRoot ω (4 * u)) (hj : j < u) :
    1 + ω ^ (2 * j) ≠ 0 := by
  by_cases hj0 : j = 0
  · simp [hj0]
  intro he
  have hn : ω ^ (2 * j) = -1 := by linear_combination he
  have hp : ω ^ (4 * j) = 1 := by
    have heq : 4 * j = (2 * j) * 2 := by omega
    rw [heq, pow_mul, hn]
    norm_num
  exact hω.pow_ne_one_of_pos_of_lt (by omega) (by omega) hp

end RootGeometry

namespace Generic
section LocalMoments
variable {k : Type*} [Field k] [CharZero k]
open QZeta3.Generic

/-- Actual q-Catalan polynomial moments are regular whenever their explicit
plus-sign denominator is nonzero. -/
theorem mu_mem_regularAt_of_den_ne_zero (ω : k) (j : ℕ)
    (hj : 1 + ω ^ (2 * j) ≠ 0) :
    mu (RatFunc.X : RatFunc k) j ∈ regularAt ω := by
  unfold mu
  rw [div_eq_mul_inv]
  apply (regularAt ω).mul_mem
  · exact (regularAt ω).mul_mem (natCast_mem (regularAt ω) j)
      ((regularAt ω).pow_mem (base_mem_regularAt ω) j)
  · have h := inv_polynomial_mem_regularAt ω (1 + Polynomial.X ^ (2 * j))
      (by simpa using hj)
    simpa only [map_add, map_one, map_pow, RatFunc.algebraMap_X] using h

/-- Every actual q-Catalan polynomial moment has at most a simple pole away from
zero; its denominator is `1+z^(2j)`, rather than the q-zeta denominator. -/
theorem uniformizer_mul_mu_mem (ω : k) (hω : ω ≠ 0) (j : ℕ) :
    uniformizer ω * mu (RatFunc.X : RatFunc k) j ∈ regularAt ω := by
  by_cases hj : j = 0
  · simp [mu, hj]
  by_cases hd : 1 + ω ^ (2 * j) = 0
  · have hder : (Polynomial.derivative (1 + Polynomial.X ^ (2 * j) : Polynomial k)).eval ω ≠ 0 := by
      simp only [Polynomial.derivative_add, Polynomial.derivative_one, zero_add,
        Polynomial.derivative_X_pow, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (pow_ne_zero _ hω)
    have hc := uniformizer_div_mem_of_simple_root ω (1 + Polynomial.X ^ (2 * j))
      (by simpa using hd) hder
    have hc' : uniformizer ω / (1 + (RatFunc.X : RatFunc k) ^ (2 * j)) ∈ regularAt ω := by
      simpa only [map_add, map_one, map_pow, RatFunc.algebraMap_X] using hc
    have hn := (regularAt ω).mul_mem (natCast_mem (regularAt ω) j)
      ((regularAt ω).pow_mem (base_mem_regularAt ω) j)
    convert (regularAt ω).mul_mem hn hc' using 1
    unfold mu
    ring
  · exact (regularAt ω).mul_mem (uniformizer_mem ω) (mu_mem_regularAt_of_den_ne_zero ω j hd)

/-- The first possible singular moment at order `4u` is indeed at index `u`. -/
theorem mu_mem_regularAt_fourfold_below {ω : k} {u j : ℕ}
    (hω : IsPrimitiveRoot ω (4 * u)) (hj : j < u) :
    mu (RatFunc.X : RatFunc k) j ∈ regularAt ω :=
  mu_mem_regularAt_of_den_ne_zero ω j (primitive_fourfold_moment_den_ne_zero hω hj)

/-- Character-zero even indices remove every possible tail singularity at an
even-order root of unity. This holds for the actual finite q-Catalan tails. -/
theorem S_mem_regularAt_even_order (ω : k) (d N : ℕ)
    (hω : IsPrimitiveRoot ω d) (hd : 2 ∣ d) :
    S (RatFunc.X : RatFunc k) N ∈ regularAt ω := by
  unfold S
  apply (regularAt ω).sum_mem
  intro b hb
  by_cases hb2 : b % 2 = 0
  · simp [QCatalan.chi, hb2]
  · have hbω : ω ^ b ≠ 1 := by
      intro hp
      have hdvd : d ∣ b := (hω.pow_eq_one_iff_dvd b).mp hp
      exact hb2 (Nat.mod_eq_zero_of_dvd (dvd_trans hd hdvd))
    have hden : ((1 - (RatFunc.X : RatFunc k) ^ b) ^ 2)⁻¹ ∈ regularAt ω := by
      have hp := inv_polynomial_mem_regularAt ω ((1 - Polynomial.X ^ b) ^ 2)
        (by simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_one,
          Polynomial.eval_X]; exact pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hbω)))
      simpa only [map_pow, map_sub, map_one, RatFunc.algebraMap_X] using hp
    apply (regularAt ω).mul_mem (intCast_mem (regularAt ω) (QCatalan.chi b))
    unfold g2
    rw [div_eq_mul_inv]
    exact (regularAt ω).mul_mem ((regularAt ω).pow_mem (base_mem_regularAt ω) b) hden

/-- A uniform two-pole bound for every finite character tail. -/
theorem uniformizer_sq_mul_S_mem (ω : k) (hω : ω ≠ 0) (N : ℕ) :
    uniformizer ω ^ 2 * S (RatFunc.X : RatFunc k) N ∈ regularAt ω := by
  unfold S
  rw [Finset.mul_sum]
  apply (regularAt ω).sum_mem
  intro b hb
  have h := (regularAt ω).mul_mem
    ((regularAt ω).mul_mem (intCast_mem (regularAt ω) (QCatalan.chi b))
      ((regularAt ω).pow_mem (base_mem_regularAt ω) b))
    ((regularAt ω).pow_mem
      (uniformizer_div_geometric_mem ω hω b (Finset.mem_Icc.mp hb).1) 2)
  convert h using 1
  unfold g2
  rw [div_pow]
  have he : (1 - (RatFunc.X : RatFunc k) ^ b) ^ 2 = (RatFunc.X ^ b - 1) ^ 2 := by ring
  rw [he]
  ring

/-- At odd orders there are no singular polynomial moments. -/
theorem mu_mem_regularAt_odd_order (ω : k) (d j : ℕ)
    (hω : IsPrimitiveRoot ω d) (hd : Odd d) :
    mu (RatFunc.X : RatFunc k) j ∈ regularAt ω := by
  apply mu_mem_regularAt_of_den_ne_zero
  intro he
  have hn : ω ^ (2 * j) = -1 := by linear_combination he
  have hp : (ω ^ (2 * j)) ^ d = 1 := by
    rw [← pow_mul, Nat.mul_comm (2 * j) d, pow_mul, hω.pow_eq_one, one_pow]
  rw [hn, hd.neg_one_pow] at hp
  norm_num at hp

/-- Orders twice an odd number also have no singular polynomial moments. -/
theorem mu_mem_regularAt_twice_odd_order (ω : k) (h j : ℕ)
    (hω : IsPrimitiveRoot ω (2 * h)) (hh : Odd h) :
    mu (RatFunc.X : RatFunc k) j ∈ regularAt ω := by
  apply mu_mem_regularAt_of_den_ne_zero
  intro he
  have hn : ω ^ (2 * j) = -1 := by linear_combination he
  have hp : (ω ^ (2 * j)) ^ h = 1 := by
    calc
      (ω ^ (2 * j)) ^ h = (ω ^ (2 * h)) ^ j := by
        simp only [← pow_mul]
        congr 1
        ring
      _ = 1 := by rw [hω.pow_eq_one, one_pow]
  rw [hn, hh.neg_one_pow] at hp
  norm_num at hp

/-- Split the complete polynomial quotient contribution into a regular part and
one simple-pole matrix.  All singular moments are retained, and the pole matrix
has the low-degree radical needed for the q-Catalan rank bound. -/
theorem quotient_matrix_split_fourfold
    (ω : k) (hω0 : ω ≠ 0) (u K : ℕ) (hω : IsPrimitiveRoot ω (4 * u))
    (G : Fin K → Polynomial (RatFunc k)) (hGdegree : ∀ i, (G i).natDegree < K)
    (hGcoeff : ∀ i j, (G i).coeff j ∈ regularAt ω) (r c : Fin K → ℕ) :
    ∃ A B : Matrix (Fin K) (Fin K) (RatFunc k),
      (∀ i j, A i j ∈ regularAt ω) ∧ (∀ i j, B i j ∈ regularAt ω) ∧
      B.rank ≤ K - u - 1 ∧
      ∀ i j, uniformizer ω ^ (r i + c j) *
          Lpoly RatFunc.X ((G i * G j) /ₘ F RatFunc.X K) =
        A i j + (uniformizer ω)⁻¹ * B i j := by
  classical
  let H : Fin K → Fin K → Polynomial (RatFunc k) := fun i j => (G i * G j) /ₘ F RatFunc.X K
  let lo : ℕ → RatFunc k := fun t => if t < u then mu RatFunc.X t else 0
  let hi : ℕ → RatFunc k := fun t => if t < u then 0 else uniformizer ω * mu RatFunc.X t
  let M : Matrix (Fin K) (Fin K) (RatFunc k) :=
    fun i j => residuePolynomialFunctional hi (H i j)
  let A : Matrix (Fin K) (Fin K) (RatFunc k) := fun i j =>
    uniformizer ω ^ (r i + c j) * residuePolynomialFunctional lo (H i j)
  let B : Matrix (Fin K) (Fin K) (RatFunc k) := fun i j =>
    uniformizer ω ^ (r i + c j) * M i j
  have hHcoeff (i j : Fin K) (t : ℕ) : (H i j).coeff t ∈ regularAt ω := by
    apply quotient_coeff_mem_subring (regularAt ω) RatFunc.X (base_mem_regularAt ω) K
    apply (coeff_mem_iff_lifts (regularAt ω) (G i * G j)).mpr
    exact (Polynomial.liftsRing (regularAt ω).subtype).mul_mem
      ((coeff_mem_iff_lifts _ _).mp (hGcoeff i)) ((coeff_mem_iff_lifts _ _).mp (hGcoeff j))
  have hlo (t : ℕ) : lo t ∈ regularAt ω := by
    dsimp [lo]
    split_ifs with ht
    · exact mu_mem_regularAt_fourfold_below hω ht
    · exact (regularAt ω).zero_mem
  have hhi (t : ℕ) : hi t ∈ regularAt ω := by
    dsimp [hi]
    split_ifs with ht
    · exact (regularAt ω).zero_mem
    · exact uniformizer_mul_mu_mem ω hω0 t
  have hfun (f : Polynomial (RatFunc k)) (hf : ∀ t, f.coeff t ∈ regularAt ω)
      (v : ℕ → RatFunc k) (hv : ∀ t, v t ∈ regularAt ω) :
      residuePolynomialFunctional v f ∈ regularAt ω := by
    unfold residuePolynomialFunctional
    exact (regularAt ω).sum_mem (fun t ht => (regularAt ω).mul_mem (hf t) (hv t))
  have hA (i j : Fin K) : A i j ∈ regularAt ω :=
    (regularAt ω).mul_mem ((regularAt ω).pow_mem (uniformizer_mem ω) _)
      (hfun (H i j) (hHcoeff i j) lo hlo)
  have hB (i j : Fin K) : B i j ∈ regularAt ω :=
    (regularAt ω).mul_mem ((regularAt ω).pow_mem (uniformizer_mem ω) _)
      (hfun (H i j) (hHcoeff i j) hi hhi)
  have hMrank : M.rank ≤ K - u - 1 :=
    rank_quotientResidueMatrix_basis_le (F_monic _ K) (F_natDegree _ K) hi
      (by intro t ht; simp [hi, ht]) G hGdegree
  have hBrank : B.rank ≤ K - u - 1 := by
    have heq : B = Matrix.diagonal (fun i => uniformizer ω ^ r i) * M *
        Matrix.diagonal (fun j => uniformizer ω ^ c j) := by
      ext i j
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      dsimp [B]
      rw [pow_add]
      ring
    rw [heq]
    exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans hMrank)
  refine ⟨A, B, hA, hB, hBrank, ?_⟩
  intro i j
  have hsplit : Lpoly RatFunc.X (H i j) =
      residuePolynomialFunctional lo (H i j) +
        (uniformizer ω)⁻¹ * residuePolynomialFunctional hi (H i j) := by
    unfold Lpoly residuePolynomialFunctional
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    dsimp [lo, hi]
    split_ifs with htu
    · ring
    · have hu0 := uniformizer_ne_zero ω
      field_simp
      ring
  change uniformizer ω ^ (r i + c j) * Lpoly RatFunc.X (H i j) = _
  rw [hsplit]
  dsimp [A, B, M]
  ring

noncomputable def unnormalizedGram (z : k) (K : ℕ) (G : Fin K → Polynomial k) :
    Matrix (Fin K) (Fin K) (Polynomial k) :=
  Matrix.of fun i j => momentPolynomial z K (G i * G j)

/-- Any entrywise clearing of the proper part combines with the complete
polynomial-moment rank bound at order `4u`. -/
theorem fourfold_gram_det_mem {ω : k} {K u : ℕ}
    (hω : IsPrimitiveRoot ω (4 * u)) (hω0 : ω ≠ 0)
    (G : Fin K → Polynomial (RatFunc k))
    (hGdegree : ∀ i, (G i).natDegree < K)
    (hGcoeff : ∀ i j, (G i).coeff j ∈ regularAt ω)
    (r c : Fin K → ℕ)
    (hproper : ∀ i j, Polynomial.C (uniformizer ω ^ (r i + c j)) *
      (∑ a ∈ Icc 1 K, Polynomial.C ((G i * G j).eval (RatFunc.X ^ (2 * a)) * (-1) ^ a /
        (RatFunc.X ^ (2 * a) * (Polynomial.derivative (F (RatFunc.X : RatFunc k) K)).eval
          (RatFunc.X ^ (2 * a)))) *
        (Polynomial.X - Polynomial.C (S (RatFunc.X : RatFunc k) (2 * a)))) ∈
          Polynomial.liftsRing (regularAt ω).subtype) :
    Polynomial.C (uniformizer ω) ^ ((∑ i, r i) + (∑ i, c i) + (K - u - 1)) *
      (unnormalizedGram RatFunc.X K G).det ∈ Polynomial.liftsRing (regularAt ω).subtype := by
  classical
  let T := Polynomial.liftsRing (regularAt ω).subtype
  obtain ⟨A, B, hA, hB, hBrank, hAB⟩ :=
    quotient_matrix_split_fourfold ω hω0 u K hω G hGdegree hGcoeff r c
  let P : Matrix (Fin K) (Fin K) (Polynomial (RatFunc k)) := fun i j =>
    Polynomial.C (uniformizer ω ^ (r i + c j)) *
      (∑ a ∈ Icc 1 K, Polynomial.C ((G i * G j).eval (RatFunc.X ^ (2 * a)) * (-1) ^ a /
        (RatFunc.X ^ (2 * a) * (Polynomial.derivative (F (RatFunc.X : RatFunc k) K)).eval
          (RatFunc.X ^ (2 * a)))) *
        (Polynomial.X - Polynomial.C (S (RatFunc.X : RatFunc k) (2 * a))))
  let A' : Matrix (Fin K) (Fin K) (Polynomial (RatFunc k)) := A.map Polynomial.C - P
  have hA' (i j : Fin K) : A' i j ∈ T :=
    T.sub_mem (C_mem_lifts_regularAt ω _ (hA i j)) (hproper i j)
  have hB' (i j : Fin K) : Polynomial.C (B i j) ∈ T := C_mem_lifts_regularAt ω _ (hB i j)
  have hmem := QZeta3.C_pow_mul_det_add_inv_mem_subring T (uniformizer ω)
    (uniformizer_ne_zero ω) (C_mem_lifts_regularAt ω _ (uniformizer_mem ω))
    A' B hA' hB' (K-u-1) hBrank
  have heq : A' + Polynomial.C ((uniformizer ω)⁻¹) • B.map Polynomial.C =
      Matrix.of fun i j => Polynomial.C (uniformizer ω) ^ (r i + c j) *
        unnormalizedGram RatFunc.X K G i j := by
    apply Matrix.ext
    intro i j
    change Polynomial.C (A i j) - P i j +
      Polynomial.C ((uniformizer ω)⁻¹) * Polynomial.C (B i j) = _
    simp only [P, unnormalizedGram, Matrix.of_apply, momentPolynomial,
      ← map_pow, mul_sub, ← map_mul]
    rw [hAB i j, map_add, map_mul]
    ring
  rw [heq, det_weighted_eq] at hmem
  simpa only [← mul_assoc, ← pow_add, Nat.add_comm (K-u-1)] using hmem

/-- Local Gram regularity descends to the concrete q-Catalan determinant through
any locally invertible polynomial basis change. -/
theorem Delta_scaled_coeff_mem_of_gram (ω : k) (K e : ℕ)
    (G : Fin K → Polynomial (RatFunc k)) (hG : ∀ i, (G i).natDegree < K)
    (hU0 : (polynomialChange K G).det ≠ 0)
    (hUinv : (polynomialChange K G).det⁻¹ ∈ regularAt ω)
    (hdet : Polynomial.C (uniformizer ω)^e * (unnormalizedGram RatFunc.X K G).det ∈
      Polynomial.liftsRing (regularAt ω).subtype) (i : ℕ) :
    uniformizer ω^e * (Delta (RatFunc.X : RatFunc k) K).coeff i ∈ regularAt ω := by
  let T := Polynomial.liftsRing (regularAt ω).subtype
  have hnrm0 : nrm (RatFunc.X : RatFunc k) K ∈ regularAt ω := by
    unfold nrm
    exact (regularAt ω).mul_mem ((regularAt ω).pow_mem ((regularAt ω).neg_mem (regularAt ω).one_mem) _)
      ((regularAt ω).pow_mem (base_mem_regularAt ω) _)
  have hnrm := C_mem_lifts_regularAt ω (nrm (RatFunc.X : RatFunc k) K) hnrm0
  have hinv := C_mem_lifts_regularAt ω ((polynomialChange K G).det⁻¹) hUinv
  have hmem := T.mul_mem (T.pow_mem hinv 2) (T.mul_mem (T.pow_mem hnrm K) hdet)
  have hnorm : (normalizedGram (RatFunc.X : RatFunc k) K G).det =
      Polynomial.C (nrm (RatFunc.X : RatFunc k) K)^K *
        (unnormalizedGram RatFunc.X K G).det := by
    have hmatrix : normalizedGram (RatFunc.X : RatFunc k) K G =
        Polynomial.C (nrm (RatFunc.X : RatFunc k) K) • unnormalizedGram RatFunc.X K G := by
      ext a b
      rfl
    rw [hmatrix, Matrix.det_smul, Fintype.card_fin]
  have hidentity : Polynomial.C ((polynomialChange K G).det⁻¹)^2 *
      (Polynomial.C (nrm (RatFunc.X : RatFunc k) K)^K *
        (Polynomial.C (uniformizer ω)^e * (unnormalizedGram RatFunc.X K G).det)) =
      Polynomial.C (uniformizer ω)^e * Delta (RatFunc.X : RatFunc k) K := by
    calc _ = Polynomial.C (uniformizer ω)^e *
        (Polynomial.C ((polynomialChange K G).det⁻¹)^2 *
          (normalizedGram RatFunc.X K G).det) := by rw [hnorm]; ring
      _ = _ := by
        rw [det_normalizedGram RatFunc.X K G hG]
        have hc : Polynomial.C ((polynomialChange K G).det⁻¹)^2 *
            Polynomial.C ((polynomialChange K G).det)^2 = (1 : Polynomial (RatFunc k)) := by
          rw [← mul_pow, ← map_mul, inv_mul_cancel₀ hU0, map_one, one_pow]
        rw [← mul_assoc (Polynomial.C ((polynomialChange K G).det⁻¹)^2), hc, one_mul]
  rw [hidentity] at hmem
  have hcoeff := (coeff_mem_iff_lifts (regularAt ω) _).mpr hmem i
  simpa only [← map_pow, Polynomial.coeff_C_mul] using hcoeff

end LocalMoments
end Generic

end QCatalan
