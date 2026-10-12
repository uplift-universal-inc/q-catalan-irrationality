import QCatalan.Defs
import QCatalan.ContentAuxRearrangement
import QZeta3.ContentProof

/-!
# Base-prime arithmetic for the q-Catalan determinant

The conservative content estimate can be obtained directly from the individual
residues: all finite character tails are already integral at the base. Thus the
local analytic translation in the manuscript is unnecessary for this bound.
-/

open Polynomial Finset
open QZeta3 (baseIntegral intCast_div_mem_baseIntegral pow_sub_one_coprime)

namespace QCatalan

variable {p : ℕ}

/-- Every denominator `1+p^j`, for positive `j`, is coprime to `p`. -/
theorem pow_add_one_coprime (p j : ℕ) (hj : 0 < j) :
    Nat.Coprime (1 + p ^ j) p := by
  have h : Nat.Coprime (1 + p ^ j) (p ^ j) := by simp
  exact h.coprime_dvd_right (dvd_pow_self p (Nat.ne_zero_of_lt hj))

/-- The actual signed Euler moments are integral at all base primes. -/
theorem mu_mem_baseIntegral (p j : ℕ) : mu p j ∈ baseIntegral p := by
  by_cases hj : j = 0
  · simp [mu, hj]
  · have h := intCast_div_mem_baseIntegral ((j : ℤ) * (p : ℤ) ^ j)
      ((1 + p ^ (2 * j) : ℕ) : ℤ)
      (by exact_mod_cast pow_add_one_coprime p (2*j) (by omega))
    simpa [mu] using h

/-- The finite pole-tail terms need no local limiting argument. -/
theorem g2_pow_mem_baseIntegral (hp : 1 ≤ p) (b : ℕ) (hb : 0 < b) :
    g2 ((p : ℚ) ^ b) ∈ baseIntegral p := by
  have hpow : 1 ≤ p ^ b := one_le_pow₀ hp
  have h := intCast_div_mem_baseIntegral ((p : ℤ) ^ b)
    (((p ^ b - 1 : ℕ) : ℤ) ^ 2)
    (by simpa using (pow_sub_one_coprime p b hp hb).pow_left 2)
  convert h using 1
  push_cast [Nat.cast_sub hpow]
  unfold g2
  congr 1
  ring

theorem S_mem_baseIntegral (hp : 1 ≤ p) (a : ℕ) : S p a ∈ baseIntegral p := by
  unfold S
  apply (baseIntegral p).sum_mem
  intro b hb
  exact (baseIntegral p).mul_mem (intCast_mem (baseIntegral p) (chi b))
    (g2_pow_mem_baseIntegral hp b (mem_Icc.mp hb).1)

/-- The polynomial functional preserves coefficientwise base integrality. -/
theorem Lpoly_mem_baseIntegral (p : ℕ) (f : ℚ[X])
    (hf : ∀ i, f.coeff i ∈ baseIntegral p) : Lpoly p f ∈ baseIntegral p := by
  unfold Lpoly
  exact (baseIntegral p).sum_mem fun i _ =>
    (baseIntegral p).mul_mem (hf i) (mu_mem_baseIntegral p i)

noncomputable def integralF (p K : ℕ) : (baseIntegral p)[X] :=
  ∏ a ∈ Icc 1 K, (X - C (⟨(p : ℚ) ^ (2*a),
    (baseIntegral p).pow_mem (natCast_mem (baseIntegral p) p) (2*a)⟩ : baseIntegral p))

theorem integralF_monic (p K : ℕ) : (integralF p K).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _

theorem integralF_map (p K : ℕ) :
    (integralF p K).map (baseIntegral p).subtype = F p K := by
  simp [integralF, F, Polynomial.map_prod]

/-- Monic polynomial division introduces no base-prime denominators. -/
theorem quotient_coeff_mem_baseIntegral (p K k i : ℕ) :
    (X ^ k /ₘ F p K).coeff i ∈ baseIntegral p := by
  let f : (baseIntegral p)[X] := X ^ k /ₘ integralF p K
  have hmap : f.map (baseIntegral p).subtype = X ^ k /ₘ F p K := by
    rw [Polynomial.map_divByMonic _ (integralF_monic p K), integralF_map]
    simp
  rw [← hmap, Polynomial.coeff_map]
  exact (f.coeff i).property

theorem quotient_moment_mem_baseIntegral (p K k : ℕ) :
    Lpoly p (X ^ k /ₘ F p K) ∈ baseIntegral p :=
  Lpoly_mem_baseIntegral p _ (quotient_coeff_mem_baseIntegral p K k)

/-- A sharp base-power denominator for a difference of distinct powers. -/
theorem pow_min_div_difference_mem (hp : 2 ≤ p) (a b : ℕ) (hab : a ≠ b) :
    (p : ℚ) ^ min a b / ((p : ℚ) ^ a - (p : ℚ) ^ b) ∈ baseIntegral p := by
  wlog hlt : a < b generalizing a b
  · have hba : b < a := by omega
    have h := (baseIntegral p).neg_mem (this b a hab.symm hba)
    simpa only [min_comm, ← neg_sub ((p : ℚ)^b), div_neg] using h
  rw [min_eq_left (Nat.le_of_lt hlt)]
  have hpow : 1 ≤ p ^ (b-a) := one_le_pow₀ (show 1 ≤ p by omega)
  have h := intCast_div_mem_baseIntegral (-1) ((p^(b-a)-1 : ℕ) : ℤ)
    (by simpa using pow_sub_one_coprime p (b-a) (by omega) (by omega))
  convert h using 1
  push_cast [Nat.cast_sub hpow]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have he : (p : ℚ)^b = (p : ℚ)^a * (p : ℚ)^(b-a) := by
    rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hlt)]
  rw [he]
  field_simp
  rw [show (1 - (p : ℚ) ^ (b-a)) = -(-1 + (p : ℚ) ^ (b-a)) by ring, div_neg]
  congr 2
  ring

/-- Exact sum of the derivative's base-prime exponents. -/
theorem sum_min_Icc (K a : ℕ) (ha : a ≤ K) :
    2 * (∑ b ∈ Icc 1 K, min a b) + a*a = 2*a*K+a := by
  induction K with
  | zero => simp_all
  | succ K ih =>
    by_cases hak : a ≤ K
    · rw [sum_Icc_succ_top (by omega), min_eq_left (by omega)]
      have h := ih hak
      nlinarith
    · have he : a = K+1 := by omega
      subst a
      have hs : (∑ b ∈ Icc 1 (K+1), min (K+1) b) = ∑ b ∈ Icc 1 (K+1), b := by
        apply sum_congr rfl
        intro b hb
        exact min_eq_right (mem_Icc.mp hb).2
      rw [hs]
      have h := QZeta3.sum_Icc_id_mul_two (K+1)
      nlinarith

/-- Base exponent in the derivative at the `a`th geometric node. -/
def derivativeExponent (K a : ℕ) : ℕ :=
  ∑ b ∈ (Icc 1 K).erase a, 2 * min a b

theorem derivativeExponent_eq (K a : ℕ) (ha : a ∈ Icc 1 K) :
    derivativeExponent K a + a*a + a = 2*a*K := by
  have hsum := sum_min_Icc K a (mem_Icc.mp ha).2
  have herase := sum_erase_add (Icc 1 K) (fun b => min a b) ha
  simp only [min_self] at herase
  unfold derivativeExponent
  rw [← mul_sum]
  nlinarith

theorem derivative_F_eval_eq_prod (p K a : ℕ) (ha : a ∈ Icc 1 K) :
    (derivative (F p K)).eval ((p : ℚ) ^ (2*a)) =
      ∏ b ∈ (Icc 1 K).erase a, ((p : ℚ) ^ (2*a) - (p : ℚ) ^ (2*b)) := by
  change (derivative (Lagrange.nodal (Icc 1 K) (fun b => (p : ℚ) ^ (2*b)))).eval
    ((p : ℚ) ^ (2*a)) = _
  rw [Lagrange.eval_nodal_derivative_eval_node_eq (v := fun b => (p : ℚ) ^ (2*b)) ha, Lagrange.eval_nodal]

theorem derivative_scaled_inv_mem (hp : 2 ≤ p) (K a : ℕ) (ha : a ∈ Icc 1 K) :
    (p : ℚ) ^ derivativeExponent K a /
      (derivative (F p K)).eval ((p : ℚ) ^ (2*a)) ∈ baseIntegral p := by
  have hprod : (∏ b ∈ (Icc 1 K).erase a,
      (p : ℚ) ^ (2 * min a b) / ((p : ℚ) ^ (2*a) - (p : ℚ) ^ (2*b))) ∈
      baseIntegral p := by
    apply (baseIntegral p).prod_mem
    intro b hb
    have hne : 2*a ≠ 2*b := by have := (mem_erase.mp hb).1; omega
    simpa only [← Nat.mul_min_mul_left] using pow_min_div_difference_mem hp (2*a) (2*b) hne
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum,
    ← derivative_F_eval_eq_prod p K a ha] at hprod
  exact hprod

/-- The loss in the moment of total index `k`. -/
def momentLoss (K k : ℕ) : ℕ := (K-k)*(K-k+1)

theorem momentLoss_bounds_residue (K k a : ℕ) (ha : a ∈ Icc 1 K) :
    derivativeExponent K a + 2*a ≤ momentLoss K k + 2*a*k := by
  have he := derivativeExponent_eq K a ha
  have ha0 := (mem_Icc.mp ha).1
  unfold momentLoss
  by_cases hk : k ≤ K
  · have hsub : K-k+k = K := Nat.sub_add_cancel hk
    by_cases hle : a ≤ K-k
    · have hmul : (K-k-a)*(K-k-a+1) ≥ 0 := Nat.zero_le _
      have hsuba : K-k-a+a = K-k := Nat.sub_add_cancel hle
      nlinarith
    · have hmul : (a-(K-k)-1)*(a-(K-k)) ≥ 0 := Nat.zero_le _
      have hsuba : a-(K-k)+(K-k)=a := Nat.sub_add_cancel (by omega)
      have hsuba2 : a-(K-k)-1+1 = a-(K-k) := by omega
      nlinarith
  · have hsub : K-k=0 := by omega
    rw [hsub]
    nlinarith


/-- Each residue already has the conservative quadratic denominator bound. -/
theorem scaled_residue_mem (hp : 2 ≤ p) (K k a : ℕ) (ha : a ∈ Icc 1 K) :
    (p : ℚ) ^ momentLoss K k * (res p K k a / (p : ℚ) ^ (2*a)) ∈
      baseIntegral p := by
  have hle := momentLoss_bounds_residue K k a ha
  have he : momentLoss K k + 2*a*k =
      derivativeExponent K a + 2*a +
        (momentLoss K k + 2*a*k - (derivativeExponent K a + 2*a)) := by omega
  have hint := (baseIntegral p).mul_mem (derivative_scaled_inv_mem hp K a ha)
    ((baseIntegral p).pow_mem (natCast_mem (baseIntegral p) p)
      (momentLoss K k + 2*a*k - (derivativeExponent K a + 2*a)))
  convert hint using 1
  unfold res
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  calc
    _ = ((p : ℚ)^momentLoss K k * (p : ℚ)^(2*a*k)) /
        ((derivative (F p K)).eval ((p : ℚ)^(2*a)) * (p : ℚ)^(2*a)) := by ring
    _ = _ := by
      rw [← pow_add, he, pow_add, pow_add]
      field_simp
      simp

/-- Both coefficients of a normalized affine moment satisfy the same bound. -/
theorem scaled_mLin_mem (hp : 2 ≤ p) (K k : ℕ) :
    (p : ℚ) ^ momentLoss K k * mLin p K k ∈ baseIntegral p := by
  unfold mLin
  rw [mul_neg, Finset.mul_sum]
  apply (baseIntegral p).neg_mem
  apply (baseIntegral p).sum_mem
  intro a ha
  have h := (baseIntegral p).mul_mem (scaled_residue_mem hp K k a ha)
    ((baseIntegral p).pow_mem ((baseIntegral p).neg_mem (baseIntegral p).one_mem) a)
  convert h using 1
  ring

theorem scaled_mConst_mem (hp : 2 ≤ p) (K k : ℕ) :
    (p : ℚ) ^ momentLoss K k * mConst p K k ∈ baseIntegral p := by
  unfold mConst
  rw [mul_add, Finset.mul_sum]
  apply (baseIntegral p).add_mem
  · exact (baseIntegral p).mul_mem
      ((baseIntegral p).pow_mem (natCast_mem (baseIntegral p) p) _)
      (quotient_moment_mem_baseIntegral p K k)
  · apply (baseIntegral p).sum_mem
    intro a ha
    have h := (baseIntegral p).mul_mem
      ((baseIntegral p).mul_mem (scaled_residue_mem hp K k a ha)
        ((baseIntegral p).pow_mem ((baseIntegral p).neg_mem (baseIntegral p).one_mem) a))
      (S_mem_baseIntegral (by omega) (2*a))
    convert h using 1
    ring

/-- Unscaled affine moments, viewed as polynomials in the target variable. -/
noncomputable def momentMatrix (p K : ℕ) : Matrix (Fin K) (Fin K) ℚ[X] :=
  fun i j => C (mConst p K (i.val+j.val)) + C (mLin p K (i.val+j.val)) * X

theorem scaled_momentMatrix_mem (hp : 2 ≤ p) (K : ℕ) (i j : Fin K) :
    C ((p : ℚ) ^ momentLoss K (i.val+j.val)) * momentMatrix p K i j ∈
      Polynomial.liftsRing (baseIntegral p).subtype := by
  apply (QZeta3.coeff_mem_baseIntegral_iff p _).mp
  intro n
  have he : C ((p : ℚ) ^ momentLoss K (i.val+j.val)) * momentMatrix p K i j =
      C ((p : ℚ) ^ momentLoss K (i.val+j.val) * mConst p K (i.val+j.val)) +
      C ((p : ℚ) ^ momentLoss K (i.val+j.val) * mLin p K (i.val+j.val)) * X := by
    simp only [momentMatrix, map_mul]
    ring
  rw [he, Polynomial.coeff_add, Polynomial.coeff_C_mul]
  apply (baseIntegral p).add_mem
  · simp only [Polynomial.coeff_C]
    split_ifs
    · exact scaled_mConst_mem hp K _
    · exact (baseIntegral p).zero_mem
  · apply (baseIntegral p).mul_mem (scaled_mLin_mem hp K _)
    simp only [Polynomial.coeff_X]
    split_ifs <;> simp

/-- Total loss on the main diagonal, which bounds the loss of every permutation. -/
def totalLoss (K : ℕ) : ℕ := ∑ i ∈ range K, momentLoss K (2*i)

theorem totalLoss_eq_sum_fin (K : ℕ) :
    totalLoss K = ∑ i : Fin K, momentLoss K (2*i.val) := by
  exact (Fin.sum_univ_eq_sum_range _ _).symm

theorem permutation_loss_le (K : ℕ) (σ : Equiv.Perm (Fin K)) :
    (∑ i : Fin K, momentLoss K ((σ i).val+i.val)) ≤ totalLoss K := by
  rw [totalLoss_eq_sum_fin]
  simpa only [momentLoss, Nat.add_comm] using sum_weight_perm_le_diag K σ

/-- The normalized determinant is coefficientwise integral at the base. -/
theorem scaled_det_mem (hp : 2 ≤ p) (K : ℕ) :
    C ((p : ℚ) ^ totalLoss K) * (momentMatrix p K).det ∈
      Polynomial.liftsRing (baseIntegral p).subtype := by
  let R := Polynomial.liftsRing (baseIntegral p).subtype
  have hC (n : ℕ) : C ((p : ℚ)^n) ∈ R := by
    apply (QZeta3.coeff_mem_baseIntegral_iff p _).mp
    intro i
    simp only [Polynomial.coeff_C]
    split_ifs
    · exact (baseIntegral p).pow_mem (natCast_mem (baseIntegral p) p) n
    · exact (baseIntegral p).zero_mem
  rw [Matrix.det_apply', Finset.mul_sum]
  apply R.sum_mem
  intro σ _
  let s : ℕ := ∑ i : Fin K, momentLoss K ((σ i).val+i.val)
  have hle : s ≤ totalLoss K := permutation_loss_le K σ
  have hprod : (∏ i : Fin K,
      C ((p : ℚ) ^ momentLoss K ((σ i).val+i.val)) * momentMatrix p K (σ i) i) ∈ R :=
    R.prod_mem fun i _ => scaled_momentMatrix_mem hp K (σ i) i
  rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum] at hprod
  have h := R.mul_mem (R.mul_mem (hC (totalLoss K-s)) hprod)
    (intCast_mem R (Equiv.Perm.sign σ))
  have hc : C ((p : ℚ)^(totalLoss K-s)) * C ((p : ℚ)^s) =
      C ((p : ℚ)^totalLoss K) := by
    rw [← map_mul, ← pow_add, Nat.sub_add_cancel hle]
  convert h using 1
  rw [← hc]
  dsimp [s]
  ring

theorem totalLoss_le (K : ℕ) : totalLoss K ≤ K^2*(K+1) := by
  have h : totalLoss K ≤ ∑ _i ∈ range K, K*(K+1) := by
    apply sum_le_sum
    intro i _
    unfold momentLoss
    exact Nat.mul_le_mul (Nat.sub_le _ _) (Nat.add_le_add_right (Nat.sub_le _ _) 1)
  simpa only [sum_const, card_range, smul_eq_mul, pow_two, mul_assoc] using h

theorem cK_add_totalLoss (K : ℕ) : cK K + totalLoss K = K^2*(K+1) := by
  exact Nat.sub_add_cancel (totalLoss_le K)

theorem Delta_eq_momentMatrix_det (p K : ℕ) :
    Delta p K = C ((nrm p K)^K) * (momentMatrix p K).det := by
  have hM : (X : ℚ[X]) • (hankelLin p K).map C + (hankelConst p K).map C =
      C (nrm p K) • momentMatrix p K := by
    apply Matrix.ext
    intro i j
    change X * C (nrm p K * mLin p K (i.val+j.val)) +
      C (nrm p K * mConst p K (i.val+j.val)) =
      C (nrm p K) * (C (mConst p K (i.val+j.val)) +
        C (mLin p K (i.val+j.val)) * X)
    simp only [map_mul]
    ring
  unfold Delta
  rw [hM, Matrix.det_smul, Fintype.card_fin, ← map_pow]

/-- Proposition 3.1: the exact conservative coefficient-content bound for every
integer base, including composite bases. -/
theorem content_coeff (hp : 2 ≤ p) (K i : ℕ) :
    Nat.Coprime ((Delta p K).coeff i / (p : ℚ)^cK K).den p := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hnorm : (nrm p K)^K / (p : ℚ)^cK K =
      (-1 : ℚ)^(K*K) * (p : ℚ)^totalLoss K := by
    unfold nrm
    rw [mul_pow, ← pow_mul, ← pow_mul,
      show K*(K+1)*K = K^2*(K+1) by ring, ← cK_add_totalLoss K, pow_add]
    field_simp
  have hcoeff := (QZeta3.coeff_mem_baseIntegral_iff p _).mpr (scaled_det_mem hp K) i
  have h := (baseIntegral p).mul_mem
    ((baseIntegral p).pow_mem ((baseIntegral p).neg_mem (baseIntegral p).one_mem) (K*K)) hcoeff
  change _ ∈ baseIntegral p
  convert h using 1
  rw [Delta_eq_momentMatrix_det, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
    mul_div_right_comm, hnorm]
  ring

end QCatalan
