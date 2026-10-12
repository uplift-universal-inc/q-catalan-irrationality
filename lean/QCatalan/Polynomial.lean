import QCatalan.Defs
import QZeta3.Leading

/-! # Exact determinant polynomial and normalization for q-Catalan

The additional alternating residue signs and the doubled node exponents are
retained in the Vandermonde factorization.  No q-zeta moment or arithmetic theorem
is used in this calculation.
-/

open Polynomial Finset Matrix

namespace QCatalan

variable {p : ℕ}

theorem natDegree_Delta_le (p K : ℕ) : (Delta p K).natDegree ≤ K := by
  unfold Delta
  simpa [Fintype.card_fin] using
    Polynomial.natDegree_det_X_add_C_le (hankelLin p K) (hankelConst p K)

theorem natDegree_PK_le (p K : ℕ) : (PK p K).natDegree ≤ K :=
  (Polynomial.natDegree_mul_C_le _ _).trans (natDegree_Delta_le p K)

theorem aeval_PK (p K : ℕ) (x : ℝ) :
    aeval x (PK p K) = DeltaR p K x * ((CK p K : ℝ) / (p : ℝ) ^ cK K) := by
  unfold PK DeltaR
  rw [aeval_mul, aeval_C, eq_ratCast]
  congr 1
  norm_cast

theorem coeff_Delta_top_eq_det (p K : ℕ) :
    (Delta p K).coeff K = (hankelLin p K).det := by
  simpa [Delta] using Polynomial.coeff_det_X_add_C_card (hankelLin p K) (hankelConst p K)

def nodes (p K : ℕ) (i : Fin K) : ℚ := (p : ℚ) ^ (2 * (i.val + 1))

theorem F_eq_nodal (p K : ℕ) :
    F p K = Lagrange.nodal univ (nodes p K) := by
  simpa [F, Lagrange.nodal, nodes] using
    QZeta3.prod_Icc_eq_fin K (fun a => X - C ((p : ℚ) ^ (2 * a)))

noncomputable def linWeight (p K : ℕ) (i : Fin K) : ℚ :=
  -nrm p K * (-1) ^ (i.val + 1) /
    (nodes p K i * (derivative (F p K)).eval (nodes p K i))

theorem hankelLin_factor (p K : ℕ) :
    hankelLin p K = (Matrix.vandermonde (nodes p K))ᵀ *
      Matrix.diagonal (linWeight p K) * Matrix.vandermonde (nodes p K) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  simp only [hankelLin, Matrix.of_apply, mLin, QZeta3.sum_Icc_eq_fin, mul_neg,
    Finset.mul_sum, ← Finset.sum_neg_distrib, Matrix.transpose_apply,
    Matrix.vandermonde_apply]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [res, linWeight, nodes, pow_mul, pow_add, div_eq_mul_inv, _root_.mul_inv_rev]
  ring

theorem nodes_injective (hp : 2 ≤ p) (K : ℕ) : Function.Injective (nodes p K) := by
  intro i j hij
  have hp1 : (1 : ℚ) < p := by exact_mod_cast (show 1 < p by omega)
  have hpow := (pow_right_strictMono₀ hp1).injective hij
  exact Fin.ext (by omega)

theorem derivative_F_node_ne_zero (hp : 2 ≤ p) (K : ℕ) (i : Fin K) :
    (derivative (F p K)).eval (nodes p K i) ≠ 0 := by
  rw [F_eq_nodal]
  have h := Lagrange.nodalWeight_ne_zero (nodes_injective hp K).injOn (mem_univ i)
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal (mem_univ i)] at h
  intro hz
  change (derivative (Lagrange.nodal univ (nodes p K))).eval (nodes p K i) = 0 at hz
  exact h (by rw [hz, _root_.inv_zero])

theorem linWeight_ne_zero (hp : 2 ≤ p) (K : ℕ) (i : Fin K) : linWeight p K i ≠ 0 := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  apply div_ne_zero
  · exact mul_ne_zero
      (neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hp0)))
      (pow_ne_zero _ (by norm_num))
  · exact mul_ne_zero (pow_ne_zero _ hp0) (derivative_F_node_ne_zero hp K i)

theorem det_hankelLin_ne_zero (hp : 2 ≤ p) (K : ℕ) : (hankelLin p K).det ≠ 0 := by
  rw [hankelLin_factor, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_diagonal]
  exact mul_ne_zero
    (mul_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr (nodes_injective hp K))
      (Finset.prod_ne_zero_iff.mpr (fun i hi => linWeight_ne_zero hp K i)))
    (Matrix.det_vandermonde_ne_zero_iff.mpr (nodes_injective hp K))

theorem Delta_ne_zero (hp : 2 ≤ p) (K : ℕ) : Delta p K ≠ 0 := by
  intro h
  have ht := det_hankelLin_ne_zero hp K
  rw [← coeff_Delta_top_eq_det, h, coeff_zero] at ht
  exact ht rfl

theorem natDegree_Delta (hp : 2 ≤ p) (K : ℕ) : (Delta p K).natDegree = K := by
  apply le_antisymm (natDegree_Delta_le p K)
  apply Polynomial.le_natDegree_of_ne_zero
  rw [coeff_Delta_top_eq_det]
  exact det_hankelLin_ne_zero hp K

theorem prod_nodes (p K : ℕ) : ∏ i : Fin K, nodes p K i = (p : ℚ) ^ (K * (K + 1)) := by
  unfold nodes
  rw [← QZeta3.prod_Icc_eq_fin K (fun a => (p : ℚ) ^ (2 * a))]
  rw [Finset.prod_pow_eq_pow_sum, ← Finset.mul_sum, Nat.mul_comm,
    QZeta3.sum_Icc_id_mul_two]

theorem neg_nrm_pow (p K : ℕ) : (-nrm p K) ^ K = (p : ℚ) ^ (K * (K + 1) * K) := by
  have heven : Even ((K + 1) * K) := by simpa [Nat.mul_comm] using Nat.even_mul_succ_self K
  calc
    (-nrm p K) ^ K = ((-1 : ℚ) ^ (K + 1) * (p : ℚ) ^ (K * (K + 1))) ^ K := by
      congr 1
      simp [nrm, pow_succ]
    _ = (p : ℚ) ^ (K * (K + 1) * K) := by
      rw [mul_pow, ← pow_mul, heven.neg_one_pow, one_mul, ← pow_mul]

theorem signed_node_product (K : ℕ) :
    (∏ i : Fin K, (-1 : ℚ) ^ (i.val + 1)) *
      (-1 : ℚ) ^ (K * (K - 1) / 2) = (-1 : ℚ) ^ K := by
  rw [← QZeta3.prod_Icc_eq_fin K (fun a => (-1 : ℚ) ^ a),
    Finset.prod_pow_eq_pow_sum, ← pow_add]
  have hs := QZeta3.sum_Icc_id_mul_two K
  have ht := Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self K)
  have he : (∑ a ∈ Icc 1 K, a) + K * (K - 1) / 2 = K + K * (K - 1) := by
    by_cases hk : K = 0
    · subst K; simp
    have hk' : K - 1 + 1 = K := by omega
    nlinarith
  rw [he, pow_add, (Nat.even_mul_pred_self K).neg_one_pow, mul_one]

theorem det_hankelLin_eq (hp : 2 ≤ p) (K : ℕ) :
    (hankelLin p K).det = (-1) ^ K * (p : ℚ) ^ (K * (K ^ 2 - 1)) := by
  by_cases hK : K = 0
  · subst K; simp [hankelLin]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hv0 := Matrix.det_vandermonde_ne_zero_iff.mpr (nodes_injective hp K)
  have hprod : ∏ i : Fin K, (derivative (F p K)).eval (nodes p K i) =
      (-1 : ℚ) ^ (K * (K - 1) / 2) * (Matrix.vandermonde (nodes p K)).det ^ 2 := by
    rw [F_eq_nodal]
    exact QZeta3.prod_derivative_nodal K (nodes p K)
  have hexp : K * (K + 1) * K = K * (K + 1) + K * (K ^ 2 - 1) := by
    have : K ^ 2 - 1 + 1 = K ^ 2 := by
      have : 1 ≤ K := by omega
      have : 1 ≤ K ^ 2 := by nlinarith
      omega
    nlinarith
  have hsign : ((-1 : ℚ) ^ (K * (K - 1) / 2)) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hsignprod := signed_node_product K
  rw [hankelLin_factor, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_diagonal]
  simp_rw [linWeight, Finset.prod_div_distrib, Finset.prod_mul_distrib]
  rw [Finset.prod_const, card_univ, Fintype.card_fin, prod_nodes, hprod, neg_nrm_pow,
    hexp, pow_add]
  field_simp
  calc
    (∏ i : Fin K, (-1 : ℚ) ^ (i.val + 1)) =
        (∏ i : Fin K, (-1 : ℚ) ^ (i.val + 1)) *
          ((-1 : ℚ) ^ (K * (K - 1) / 2)) ^ 2 := by rw [hsign, mul_one]
    _ = (-1 : ℚ) ^ (K * (K - 1) / 2) *
        ((∏ i : Fin K, (-1 : ℚ) ^ (i.val + 1)) *
          (-1 : ℚ) ^ (K * (K - 1) / 2)) := by ring
    _ = (-1 : ℚ) ^ (K * (K - 1) / 2) * (-1 : ℚ) ^ K := by rw [hsignprod]

theorem leading_coeff (hp : 2 ≤ p) (K : ℕ) :
    (Delta p K).coeff K = (-1) ^ K * (p : ℚ) ^ (K * (K ^ 2 - 1)) := by
  rw [coeff_Delta_top_eq_det, det_hankelLin_eq hp]

end QCatalan
