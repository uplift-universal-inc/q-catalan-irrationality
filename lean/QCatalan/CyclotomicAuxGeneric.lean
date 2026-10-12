import QCatalan.Defs
import QZeta3.GenericMoments
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Eval.SMul

/-! # Generic q-Catalan rational expressions

The base is a field element so that it can subsequently be the indeterminate
of a rational-function field. These definitions specialize to the actual
q-Catalan determinant, including its alternating residue signs and quotient.
-/

open Polynomial Finset

namespace QCatalan.Generic

variable {k : Type*} [Field k]

def mu (z : k) (j : ℕ) : k := (j : k) * z ^ j / (1 + z ^ (2 * j))
def g2 (y : k) : k := y / (1 - y) ^ 2
noncomputable def S (z : k) (N : ℕ) : k :=
  ∑ b ∈ Icc 1 N, (QCatalan.chi b : k) * g2 (z ^ b)
noncomputable def F (z : k) (K : ℕ) : k[X] :=
  ∏ a ∈ Icc 1 K, (X - C (z ^ (2 * a)))
noncomputable def Lpoly (z : k) (f : k[X]) : k :=
  ∑ j ∈ f.support, f.coeff j * mu z j
noncomputable def res (z : k) (K i a : ℕ) : k :=
  z ^ (2 * a * i) / (derivative (F z K)).eval (z ^ (2 * a))
noncomputable def mConst (z : k) (K i : ℕ) : k :=
  Lpoly z (X ^ i /ₘ F z K) +
    ∑ a ∈ Icc 1 K, res z K i a * (-1) ^ a * S z (2 * a) / z ^ (2 * a)
noncomputable def mLin (z : k) (K i : ℕ) : k :=
  -∑ a ∈ Icc 1 K, res z K i a * (-1) ^ a / z ^ (2 * a)
def nrm (z : k) (K : ℕ) : k := (-1) ^ K * z ^ (K * (K + 1))
noncomputable def hankelLin (z : k) (K : ℕ) : Matrix (Fin K) (Fin K) k :=
  Matrix.of fun i j => nrm z K * mLin z K (i.val + j.val)
noncomputable def hankelConst (z : k) (K : ℕ) : Matrix (Fin K) (Fin K) k :=
  Matrix.of fun i j => nrm z K * mConst z K (i.val + j.val)
noncomputable def Delta (z : k) (K : ℕ) : k[X] :=
  Matrix.det ((X : k[X]) • (hankelLin z K).map C + (hankelConst z K).map C)

theorem Delta_natCast (p K : ℕ) : Delta (p : ℚ) K = QCatalan.Delta p K := rfl

theorem F_eq_square_base (z : k) (K : ℕ) : F z K = QZeta3.Generic.F (z ^ 2) K := by
  simp [F, QZeta3.Generic.F, pow_mul]

theorem F_monic (z : k) (K : ℕ) : (F z K).Monic := by
  rw [F_eq_square_base]
  exact QZeta3.Generic.F_monic _ _

theorem F_natDegree (z : k) (K : ℕ) : (F z K).natDegree = K := by
  rw [F_eq_square_base]
  exact QZeta3.Generic.F_natDegree _ _

theorem quotient_coeff_mem_subring (R : Subring k) (z : k) (hz : z ∈ R) (K : ℕ)
    (f : k[X]) (hf : ∀ i, f.coeff i ∈ R) (i : ℕ) : (f /ₘ F z K).coeff i ∈ R := by
  rw [F_eq_square_base]
  exact QZeta3.Generic.quotient_coeff_mem_subring R (z ^ 2) (R.pow_mem hz 2) K f hf i

noncomputable def LpolyLinear (z : k) : k[X] →ₗ[k] k :=
  Polynomial.lsum (fun j => LinearMap.mulRight k (mu z j))

@[simp] theorem LpolyLinear_apply (z : k) (f : k[X]) :
    LpolyLinear z f = Lpoly z f := rfl

theorem Lpoly_add (z : k) (f g : k[X]) : Lpoly z (f+g) = Lpoly z f + Lpoly z g :=
  (LpolyLinear z).map_add f g

theorem Lpoly_smul (z c : k) (f : k[X]) : Lpoly z (c • f) = c * Lpoly z f :=
  (LpolyLinear z).map_smul c f

/-- Formal moment of the complete q-Catalan functional. -/
noncomputable def momentPolynomial (z : k) (K : ℕ) (f : k[X]) : k[X] :=
  C (Lpoly z (f /ₘ F z K)) - ∑ a ∈ Icc 1 K,
    C (f.eval (z^(2*a)) * (-1)^a / (z^(2*a) * (derivative (F z K)).eval (z^(2*a)))) * (X-C (S z (2*a)))

noncomputable def momentFunctional (z : k) (K : ℕ) : k[X] →ₗ[k] k[X] where
  toFun := momentPolynomial z K
  map_add' f g := by
    simp only [momentPolynomial, Polynomial.add_divByMonic, Lpoly_add, map_add,
      Polynomial.eval_add, add_div, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' c f := by
    simp only [momentPolynomial, Polynomial.smul_divByMonic, Lpoly_smul,
      Polynomial.eval_smul, smul_eq_mul, mul_div_assoc, map_mul, RingHom.id_apply]
    rw [Polynomial.smul_eq_C_mul, mul_sub, Finset.mul_sum]
    congr 1
    apply sum_congr rfl
    intro a ha
    ring

@[simp] theorem momentFunctional_apply (z : k) (K : ℕ) (f : k[X]) :
    momentFunctional z K f = momentPolynomial z K f := rfl

/-- The generalized functional agrees exactly with the original formal moments. -/
theorem momentPolynomial_monomial (z : k) (K n : ℕ) :
    momentPolynomial z K (X^n) = X*C (mLin z K n) + C (mConst z K n) := by
  have he (a : ℕ) : (X^n : k[X]).eval (z^(2*a)) * (-1)^a /
      (z^(2*a) * (derivative (F z K)).eval (z^(2*a))) = res z K n a * (-1)^a / z^(2*a) := by
    simp only [Polynomial.eval_pow, Polynomial.eval_X, res, ← pow_mul]
    ring
  simp only [momentPolynomial, he, mLin, mConst, map_neg, map_add, map_sum]
  rw [mul_neg, Finset.mul_sum]
  have hsum : (∑ a ∈ Icc 1 K, C (res z K n a * (-1)^a / z^(2*a)) * (X-C (S z (2*a)))) =
      (∑ a ∈ Icc 1 K, X*C (res z K n a * (-1)^a / z^(2*a))) -
        ∑ a ∈ Icc 1 K, C (res z K n a * (-1)^a * S z (2*a) / z^(2*a)) := by
    rw [← Finset.sum_sub_distrib]
    apply sum_congr rfl
    intro a ha
    rw [mul_sub, ← map_mul]
    congr 1
    · ring
    · congr 1
      ring
  rw [hsum]
  ring

noncomputable def normalizedGram (z : k) (K : ℕ) (G : Fin K → k[X]) :
    Matrix (Fin K) (Fin K) k[X] :=
  Matrix.of fun i j => C (nrm z K) * momentPolynomial z K (G i * G j)

noncomputable def polynomialChange (K : ℕ) (G : Fin K → k[X]) : Matrix (Fin K) (Fin K) k :=
  Matrix.of fun i j => (G i).coeff j.val

theorem normalizedGram_congruence (z : k) (K : ℕ) (G : Fin K → k[X])
    (hG : ∀ i, (G i).natDegree < K) :
    normalizedGram z K G = (polynomialChange K G).map C *
      ((X : k[X]) • (hankelLin z K).map C + (hankelConst z K).map C) *
      ((polynomialChange K G).map C).transpose := by
  let U := polynomialChange K G
  let L : k[X] →ₗ[k] k[X] := (nrm z K) • momentFunctional z K
  have hexp (i : Fin K) : G i = ∑ j : Fin K, U i j • (X : k[X])^j.val := by
    have h := (G i).as_sum_range_C_mul_X_pow' (hG i)
    rw [← Fin.sum_univ_eq_sum_range _ K] at h
    simpa only [U, polynomialChange, Matrix.of_apply, Polynomial.smul_eq_C_mul] using h
  have hmono (i j : Fin K) :
      L ((X : k[X])^(i.val+j.val)) =
        ((X : k[X]) • (hankelLin z K).map C + (hankelConst z K).map C) i j := by
    simp only [L, LinearMap.smul_apply, momentFunctional_apply, momentPolynomial_monomial,
      Polynomial.smul_eq_C_mul, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
      hankelLin, hankelConst, Matrix.of_apply, smul_eq_mul, map_mul]
    ring
  apply Matrix.ext
  intro i j
  have hid : normalizedGram z K G i j = L (G i * G j) := by
    simp [normalizedGram, L, Polynomial.smul_eq_C_mul]
  rw [hid]
  rw [hexp i, hexp j]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    ← pow_add, map_sum, map_smul, hmono]
  simp only [Polynomial.smul_eq_C_mul]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul, Finset.mul_sum]
  apply sum_congr rfl
  intro s hs
  apply sum_congr rfl
  intro r hr
  ring

/-- The determinant changes by the square of the coefficient determinant. -/
theorem det_normalizedGram (z : k) (K : ℕ) (G : Fin K → k[X])
    (hG : ∀ i, (G i).natDegree < K) :
    (normalizedGram z K G).det = C ((polynomialChange K G).det)^2 * Delta z K := by
  rw [normalizedGram_congruence z K G hG, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose]
  have hm : ((polynomialChange K G).map C).det = C ((polynomialChange K G).det) :=
    (RingHom.map_det C (polynomialChange K G)).symm
  rw [hm]
  unfold Delta
  ring


end QCatalan.Generic
