import QCatalan.GramIdentity
import QCatalan.CauchyInterpolation
import QCatalan.CauchyNonrational
import QZeta3.NonvanishingAnalytic

/-!
# Infinitely many nonzero q-Catalan determinants

The actual signed first-derivative Cauchy transform has genuine double poles
at infinitely many odd geometric nodes. Its nonrational germ and the exterior
interpolation identities exclude an eventually singular determinant sequence.
No positivity or eventual nonvanishing claim is required.
-/

open Finset Filter Topology

namespace QCatalan

variable {p : ℕ}

/-- Singularity of the actual moving Gram matrix gives the orthogonal
polynomial used by the normality argument. -/
theorem gram_singular_orthogonal (hp : 2 ≤ p) {n : ℕ} (hn : 0 < n)
    (hsingular : (gramR p n).det = 0) :
    ∃ Q : Polynomial ℝ, Q ≠ 0 ∧ Q.natDegree < n ∧
      ∀ j : Fin n, Lfun p (fun x => x ^ j.val * Q.eval x / DK p n x) = 0 := by
  have hmoment : (Matrix.of fun i j : Fin n =>
      numeratorFunctional hp n (Polynomial.X ^ (i.val + j.val))).det = 0 := by
    simpa [numeratorFunctional, gramR] using hsingular
  obtain ⟨Q, hQ, hdegree, horth⟩ :=
    QZeta3.NonvanishingAlgebra.exists_orthogonal_polynomial hn (numeratorFunctional hp n) hmoment
  refine ⟨Q, hQ, hdegree, ?_⟩
  intro j
  simpa [numeratorFunctional] using horth j

/-- Analytic interface for Proposition 5.1.  All linear
algebra, polynomial stabilization, Laurent-order, and root-count steps are
proved by this reduction.  The following results discharge its hypotheses
for the actual q-functional. -/
theorem gram_frequently_ne_zero_of_cauchy_data (hp : 2 ≤ p)
    (hmeromorphic : MeromorphicAt (fun u : ℝ => cauchyF p u⁻¹) 0)
    (hnonrational : ∀ P Q : Polynomial ℝ, Q ≠ 0 →
      ¬ ∀ᶠ x : ℝ in atTop, cauchyF p x * Q.eval x - P.eval x = 0)
    (hinterpolant : ∀ n, 0 < n → ∀ Q : Polynomial ℝ, Q ≠ 0 → Q.natDegree < n →
      (∀ j : Fin n, Lfun p (fun x => x ^ j.val * Q.eval x / DK p n x) = 0) →
      ∃ P : Polynomial ℝ,
        Tendsto (fun x => cauchyF p x * Q.eval x - P.eval x) atTop (𝓝 0) ∧
        ∀ a, a < n → cauchyF p ((p : ℝ) ^ (2 * (a + 1))) *
          Q.eval ((p : ℝ) ^ (2 * (a + 1))) - P.eval ((p : ℝ) ^ (2 * (a + 1))) = 0) :
    ∀ N : ℕ, ∃ K, N ≤ K ∧ (gramR p K).det ≠ 0 := by
  have hp2 : 2 ≤ p ^ 2 := by nlinarith
  have h := QZeta3.NonvanishingAlgebra.frequently_nonsingular_of_meromorphic_nonrational
    (cauchyF p) (fun a : ℕ => (p : ℝ) ^ (2 * (a + 1)))
    (by simpa only [Nat.cast_pow, ← pow_mul] using
      QZeta3.NonvanishingAlgebra.exterior_nodes_injective hp2)
    (by simpa only [Nat.cast_pow, ← pow_mul] using
      QZeta3.NonvanishingAlgebra.exterior_nodes_tendsto hp2)
    (numeratorFunctional hp) hmeromorphic hnonrational
    (by simpa [numeratorFunctional] using hinterpolant)
  simpa [numeratorFunctional, gramR] using h

/-- Normality reduced to the nonrationality of the Cauchy germ, with every
other analytic input discharged for the actual q-functional. -/
theorem gram_frequently_ne_zero_of_nonrational (hp : 2 ≤ p)
    (hnonrational : ∀ P Q : Polynomial ℝ, Q ≠ 0 →
      ¬ ∀ᶠ x : ℝ in atTop, cauchyF p x * Q.eval x - P.eval x = 0) :
    ∀ N : ℕ, ∃ K, N ≤ K ∧ (gramR p K).det ≠ 0 := by
  apply gram_frequently_ne_zero_of_cauchy_data hp
    (meromorphicAt_cauchySeries_inv hp) hnonrational
  intro n hn Q hQ hdegree horth
  exact cauchy_orthogonal_interpolant hp n Q horth

/-- The real Gram determinant is nonzero for infinitely many sizes (§5). -/
theorem gram_frequently_ne_zero (hp : 2 ≤ p) : ∀ N : ℕ, ∃ K, N ≤ K ∧ (gramR p K).det ≠ 0 := by
  apply gram_frequently_ne_zero_of_nonrational hp
  exact cauchySeries_nonrational hp

/-- The concrete determinant polynomial has nonzero target values arbitrarily far out. -/
theorem frequently_ne_zero (hp : 2 ≤ p) (N : ℕ) :
    ∃ K, N ≤ K ∧ DeltaR p K (xi p) ≠ 0 := by
  obtain ⟨K, hNK, hK⟩ := gram_frequently_ne_zero hp N
  exact ⟨K, hNK, (gram_det_eq hp K) ▸ hK⟩

end QCatalan
