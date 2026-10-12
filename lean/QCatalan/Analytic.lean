import QCatalan.Series
import QZeta3.AnalyticDeterminant
import QZeta3.AnalyticWeight
import QZeta3.GeometricTail

/-!
# The double-root basis in the q-Catalan determinant estimate

The polynomial statements below are unconditional.  The determinant estimate
at the end is the finite-dimensional step: its entry-bound hypothesis is
explicit, and is not a claim that the functional estimate is already proved.
-/

open Polynomial Finset Matrix

namespace QCatalan

/-- Two successive roots are placed at each successive odd geometric node. -/
noncomputable def doubleRootPoly (q : ℝ) (j : ℕ) : ℝ[X] :=
  ∏ t ∈ Icc 1 j, (X - C (q ^ (2 * ((t + 1) / 2) - 1)))

/-- Largest root exponent, with zero at degree zero. -/
def rootCutoff (j : ℕ) : ℕ := 2 * ((j + 1) / 2) - 1

theorem doubleRootPoly_monic (q : ℝ) (j : ℕ) : (doubleRootPoly q j).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _

theorem doubleRootPoly_natDegree (q : ℝ) (j : ℕ) :
    (doubleRootPoly q j).natDegree = j := by
  unfold doubleRootPoly
  rw [Polynomial.natDegree_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _,
    Finset.sum_congr rfl fun t _ => Polynomial.natDegree_X_sub_C _]
  simp

theorem doubleRootPoly_succ (q : ℝ) (j : ℕ) :
    doubleRootPoly q (j + 1) = doubleRootPoly q j *
      (X - C (q ^ (2 * ((j + 2) / 2) - 1))) := by
  unfold doubleRootPoly
  rw [Finset.prod_Icc_succ_top (by omega)]

theorem doubleRootPoly_dvd (q : ℝ) {a b : ℕ} (hab : a ≤ b) :
    doubleRootPoly q a ∣ doubleRootPoly q b := by
  induction b, hab using Nat.le_induction with
  | base => exact dvd_refl _
  | succ b hab ih =>
    rw [doubleRootPoly_succ]
    exact dvd_mul_of_dvd_left ih _

/-- A completed pair supplies a double root at the associated odd node. -/
theorem doubleRootPoly_block (q : ℝ) (n : ℕ) :
    doubleRootPoly q (2 * (n + 1)) =
      doubleRootPoly q (2 * n) * (X - C (q ^ (2 * n + 1))) ^ 2 := by
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
  rw [doubleRootPoly_succ, doubleRootPoly_succ]
  have h₁ : 2 * ((2 * n + 2) / 2) - 1 = 2 * n + 1 := by omega
  have h₂ : 2 * ((2 * n + 1 + 2) / 2) - 1 = 2 * n + 1 := by omega
  rw [h₁, h₂]
  ring

theorem doubleRoot_dvd (q : ℝ) {n j : ℕ} (hj : 2 * (n + 1) ≤ j) :
    (X - C (q ^ (2 * n + 1))) ^ 2 ∣ doubleRootPoly q j := by
  apply dvd_trans _ (doubleRootPoly_dvd q hj)
  rw [doubleRootPoly_block]
  exact dvd_mul_left _ _

/-- Both jets vanish at an odd node whose repeated root is complete. -/
theorem doubleRoot_jets_vanish (q : ℝ) {n j : ℕ} (hj : 2 * (n + 1) ≤ j) :
    (doubleRootPoly q j).eval (q ^ (2 * n + 1)) = 0 ∧
      (doubleRootPoly q j).derivative.eval (q ^ (2 * n + 1)) = 0 := by
  obtain ⟨f, hf⟩ := doubleRoot_dvd q hj
  rw [hf]
  simp [Polynomial.derivative_mul, Polynomial.derivative_pow]

/-- At every surviving node, each factor is bounded by its root. -/
theorem doubleRoot_eval_bound {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (j m : ℕ) (hm : rootCutoff j ≤ m) :
    |(doubleRootPoly q j).eval (q ^ m)| ≤ q ^ aj j := by
  unfold doubleRootPoly aj
  rw [Polynomial.eval_prod, Finset.abs_prod, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod₀
  · intro t ht
    exact abs_nonneg _
  · intro t ht
    have htj := (Finset.mem_Icc.mp ht).2
    have htm : 2 * ((t + 1) / 2) - 1 ≤ m := by
      dsimp [rootCutoff] at hm
      omega
    have hpow : q ^ m ≤ q ^ (2 * ((t + 1) / 2) - 1) :=
      pow_le_pow_of_le_one hq0 hq1 htm
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [abs_of_nonpos (sub_nonpos.mpr hpow)]
    have : 0 ≤ q ^ m := pow_nonneg hq0 m
    linarith

/-- First-derivative product estimate, without divisions in the induction. -/
theorem doubleRoot_derivative_bounds {q x a : ℝ} (hq : 0 < q)
    (hx : 0 ≤ x) (ha : 0 < a) (hxa : x ≤ a) (j : ℕ)
    (hroot : ∀ t ∈ Icc 1 j, a ≤ q ^ (2 * ((t + 1) / 2) - 1)) :
    |(doubleRootPoly q j).eval x| ≤ q ^ aj j ∧
      |(doubleRootPoly q j).derivative.eval x| * a ≤ (j : ℝ) * q ^ aj j := by
  induction j with
  | zero => simp [doubleRootPoly, aj]
  | succ j ih =>
    have hr : a ≤ q ^ (2 * ((j + 2) / 2) - 1) := hroot (j + 1) (by simp)
    have hi := ih (fun t ht => hroot t (by
      rcases Finset.mem_Icc.mp ht with ⟨ht1, htj⟩
      exact Finset.mem_Icc.mpr ⟨ht1, by omega⟩))
    let P := q ^ aj j
    let r := q ^ (2 * ((j + 2) / 2) - 1)
    let f := doubleRootPoly q j
    have hP : 0 ≤ P := (pow_pos hq _).le
    have hr0 : 0 ≤ r := (pow_pos hq _).le
    have hxr : |x - r| ≤ r := by
      rw [abs_of_nonpos (by dsimp [r]; linarith)]
      linarith
    have hpow : q ^ aj (j + 1) = P * r := by
      dsimp [P, r]
      unfold aj
      rw [Finset.sum_Icc_succ_top (by omega), pow_add]
    have he0 : (doubleRootPoly q (j + 1)).eval x = f.eval x * (x - r) := by
      rw [doubleRootPoly_succ]
      simp [f, r]
    have he1 : (doubleRootPoly q (j + 1)).derivative.eval x =
        f.derivative.eval x * (x - r) + f.eval x := by
      rw [doubleRootPoly_succ]
      simp only [Polynomial.derivative_mul, Polynomial.derivative_sub,
        Polynomial.derivative_X, Polynomial.derivative_C, sub_zero,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, mul_one, f, r]
    change |f.eval x| ≤ P ∧ |f.derivative.eval x| * a ≤ (j : ℝ) * P at hi
    have hb0 : |f.eval x * (x - r)| ≤ P * r := by
      rw [abs_mul]
      exact mul_le_mul hi.1 hxr (abs_nonneg _) hP
    have hb1 := QZeta3.first_jet_product_step x a r P j (f.eval x) (f.derivative.eval x)
      ha.le hr hP hxr hi.1 hi.2
    rw [he0, he1, hpow]
    push_cast
    exact ⟨hb0, hb1⟩

/-- The surviving Euler derivative has the exact geometric loss of the paper. -/
theorem doubleRoot_euler_bound {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (j m : ℕ) (hm : rootCutoff j ≤ m) :
    |QZeta3.theta (fun x => (doubleRootPoly q j).eval x) (q ^ m)| ≤
      (j : ℝ) * q ^ aj j * q ^ m / q ^ rootCutoff j := by
  have hxa := pow_le_pow_of_le_one hq0.le hq1 hm
  have h := doubleRoot_derivative_bounds hq0 (pow_pos hq0 m).le
    (pow_pos hq0 _) hxa j (fun t ht =>
      pow_le_pow_of_le_one hq0.le hq1 (by
        have := (Finset.mem_Icc.mp ht).2
        dsimp [rootCutoff]
        omega))
  rw [QZeta3.theta_polynomial, le_div_iff₀ (pow_pos hq0 _), abs_mul,
    abs_of_nonneg (pow_pos hq0 m).le]
  nlinarith [mul_le_mul_of_nonneg_left h.2 (pow_pos hq0 m).le]

/-- Both contributions to the first Euler derivative vanish at omitted nodes. -/
theorem doubleRoot_euler_vanish (q : ℝ) {n j : ℕ}
    (hj : 2 * n + 1 < rootCutoff j) :
    (doubleRootPoly q j).eval (q ^ (2 * n + 1)) = 0 ∧
      QZeta3.theta (fun x => (doubleRootPoly q j).eval x) (q ^ (2 * n + 1)) = 0 := by
  have hcomplete : 2 * (n + 1) ≤ j := by dsimp [rootCutoff] at hj; omega
  obtain ⟨h₀, h₁⟩ := doubleRoot_jets_vanish q hcomplete
  rw [QZeta3.theta_polynomial, h₀, h₁]
  simp

/-- Coefficient matrix for the monic double-root basis. -/
noncomputable def doubleRootChange (q : ℝ) (K : ℕ) : Matrix (Fin K) (Fin K) ℝ :=
  fun i j => (doubleRootPoly q i.val).coeff j.val

theorem det_doubleRootChange (q : ℝ) (K : ℕ) : (doubleRootChange q K).det = 1 := by
  have h := Matrix.det_matrixOfPolynomials (fun i : Fin K => doubleRootPoly q i.val)
    (fun i => doubleRootPoly_natDegree q i.val) (fun i => doubleRootPoly_monic q i.val)
  convert h using 1
  exact (Matrix.det_transpose _).symm

/-- Row and column weights combine into the exact declared exponent. -/
theorem prod_doubleRoot_weights (p K : ℕ) :
    (∏ i : Fin K, ((p : ℝ)⁻¹) ^ aj i.val) ^ 2 = ((p : ℝ)⁻¹) ^ bK K := by
  rw [Finset.prod_pow_eq_pow_sum, ← pow_mul]
  congr 1
  simp only [bK, Fin.sum_univ_eq_sum_range]
  omega

/-- Finite determinant step, using the factorial bound (the same cubic
exponent as the paper, and a slightly larger subcubic prefactor).  The
functional entry estimate is a visible, separate hypothesis. -/
theorem doubleRoot_det_bound (p K : ℕ) (hp : 2 ≤ p)
    (A : Matrix (Fin K) (Fin K) ℝ)
    (hA : ∀ i j, |A i j| ≤
      2 * ((i.val : ℝ) + j.val + 1) * ((p : ℝ)⁻¹) ^ (aj i.val + aj j.val)) :
    |A.det| ≤ (K.factorial : ℝ) * (2 * (2 * (K : ℝ) - 1)) ^ K *
      ((p : ℝ)⁻¹) ^ bK K := by
  have hp0 : 0 < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast (show 0 < p by omega))
  have hentry : ∀ i j : Fin K, |A i j| ≤
      (2 * (2 * (K : ℝ) - 1)) * ((p : ℝ)⁻¹) ^ aj i.val *
        ((p : ℝ)⁻¹) ^ aj j.val := by
    intro i j
    have hi : (i.val : ℝ) + 1 ≤ K := by exact_mod_cast i.isLt
    have hj : (j.val : ℝ) + 1 ≤ K := by exact_mod_cast j.isLt
    have hle : (i.val : ℝ) + j.val + 1 ≤ 2 * K - 1 := by linarith
    calc |A i j| ≤ 2 * ((i.val : ℝ) + j.val + 1) *
          ((p : ℝ)⁻¹) ^ (aj i.val + aj j.val) := hA i j
      _ ≤ 2 * (2 * (K : ℝ) - 1) * ((p : ℝ)⁻¹) ^ (aj i.val + aj j.val) := by
        gcongr
      _ = _ := by rw [pow_add]; ring
  have h := QZeta3.abs_det_le_of_scaled_entries A (fun i => ((p : ℝ)⁻¹) ^ aj i.val)
    (2 * (2 * (K : ℝ) - 1)) (fun i => pow_pos hp0 _) hentry
  simpa only [Fintype.card_fin, prod_doubleRoot_weights] using h

/-- The denominator on the even exterior lattice. -/
noncomputable def DK (p K : ℕ) (x : ℝ) : ℝ :=
  ∏ a ∈ Icc 1 K, (1 - ((p : ℝ)⁻¹) ^ (2 * a) * x)

/-- Reciprocal denominator with the base left as a real parameter. -/
noncomputable def squareWeight (q : ℝ) (K : ℕ) : ℝ → ℝ :=
  QZeta3.rationalWeight (q ^ 2) K

theorem squareWeight_eq_DK_inv (p K : ℕ) :
    squareWeight ((p : ℝ)⁻¹) K = fun x => (DK p K x)⁻¹ := by
  funext x
  simp only [squareWeight, QZeta3.rationalWeight, DK, ← pow_mul,
    Finset.prod_inv_distrib]

theorem square_node_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (a : ℕ) :
    (q ^ 2) ^ a ≤ q ^ a := by
  rw [← pow_mul]
  exact pow_le_pow_of_le_one hq0 hq1 (by omega)

theorem squareWeight_factor_bounds {q x : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hx0 : 0 ≤ x) (hxq : x ≤ q) {a : ℕ} (ha : 1 ≤ a) :
    0 ≤ (q ^ 2) ^ a * x ∧ (q ^ 2) ^ a * x ≤ 1 / 4 := by
  have h := QZeta3.weight_factor_bounds hq0 hq1 hx0 hxq ha
  refine ⟨by positivity, ?_⟩
  exact (mul_le_mul_of_nonneg_right (square_node_le hq0 (by linarith) a) hx0).trans h.2

/-- Elementary uniform control suffices; this avoids numerical exponential bounds. -/
theorem squareWeight_bounds {q x : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hx0 : 0 ≤ x) (hxq : x ≤ q) (K : ℕ) :
    0 < squareWeight q K x ∧ squareWeight q K x ≤ 2 := by
  have hfac : ∀ a ∈ Icc 1 K, 0 < 1 - (q ^ 2) ^ a * x := by
    intro a ha
    have h := squareWeight_factor_bounds hq0 hq1 hx0 hxq (mem_Icc.mp ha).1
    linarith
  have hprod : 1 / 2 ≤ ∏ a ∈ Icc 1 K, (1 - (q ^ 2) ^ a * x) := by
    have h := QZeta3.one_sub_sum_le_prod (Icc 1 K) (fun a => (q ^ 2) ^ a * x)
      (fun a ha => (squareWeight_factor_bounds hq0 hq1 hx0 hxq (mem_Icc.mp ha).1).1)
      (fun a ha => le_trans (squareWeight_factor_bounds hq0 hq1 hx0 hxq (mem_Icc.mp ha).1).2 (by norm_num))
    rw [← sum_mul] at h
    have hsum : ∑ a ∈ Icc 1 K, (q ^ 2) ^ a ≤ 1 := by
      calc _ ≤ ∑ a ∈ Icc 1 K, q ^ a := sum_le_sum fun a _ => square_node_le hq0 (by linarith) a
        _ ≤ 1 := QZeta3.sum_geometric_nodes_le_one hq0 hq1 K
    nlinarith [mul_le_mul_of_nonneg_right hsum hx0]
  unfold squareWeight QZeta3.rationalWeight
  rw [Finset.prod_inv_distrib]
  constructor
  · exact inv_pos.mpr (prod_pos hfac)
  · rw [inv_le_iff_one_le_mul₀ (prod_pos hfac)]
    linarith

theorem squareWeight_alpha_bounds {q x : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hx0 : 0 ≤ x) (hxq : x ≤ q) (K : ℕ) :
    0 ≤ QZeta3.weightAlpha (q ^ 2) K x ∧
      QZeta3.weightAlpha (q ^ 2) K x ≤ (4 / 3) * x := by
  have hterm (a : ℕ) (ha : a ∈ Icc 1 K) :
      0 ≤ (q ^ 2) ^ a * x / (1 - (q ^ 2) ^ a * x) ∧
      (q ^ 2) ^ a * x / (1 - (q ^ 2) ^ a * x) ≤ (4 / 3) * ((q ^ 2) ^ a * x) := by
    have hy := squareWeight_factor_bounds hq0 hq1 hx0 hxq (mem_Icc.mp ha).1
    constructor
    · exact div_nonneg hy.1 (by linarith)
    · calc
        _ ≤ ((q ^ 2) ^ a * x) / (3 / 4) :=
          div_le_div_of_nonneg_left hy.1 (by norm_num) (by linarith)
        _ = _ := by ring
  constructor
  · exact sum_nonneg (fun a ha => (hterm a ha).1)
  · calc
      QZeta3.weightAlpha (q ^ 2) K x ≤ ∑ a ∈ Icc 1 K, (4 / 3) * ((q ^ 2) ^ a * x) :=
        sum_le_sum (fun a ha => (hterm a ha).2)
      _ ≤ ∑ a ∈ Icc 1 K, (4 / 3) * (q ^ a * x) := by
        apply sum_le_sum
        intro a ha
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (square_node_le hq0 (by linarith) a) hx0) (by norm_num)
      _ = (4 / 3) * (∑ a ∈ Icc 1 K, q ^ a) * x := by rw [← mul_sum, ← sum_mul]; ring
      _ ≤ (4 / 3) * x := by
        have h := mul_le_mul_of_nonneg_right (QZeta3.sum_geometric_nodes_le_one hq0 hq1 K) hx0
        nlinarith

/-- The weight and its first Euler derivative are uniformly controlled. -/
theorem squareWeight_euler_bounds {q x : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hx0 : 0 ≤ x) (hxq : x ≤ q) (K : ℕ) :
    |squareWeight q K x| ≤ 2 ∧
      |QZeta3.theta (squareWeight q K) x| ≤ (8 / 3) * x := by
  have hw := squareWeight_bounds hq0 hq1 hx0 hxq K
  have ha := squareWeight_alpha_bounds hq0 hq1 hx0 hxq K
  have hx : ∀ a ∈ Icc 1 K, 1 - (q ^ 2) ^ a * x ≠ 0 := by
    intro a ha
    have hy := squareWeight_factor_bounds hq0 hq1 hx0 hxq (mem_Icc.mp ha).1
    linarith
  rw [abs_of_pos hw.1]
  refine ⟨hw.2, ?_⟩
  change |QZeta3.theta (QZeta3.rationalWeight (q ^ 2) K) x| ≤ _
  have hw' : 0 < QZeta3.rationalWeight (q ^ 2) K x := hw.1
  rw [QZeta3.theta_rationalWeight K hx,
    abs_of_nonneg (mul_nonneg hw'.le ha.1)]
  calc _ ≤ 2 * ((4 / 3) * x) := mul_le_mul hw.2 ha.2 ha.1 (by norm_num)
    _ = _ := by ring

/-- The root and derivative estimates with one common surviving cutoff. -/
theorem doubleRoot_jets_common {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (i m R : ℕ) (hi : rootCutoff i ≤ R) (hm : R ≤ m) :
    |(doubleRootPoly q i).eval (q ^ m)| ≤ q ^ aj i ∧
      |QZeta3.theta (fun x => (doubleRootPoly q i).eval x) (q ^ m)| ≤
        (i : ℝ) * q ^ aj i * (q ^ m / q ^ R) := by
  have hxa := pow_le_pow_of_le_one hq.le hq1 hm
  have h := doubleRoot_derivative_bounds hq (pow_pos hq m).le (pow_pos hq _) hxa i
    (fun t ht => pow_le_pow_of_le_one hq.le hq1 (by
      have := (Finset.mem_Icc.mp ht).2
      dsimp [rootCutoff] at hi
      omega))
  refine ⟨h.1, ?_⟩
  rw [QZeta3.theta_polynomial, ← mul_div_assoc, le_div_iff₀ (pow_pos hq _), abs_mul,
    abs_of_nonneg (pow_pos hq m).le]
  nlinarith [mul_le_mul_of_nonneg_left h.2 (pow_pos hq m).le]

/-- First-order scalar product estimate for two basis elements. -/
theorem euler_product_bound (a b u v A B i j t : ℝ)
    (hA : 0 ≤ A) (_hB : 0 ≤ B) (hi : 0 ≤ i) (ht : 0 ≤ t)
    (ha : |a| ≤ A) (hb : |b| ≤ B)
    (hu : |u| ≤ i * A * t) (hv : |v| ≤ j * B * t) :
    |a * b| ≤ A * B ∧ |u * b + a * v| ≤ (i + j) * (A * B) * t := by
  constructor
  · rw [abs_mul]
    exact mul_le_mul ha hb (abs_nonneg _) hA
  · calc _ ≤ |u * b| + |a * v| := abs_add_le _ _
      _ = |u| * |b| + |a| * |v| := by rw [abs_mul, abs_mul]
      _ ≤ (i * A * t) * B + A * (j * B * t) :=
        add_le_add (mul_le_mul hu hb (abs_nonneg _) (by positivity))
          (mul_le_mul ha hv (abs_nonneg _) hA)
      _ = _ := by ring

/-- Adjoining the reciprocal denominator costs only a constant. -/
theorem euler_weight_bound (a u w v A h x t : ℝ)
    (hA : 0 ≤ A) (hh : 0 ≤ h) (hxt : x ≤ t) (ht0 : 0 ≤ t)
    (ha : |a| ≤ A) (hu : |u| ≤ h * A * t)
    (hw : |w| ≤ 2) (hv : |v| ≤ (8 / 3) * x) :
    |u * w + a * v| ≤ (8 / 3) * (h + 1) * A * t := by
  calc _ ≤ |u * w| + |a * v| := abs_add_le _ _
    _ = |u| * |w| + |a| * |v| := by rw [abs_mul, abs_mul]
    _ ≤ (h * A * t) * 2 + A * ((8 / 3) * x) :=
      add_le_add (mul_le_mul hu hw (abs_nonneg _) (by positivity))
        (mul_le_mul ha hv (abs_nonneg _) hA)
    _ ≤ (h * A * t) * 2 + A * ((8 / 3) * t) := by gcongr
    _ ≤ _ := by nlinarith [mul_nonneg hh (mul_nonneg hA ht0)]

/-- All surviving pointwise first-derivative estimates for the actual weight. -/
theorem doubleRoot_entry_surviving {q : ℝ} (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (K i j m : ℕ) (hm : 1 ≤ m) (hR : max (rootCutoff i) (rootCutoff j) ≤ m) :
    |QZeta3.theta (fun x => (doubleRootPoly q i).eval x *
        (doubleRootPoly q j).eval x * squareWeight q K x) (q ^ m)| ≤
      (8 / 3) * ((i : ℝ) + j + 1) * q ^ (aj i + aj j) *
        q ^ (m - max (rootCutoff i) (rootCutoff j)) := by
  let R := max (rootCutoff i) (rootCutoff j)
  let x := q ^ m
  let t := x / q ^ R
  let f : ℝ → ℝ := fun x => (doubleRootPoly q i).eval x
  let g : ℝ → ℝ := fun x => (doubleRootPoly q j).eval x
  have hq1 : q ≤ 1 := by linarith
  have hx0 : 0 ≤ x := (pow_pos hq m).le
  have hxq : x ≤ q := by simpa only [pow_one] using pow_le_pow_of_le_one hq.le hq1 hm
  have ht0 : 0 ≤ t := div_nonneg hx0 (pow_pos hq R).le
  have hxt : x ≤ t := (le_div_iff₀ (pow_pos hq R)).mpr (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ hq.le hq1) hx0)
  have hi := doubleRoot_jets_common hq hq1 i m R (le_max_left _ _) hR
  have hj := doubleRoot_jets_common hq hq1 j m R (le_max_right _ _) hR
  have hf : DifferentiableAt ℝ f x := (doubleRootPoly q i).differentiableAt
  have hg : DifferentiableAt ℝ g x := (doubleRootPoly q j).differentiableAt
  have hw : DifferentiableAt ℝ (squareWeight q K) x :=
    (QZeta3.contDiffAt_rationalWeight K (fun a ha => by
      have hy := squareWeight_factor_bounds hq.le hqhalf hx0 hxq (mem_Icc.mp ha).1
      linarith)).differentiableAt (by norm_num)
  have hp := euler_product_bound (f x) (g x) (QZeta3.theta f x) (QZeta3.theta g x)
    (q ^ aj i) (q ^ aj j) i j t (pow_pos hq _).le (pow_pos hq _).le
    (Nat.cast_nonneg _) ht0 hi.1 hj.1 hi.2 hj.2
  have hp1 : |QZeta3.theta (f * g) x| ≤ ((i : ℝ) + j) * (q ^ aj i * q ^ aj j) * t := by
    rw [QZeta3.theta_mul hf hg]
    exact hp.2
  have hwbound := squareWeight_euler_bounds hq.le hqhalf hx0 hxq K
  have h := euler_weight_bound ((f * g) x) (QZeta3.theta (f * g) x)
    (squareWeight q K x) (QZeta3.theta (squareWeight q K) x)
    (q ^ aj i * q ^ aj j) (i + j) x t (by positivity) (by positivity)
    hxt ht0 hp.1 hp1 hwbound.1 hwbound.2
  have ht : t = q ^ (m - R) := by
    dsimp [t, x]
    exact (pow_sub₀ q hq.ne' hR).symm
  change |QZeta3.theta ((f * g) * squareWeight q K) x| ≤ _
  rw [QZeta3.theta_mul (hf.mul hg) hw]
  simpa only [← pow_add, ht, R] using h

/-- At every earlier odd node the complete weighted summand vanishes. -/
theorem doubleRoot_entry_vanish {q : ℝ} (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (K i j n : ℕ) (hR : 2 * n + 1 < max (rootCutoff i) (rootCutoff j)) :
    QZeta3.theta (fun x => (doubleRootPoly q i).eval x *
        (doubleRootPoly q j).eval x * squareWeight q K x) (q ^ (2 * n + 1)) = 0 := by
  let f : ℝ → ℝ := fun x => (doubleRootPoly q i).eval x
  let g : ℝ → ℝ := fun x => (doubleRootPoly q j).eval x
  let x := q ^ (2 * n + 1)
  have hf : DifferentiableAt ℝ f x := (doubleRootPoly q i).differentiableAt
  have hg : DifferentiableAt ℝ g x := (doubleRootPoly q j).differentiableAt
  have hxq : x ≤ q := by
    simpa only [pow_one] using pow_le_pow_of_le_one hq.le (by linarith : q ≤ 1)
      (show 1 ≤ 2 * n + 1 by omega)
  have hw : DifferentiableAt ℝ (squareWeight q K) x :=
    (QZeta3.contDiffAt_rationalWeight K (fun a ha => by
      have hy := squareWeight_factor_bounds hq.le hqhalf (pow_pos hq _).le hxq (mem_Icc.mp ha).1
      linarith)).differentiableAt (by norm_num)
  have hz : (f * g) x = 0 ∧ QZeta3.theta (f * g) x = 0 := by
    rw [QZeta3.theta_mul hf hg]
    rcases lt_max_iff.mp hR with hi | hj
    · obtain ⟨h₀, h₁⟩ := doubleRoot_euler_vanish q hi
      change f x = 0 at h₀
      change QZeta3.theta f x = 0 at h₁
      simp [Pi.mul_apply, h₀, h₁]
    · obtain ⟨h₀, h₁⟩ := doubleRoot_euler_vanish q hj
      change g x = 0 at h₀
      change QZeta3.theta g x = 0 at h₁
      simp [Pi.mul_apply, h₀, h₁]
  change QZeta3.theta ((f * g) * squareWeight q K) x = 0
  rw [QZeta3.theta_mul (hf.mul hg) hw, hz.1, hz.2]
  simp

/-- The complete signed summand is controlled at every lattice index. -/
theorem doubleRoot_entry_majorant {p : ℕ} (hp : 2 ≤ p) (K i j m : ℕ) :
    |(chi (m + 1) : ℝ) * theta (fun x => (doubleRootPoly ((p : ℝ)⁻¹) i).eval x *
        (doubleRootPoly ((p : ℝ)⁻¹) j).eval x / DK p K x) (((p : ℝ)⁻¹) ^ (m + 1))| ≤
      ((8 / 3) * ((i : ℝ) + j + 1) * ((p : ℝ)⁻¹) ^ (aj i + aj j)) *
        QZeta3.geometricTail ((p : ℝ)⁻¹) (max (rootCutoff i) (rootCutoff j)) m := by
  have hqhalf : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    simpa only [one_div] using one_div_le_one_div_of_le
      (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hp : (2 : ℝ) ≤ p)
  have he : (fun x => (doubleRootPoly ((p : ℝ)⁻¹) i).eval x *
        (doubleRootPoly ((p : ℝ)⁻¹) j).eval x / DK p K x) =
      fun x => (doubleRootPoly ((p : ℝ)⁻¹) i).eval x *
        (doubleRootPoly ((p : ℝ)⁻¹) j).eval x * squareWeight ((p : ℝ)⁻¹) K x := by
    rw [squareWeight_eq_DK_inv]
    rfl
  rw [he]
  unfold QZeta3.geometricTail
  split_ifs with hR
  · calc _ ≤ |QZeta3.theta (fun x => (doubleRootPoly ((p : ℝ)⁻¹) i).eval x *
          (doubleRootPoly ((p : ℝ)⁻¹) j).eval x * squareWeight ((p : ℝ)⁻¹) K x)
          (((p : ℝ)⁻¹) ^ (m + 1))| := by
            rw [abs_mul]
            exact (mul_le_mul_of_nonneg_right (abs_chi_le _) (abs_nonneg _)).trans_eq (one_mul _)
      _ ≤ _ := doubleRoot_entry_surviving (inv_base_pos hp) hqhalf K i j (m + 1) (by omega) hR
  · by_cases heven : (m + 1) % 2 = 0
    · simp [chi, heven]
    · have hodd : m + 1 = 2 * ((m + 1) / 2) + 1 := by omega
      have hz := doubleRoot_entry_vanish (inv_base_pos hp) hqhalf K i j ((m + 1) / 2)
        (by omega)
      rw [← hodd] at hz
      change theta _ _ = 0 at hz
      rw [hz]
      simp

/-- Absolute convergence of every actual transformed entry follows from the
explicit geometric envelope, including cancellation at early odd nodes. -/
theorem summable_doubleRoot_entry {p : ℕ} (hp : 2 ≤ p) (K i j : ℕ) :
    Summable (fun m : ℕ => (chi (m + 1) : ℝ) *
      theta (fun x => (doubleRootPoly ((p : ℝ)⁻¹) i).eval x *
        (doubleRootPoly ((p : ℝ)⁻¹) j).eval x / DK p K x)
        (((p : ℝ)⁻¹) ^ (m + 1))) := by
  have hqhalf : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    simpa only [one_div] using one_div_le_one_div_of_le
      (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hp : (2 : ℝ) ≤ p)
  have hg := (QZeta3.geometricTail_sum_bound (inv_base_pos hp) hqhalf
    (max (rootCutoff i) (rootCutoff j))).1
  exact Summable.of_norm_bounded (hg.mul_left
    ((8 / 3) * ((i : ℝ) + j + 1) * ((p : ℝ)⁻¹) ^ (aj i + aj j)))
    (by simpa only [Real.norm_eq_abs] using doubleRoot_entry_majorant hp K i j)

/-- Actual first-derivative functional entry estimate, with a conservative
constant six and exactly the cubic exponent of the paper. -/
theorem doubleRoot_entry_sum_bound {p : ℕ} (hp : 2 ≤ p) (K i j : ℕ) :
    |Lfun p (fun x => (doubleRootPoly ((p : ℝ)⁻¹) i).eval x *
        (doubleRootPoly ((p : ℝ)⁻¹) j).eval x / DK p K x)| ≤
      6 * ((i : ℝ) + j + 1) * ((p : ℝ)⁻¹) ^ (aj i + aj j) := by
  have hqhalf : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    simpa only [one_div] using one_div_le_one_div_of_le
      (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hp : (2 : ℝ) ≤ p)
  have h := QZeta3.abs_tsum_le_geometricTail (inv_base_pos hp) hqhalf
    (max (rootCutoff i) (rootCutoff j)) (summable_doubleRoot_entry hp K i j)
    (show 0 ≤ (8 / 3) * ((i : ℝ) + j + 1) *
      ((p : ℝ)⁻¹) ^ (aj i + aj j) by positivity)
    (fun m => doubleRoot_entry_majorant hp K i j m)
  change |Lfun p _| ≤ _ at h
  have hpos : 0 ≤ ((i : ℝ) + j + 1) * ((p : ℝ)⁻¹) ^ (aj i + aj j) := by positivity
  nlinarith only [h, hpos]

/-- The transformed matrix of the actual signed derivative functional. -/
noncomputable def doubleRootGram (p K : ℕ) : Matrix (Fin K) (Fin K) ℝ :=
  fun i j => Lfun p (fun x =>
    (doubleRootPoly ((p : ℝ)⁻¹) i.val).eval x *
    (doubleRootPoly ((p : ℝ)⁻¹) j.val).eval x / DK p K x)

/-- Unconditional cubic decay for the actual transformed signed Gram matrix.
The remaining identification with `DeltaR` is a separate algebraic bridge. -/
theorem doubleRootGram_det_bound {p : ℕ} (hp : 2 ≤ p) (K : ℕ) :
    |(doubleRootGram p K).det| ≤ (K.factorial : ℝ) * (6 * (2 * (K : ℝ) - 1)) ^ K *
      ((p : ℝ)⁻¹) ^ bK K := by
  have hp0 : 0 < (p : ℝ)⁻¹ := inv_base_pos hp
  have hentry : ∀ i j : Fin K, |doubleRootGram p K i j| ≤
      (6 * (2 * (K : ℝ) - 1)) * ((p : ℝ)⁻¹) ^ aj i.val *
        ((p : ℝ)⁻¹) ^ aj j.val := by
    intro i j
    have hi : (i.val : ℝ) + 1 ≤ K := by exact_mod_cast i.isLt
    have hj : (j.val : ℝ) + 1 ≤ K := by exact_mod_cast j.isLt
    have hle : (i.val : ℝ) + j.val + 1 ≤ 2 * K - 1 := by linarith
    calc _ ≤ 6 * ((i.val : ℝ) + j.val + 1) *
          ((p : ℝ)⁻¹) ^ (aj i.val + aj j.val) := doubleRoot_entry_sum_bound hp K i.val j.val
      _ ≤ 6 * (2 * (K : ℝ) - 1) * ((p : ℝ)⁻¹) ^ (aj i.val + aj j.val) := by gcongr
      _ = _ := by rw [pow_add]; ring
  have h := QZeta3.abs_det_le_of_scaled_entries (doubleRootGram p K)
    (fun i => ((p : ℝ)⁻¹) ^ aj i.val) (6 * (2 * (K : ℝ) - 1))
    (fun i => pow_pos hp0 _) hentry
  simpa only [Fintype.card_fin, prod_doubleRoot_weights] using h

end QCatalan
