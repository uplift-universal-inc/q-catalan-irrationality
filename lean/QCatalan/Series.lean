import QCatalan.Defs
import QZeta3.Purity
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Convergence and elementary identities for the actual q-Catalan series

These statements concern the explicitly defined convergent series, not an abstract
real variable or an unverified irrationality hypothesis.
-/

set_option maxHeartbeats 2000000

open Polynomial Finset Filter Topology

namespace QCatalan

variable {p : ℕ}

theorem inv_base_pos (hp : 2 ≤ p) : 0 < (p : ℝ)⁻¹ := by
  have : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  positivity

theorem inv_base_lt_one (hp : 2 ≤ p) : (p : ℝ)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ (by exact_mod_cast (show 1 < p by omega))

theorem inv_base_pow_lt_one (hp : 2 ≤ p) {n : ℕ} (hn : 0 < n) :
    ((p : ℝ)⁻¹) ^ n < 1 :=
  pow_lt_one₀ (inv_base_pos hp).le (inv_base_lt_one hp) (Nat.ne_of_gt hn)

theorem term_nonneg (p n : ℕ) : 0 ≤ term p n := by
  unfold term
  positivity

theorem term_pos (hp : 2 ≤ p) (n : ℕ) : 0 < term p (n + 1) := by
  unfold term
  have : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  positivity

/-- The positive series is bounded term by term by a differentiated geometric series. -/
theorem term_le (hp : 2 ≤ p) (n : ℕ) :
    term p n ≤ (n : ℝ) * ((p : ℝ)⁻¹) ^ n := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hpow : 0 < (p : ℝ) ^ n := pow_pos hp0 _
  unfold term
  calc (n : ℝ) * (p : ℝ) ^ n / ((p : ℝ) ^ (2 * n) + 1)
      ≤ (n : ℝ) * (p : ℝ) ^ n / (p : ℝ) ^ (2 * n) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    _ = (n : ℝ) * ((p : ℝ)⁻¹) ^ n := by
      rw [inv_pow, mul_comm 2 n, pow_mul, pow_two]
      field_simp

theorem summable_term_all (hp : 2 ≤ p) : Summable (term p) := by
  have hr : ‖(p : ℝ)⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_base_pos hp)]
    exact inv_base_lt_one hp
  have hs : Summable (fun n : ℕ => (n : ℝ) * ((p : ℝ)⁻¹) ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  exact Summable.of_nonneg_of_le (term_nonneg p) (term_le hp) hs

theorem summable_term (hp : 2 ≤ p) : Summable (fun n : ℕ => term p (n + 1)) :=
  (summable_nat_add_iff 1).mpr (summable_term_all hp)

/-- `xi` has the intended convergent-series value; there is no default `tsum` value. -/
theorem hasSum_xi (hp : 2 ≤ p) : HasSum (fun n : ℕ => term p (n + 1)) (xi p) :=
  (summable_term hp).hasSum

theorem xi_pos (hp : 2 ≤ p) : 0 < xi p :=
  (summable_term hp).tsum_pos (fun n => term_nonneg p (n + 1)) 0 (term_pos hp 0)

/-- Equality with the reciprocal-parameter normalization in Jouhet--Mosaki. -/
theorem term_reciprocal (hp : 2 ≤ p) (n : ℕ) :
    term p n = (n : ℝ) * ((p : ℝ)⁻¹) ^ n / (1 + ((p : ℝ)⁻¹) ^ (2 * n)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hd : 1 + ((p : ℝ)⁻¹) ^ (2 * n) ≠ 0 := by positivity
  unfold term
  rw [inv_pow, inv_pow]
  field_simp
  rw [mul_comm 2 n, pow_mul]

theorem hasSum_reciprocal (hp : 2 ≤ p) :
    HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ((p : ℝ)⁻¹) ^ (n + 1) /
      (1 + ((p : ℝ)⁻¹) ^ (2 * (n + 1)))) (xi p) := by
  apply (hasSum_xi hp).congr_fun
  intro n
  exact (term_reciprocal hp (n + 1)).symm

@[simp] theorem chi_even (n : ℕ) : chi (2 * n) = 0 := by simp [chi]

@[simp] theorem chi_odd (n : ℕ) : chi (2 * n + 1) = (-1 : ℤ) ^ n := by
  simp [chi, Nat.add_div]

/-- The character shift used in every simple-pole moment. -/
theorem chi_shift (n a : ℕ) : chi (n + 2 * a) = (-1 : ℤ) ^ a * chi n := by
  unfold chi
  have hmod : (n + 2 * a) % 2 = n % 2 := by omega
  have hdiv : (n + 2 * a) / 2 = n / 2 + a := by omega
  rw [hmod, hdiv]
  split_ifs <;> simp [pow_add, mul_comm]

theorem abs_chi_le (n : ℕ) : |(chi n : ℝ)| ≤ 1 := by
  unfold chi
  split_ifs <;> simp

/-- The even-order rational kernel is invariant under reciprocal inversion. -/
theorem g2_inv {y : ℚ} (hy0 : y ≠ 0) (hy1 : y ≠ 1) : g2 y⁻¹ = g2 y := by
  unfold g2
  have h1 : (1 : ℚ) - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy1)
  have h2 : (1 : ℚ) - y⁻¹ ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    apply hy1
    rw [← inv_inv y, ← h, inv_one]
  field_simp
  ring

theorem S_eq_reciprocal (hp : 2 ≤ p) (N : ℕ) :
    S p N = ∑ b ∈ Icc 1 N, (chi b : ℚ) * g2 (((p : ℚ) ^ b)⁻¹) := by
  unfold S
  refine Finset.sum_congr rfl fun b hb => ?_
  have hb0 : 0 < b := (Finset.mem_Icc.mp hb).1
  have hp1 : (1 : ℚ) < (p : ℚ) ^ b :=
    one_lt_pow₀ (by exact_mod_cast (show 1 < p by omega)) (Nat.ne_of_gt hb0)
  rw [g2_inv (ne_of_gt (lt_trans zero_lt_one hp1)) (ne_of_gt hp1)]

/-- Euler differentiation on the real variable. -/
noncomputable def theta (f : ℝ → ℝ) (x : ℝ) : ℝ := x * deriv f x

/-- The manuscript's signed first-derivative functional. -/
noncomputable def Lfun (p : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∑' m : ℕ, (chi (m + 1) : ℝ) * theta f (((p : ℝ)⁻¹) ^ (m + 1))

/-- Exact summation of the character-weighted geometric series. -/
theorem hasSum_character_geometric {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun m : ℕ => (chi m : ℝ) * r ^ m) (r / (1 + r ^ 2)) := by
  have hnorm : ‖-(r ^ 2)‖ < 1 := by
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg r)]
    exact pow_lt_one₀ hr0 hr1 (by decide)
  have ho : HasSum (fun m : ℕ => (chi (2 * m + 1) : ℝ) * r ^ (2 * m + 1))
      (r / (1 + r ^ 2)) := by
    convert (hasSum_geometric_of_norm_lt_one hnorm).mul_left r using 1
    · ext m
      rw [chi_odd]
      push_cast
      rw [pow_add, pow_one, pow_mul, neg_eq_neg_one_mul, mul_pow]
      ring
    · simp [div_eq_mul_inv]
  have he : HasSum (fun m : ℕ => (chi (2 * m) : ℝ) * r ^ (2 * m)) 0 := by
    simp only [chi_even, Int.cast_zero, zero_mul]
    exact hasSum_zero
  simpa only [zero_add] using he.even_add_odd (f := fun m : ℕ => (chi m : ℝ) * r ^ m) ho

theorem hasSum_character_geometric_shift {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun m : ℕ => (chi (m + 1) : ℝ) * r ^ (m + 1)) (r / (1 + r ^ 2)) := by
  apply (hasSum_nat_add_iff (f := fun m : ℕ => (chi m : ℝ) * r ^ m) 1).mpr
  simpa [chi] using hasSum_character_geometric hr0 hr1

theorem theta_monomial (j : ℕ) (x : ℝ) :
    theta (fun y : ℝ => y ^ j) x = (j : ℝ) * x ^ j := by
  cases j with
  | zero => simp [theta]
  | succ j =>
    rw [theta, (hasDerivAt_pow (j + 1) x).deriv]
    simp only [Nat.add_sub_cancel, pow_succ]
    ring

/-- The constant moment vanishes, including at `j = 0`. -/
theorem mu_zero (p : ℕ) : mu p 0 = 0 := by simp [mu]

/-- Every polynomial monomial has the explicit rational moment in equation (1.4). -/
theorem hasSum_monomial (hp : 2 ≤ p) (j : ℕ) :
    HasSum (fun m : ℕ => (chi (m + 1) : ℝ) *
      theta (fun x : ℝ => x ^ j) (((p : ℝ)⁻¹) ^ (m + 1))) (mu p j : ℝ) := by
  by_cases hj : j = 0
  · subst j
    simp only [theta_monomial, Nat.cast_zero, zero_mul, mul_zero, mu_zero, Rat.cast_zero]
    exact hasSum_zero
  · have hgeom := (hasSum_character_geometric_shift
      (pow_nonneg (inv_base_pos hp).le j) (inv_base_pow_lt_one hp (Nat.pos_of_ne_zero hj))).mul_left (j : ℝ)
    convert hgeom using 1
    · ext m
      rw [theta_monomial, ← pow_mul, ← pow_mul, Nat.mul_comm j (m + 1)]
      ring
    · unfold mu
      push_cast
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
      have hd : (0 : ℝ) < 1 + (p : ℝ) ^ (2 * j) := by positivity
      have hi : (0 : ℝ) < 1 + (((p : ℝ)⁻¹) ^ j) ^ 2 := by positivity
      rw [inv_pow]
      field_simp
      rw [mul_comm 2 j, pow_mul]
      ring

/-- The kernel after one Euler derivative. -/
noncomputable def poleKernel (p b : ℕ) : ℝ :=
  ((p : ℝ)⁻¹) ^ b / (1 - ((p : ℝ)⁻¹) ^ b) ^ 2

theorem theta_inv_affine {c x : ℝ} (hx : 1 - c * x ≠ 0) :
    theta (fun y => (1 - c * y)⁻¹) x = c * x / (1 - c * x) ^ 2 := by
  exact QZeta3.theta_inv_affine hx

/-- The signed geometric double series is absolutely summable. -/
theorem summable_signed_lattice (hp : 2 ≤ p) :
    Summable (fun nm : ℕ × ℕ => (chi (nm.2 + 1) : ℝ) * ((nm.1 + 1 : ℕ) : ℝ) *
      ((p : ℝ)⁻¹) ^ ((nm.1 + 1) * (nm.2 + 1))) := by
  let f : ℕ × ℕ → ℝ := fun nm => ((nm.1 + 1 : ℕ) : ℝ) ^ 2 *
    ((p : ℝ)⁻¹) ^ ((nm.1 + 1) * (nm.2 + 1))
  have hf : Summable f := by
    apply (summable_prod_of_nonneg (fun nm => by dsimp [f]; positivity)).mpr
    constructor
    · intro n
      exact (QZeta3.hasSum_geometric_lattice_row hp n).summable
    · convert QZeta3.summable_term hp using 1
      ext n
      exact (QZeta3.hasSum_geometric_lattice_row hp n).tsum_eq
  apply Summable.of_norm_bounded hf
  intro nm
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_natCast,
    Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ ((p : ℝ)⁻¹) ^ ((nm.1 + 1) * (nm.2 + 1)) by positivity)]
  dsimp [f]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hn : (1 : ℝ) ≤ (nm.1 + 1 : ℕ) := by exact_mod_cast (show 1 ≤ nm.1 + 1 by omega)
  have hc := abs_chi_le (nm.2 + 1)
  calc |(chi (nm.2 + 1) : ℝ)| * ((nm.1 + 1 : ℕ) : ℝ)
      ≤ 1 * ((nm.1 + 1 : ℕ) : ℝ) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ ≤ ((nm.1 + 1 : ℕ) : ℝ) ^ 2 := by nlinarith

theorem hasSum_signed_lattice_row (hp : 2 ≤ p) (n : ℕ) :
    HasSum (fun m : ℕ => (chi (m + 1) : ℝ) * ((n + 1 : ℕ) : ℝ) *
      ((p : ℝ)⁻¹) ^ ((n + 1) * (m + 1))) (term p (n + 1)) := by
  have hs := hasSum_monomial hp (n + 1)
  convert hs using 1
  · ext m
    rw [theta_monomial, ← pow_mul, Nat.mul_comm (m + 1) (n + 1)]
    ring
  · simp only [term, mu, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_add,
      Rat.cast_natCast, Rat.cast_one]
    rw [add_comm 1]

theorem hasSum_signed_lattice_column (hp : 2 ≤ p) (m : ℕ) :
    HasSum (fun n : ℕ => (chi (m + 1) : ℝ) * ((n + 1 : ℕ) : ℝ) *
      ((p : ℝ)⁻¹) ^ ((n + 1) * (m + 1)))
      ((chi (m + 1) : ℝ) * poleKernel p (m + 1)) := by
  have hr : ‖((p : ℝ)⁻¹) ^ (m + 1)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact inv_base_pow_lt_one hp (by omega)
  have hs := hasSum_coe_mul_geometric_of_norm_lt_one hr
  have hshift : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) *
      (((p : ℝ)⁻¹) ^ (m + 1)) ^ (n + 1)) (poleKernel p (m + 1)) := by
    apply (hasSum_nat_add_iff (f := fun n : ℕ => (n : ℝ) *
      (((p : ℝ)⁻¹) ^ (m + 1)) ^ n) 1).mpr
    simpa [poleKernel] using hs
  convert hshift.mul_left (chi (m + 1) : ℝ) using 1
  ext n
  rw [← pow_mul, Nat.mul_comm (m + 1) (n + 1)]
  ring

/-- Fubini identifies the signed pole-kernel series with the actual target. -/
theorem hasSum_poleKernel (hp : 2 ≤ p) :
    HasSum (fun m : ℕ => (chi (m + 1) : ℝ) * poleKernel p (m + 1)) (xi p) := by
  let f : ℕ × ℕ → ℝ := fun nm => (chi (nm.2 + 1) : ℝ) * ((nm.1 + 1 : ℕ) : ℝ) *
    ((p : ℝ)⁻¹) ^ ((nm.1 + 1) * (nm.2 + 1))
  have hf : Summable f := summable_signed_lattice hp
  have heq : (fun m : ℕ => ∑' n : ℕ, f (n, m)) =
      (fun m : ℕ => (chi (m + 1) : ℝ) * poleKernel p (m + 1)) := by
    funext m
    exact (hasSum_signed_lattice_column hp m).tsum_eq
  have hsum : Summable (fun m : ℕ => (chi (m + 1) : ℝ) * poleKernel p (m + 1)) := by
    rw [← heq]
    exact hf.prod_symm.prod
  convert hsum.hasSum using 1
  have hcomm := Summable.tsum_comm (f := fun n m : ℕ => f (n, m)) hf
  rw [← heq, hcomm]
  unfold xi
  congr 1
  funext n
  exact (hasSum_signed_lattice_row hp n).tsum_eq.symm

/-- The rational tail in the formal data is the finite real kernel sum. -/
theorem S_cast_eq_sum_poleKernel (hp : 2 ≤ p) (N : ℕ) :
    (S p N : ℝ) = ∑ m ∈ range N, (chi (m + 1) : ℝ) * poleKernel p (m + 1) := by
  have hI : (S p N : ℝ) = ∑ b ∈ Icc 1 N, (chi b : ℝ) * poleKernel p b := by
    rw [S_eq_reciprocal hp]
    simp only [Rat.cast_sum, g2, poleKernel, Rat.cast_div, Rat.cast_mul,
      Rat.cast_sub, Rat.cast_pow, Rat.cast_inv, Rat.cast_one, Rat.cast_intCast,
      Rat.cast_natCast, inv_pow]
  rw [hI]
  clear hI
  induction N with
  | zero => simp
  | succ N ih => rw [sum_Icc_succ_top (by omega), sum_range_succ, ih]

/-- The exact signed simple-pole identity (equation (1.5)), as a convergent sum. -/
theorem hasSum_simplePole (hp : 2 ≤ p) (a : ℕ) :
    HasSum (fun m : ℕ => (chi (m + 1) : ℝ) * theta
      (fun x => (1 - ((p : ℝ)⁻¹) ^ (2 * a) * x)⁻¹)
      (((p : ℝ)⁻¹) ^ (m + 1)))
      ((-1 : ℝ) ^ a * (xi p - (S p (2 * a) : ℝ))) := by
  let f : ℕ → ℝ := fun m => (chi (m + 1) : ℝ) * poleKernel p (m + 1)
  have hf : HasSum f (xi p) := hasSum_poleKernel hp
  have ht : HasSum (fun m => f (m + 2 * a)) (xi p - (S p (2 * a) : ℝ)) := by
    have htail := (hasSum_nat_add_iff (f := f) (2 * a)).mpr
      (show HasSum f ((xi p - ∑ i ∈ range (2 * a), f i) +
        ∑ i ∈ range (2 * a), f i) by simpa using hf)
    simpa only [f, ← S_cast_eq_sum_poleKernel hp] using htail
  apply (ht.mul_left ((-1 : ℝ) ^ a)).congr_fun
  intro m
  have hx : 1 - ((p : ℝ)⁻¹) ^ (2 * a) * ((p : ℝ)⁻¹) ^ (m + 1) ≠ 0 := by
    rw [← pow_add]
    exact ne_of_gt (sub_pos.mpr (inv_base_pow_lt_one hp (by omega)))
  rw [theta_inv_affine hx]
  have hindex : m + 2 * a + 1 = (m + 1) + 2 * a := by omega
  have hpow : 2 * a + (m + 1) = (m + 1) + 2 * a := by omega
  simp only [f, poleKernel, hindex, chi_shift, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one, ← pow_add, hpow]
  have hsign : (-1 : ℝ) ^ a * (-1) ^ a = 1 := by rw [← mul_pow]; norm_num
  simp only [mul_assoc, ← mul_assoc ((-1 : ℝ) ^ a) ((-1 : ℝ) ^ a), hsign, one_mul]

theorem Lfun_simplePole (hp : 2 ≤ p) (a : ℕ) :
    Lfun p (fun x => (1 - ((p : ℝ)⁻¹) ^ (2 * a) * x)⁻¹) =
      (-1 : ℝ) ^ a * (xi p - (S p (2 * a) : ℝ)) :=
  (hasSum_simplePole hp a).tsum_eq

theorem theta_add {f g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    theta (f + g) x = theta f x + theta g x := by
  simp only [theta, deriv_add hf hg, mul_add]

theorem theta_const_mul {f : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (c : ℝ) :
    theta (fun y => c * f y) x = c * theta f x := by
  simp only [theta, deriv_const_mul c hf]
  ring

theorem theta_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) {x : ℝ}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) :
    theta (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, theta (f i) x := by
  simp only [theta, deriv_fun_sum hf, Finset.mul_sum]

theorem hasSum_functional_sum {p : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (v : ι → ℝ)
    (hf : ∀ i ∈ s, ∀ m : ℕ, DifferentiableAt ℝ (f i) (((p : ℝ)⁻¹) ^ (m + 1)))
    (hs : ∀ i ∈ s, HasSum (fun m : ℕ => (chi (m + 1) : ℝ) * theta (f i)
      (((p : ℝ)⁻¹) ^ (m + 1))) (v i)) :
    HasSum (fun m : ℕ => (chi (m + 1) : ℝ) * theta (fun x => ∑ i ∈ s, f i x)
      (((p : ℝ)⁻¹) ^ (m + 1))) (∑ i ∈ s, v i) := by
  apply (hasSum_sum hs).congr_fun
  intro m
  rw [theta_sum s f (fun i hi => hf i hi m), Finset.mul_sum]

theorem hasSum_functional_const_mul {p : ℕ} {f : ℝ → ℝ} {v : ℝ}
    (hf : ∀ m : ℕ, DifferentiableAt ℝ f (((p : ℝ)⁻¹) ^ (m + 1)))
    (hs : HasSum (fun m : ℕ => (chi (m + 1) : ℝ) * theta f
      (((p : ℝ)⁻¹) ^ (m + 1))) v) (c : ℝ) :
    HasSum (fun m : ℕ => (chi (m + 1) : ℝ) * theta (fun x => c * f x)
      (((p : ℝ)⁻¹) ^ (m + 1))) (c * v) := by
  apply (hs.mul_left c).congr_fun
  intro m
  rw [theta_const_mul (hf m) c]
  ring

/-- All rational polynomial moments agree with the actual signed functional. -/
theorem hasSum_polynomial (hp : 2 ≤ p) (P : ℚ[X]) :
    HasSum (fun m : ℕ => (chi (m + 1) : ℝ) *
      theta (fun x => P.eval₂ (Rat.castHom ℝ) x) (((p : ℝ)⁻¹) ^ (m + 1)))
      (Lpoly p P : ℝ) := by
  simp only [eval₂_eq_sum, Polynomial.sum_def]
  have hs := hasSum_functional_sum P.support
    (fun j x => (P.coeff j : ℝ) * x ^ j) (fun j => (P.coeff j : ℝ) * (mu p j : ℝ))
    (fun j _ m => (differentiableAt_id.pow j).const_mul _)
    (fun j _ => hasSum_functional_const_mul (fun _ => differentiableAt_id.pow j)
      (hasSum_monomial hp j) (P.coeff j : ℝ))
  simpa only [Lpoly, Rat.cast_sum, Rat.cast_mul, Rat.coe_castHom] using hs

/-- Once convergent, the functional can equivalently be indexed only by odd lattice nodes. -/
theorem Lfun_eq_odd {p : ℕ} (f : ℝ → ℝ)
    (hs : Summable (fun m : ℕ => (chi (m + 1) : ℝ) *
      theta f (((p : ℝ)⁻¹) ^ (m + 1)))) :
    Lfun p f = ∑' n : ℕ, (-1 : ℝ) ^ n *
      theta f (((p : ℝ)⁻¹) ^ (2 * n + 1)) := by
  let F : ℕ → ℝ := fun m => (chi m : ℝ) * theta f (((p : ℝ)⁻¹) ^ m)
  have hF : Summable F := (summable_nat_add_iff 1).mp hs
  have he : Summable (fun n : ℕ => F (2 * n)) := by
    simp only [F, chi_even, Int.cast_zero, zero_mul]
    exact summable_zero
  have ho : Summable (fun n : ℕ => F (2 * n + 1)) :=
    hF.comp_injective (fun m n h => by omega)
  have hdecomp := tsum_even_add_odd (f := F) he ho
  have hzero : F 0 = 0 := by simp [F, chi]
  rw [hF.tsum_eq_zero_add, hzero, zero_add] at hdecomp
  simpa only [F, Lfun, chi_even, chi_odd, Int.cast_zero, zero_mul, tsum_zero, zero_add,
    Int.cast_pow, Int.cast_neg, Int.cast_one] using hdecomp.symm

theorem hasSum_functional_add {p : ℕ} {f g : ℝ → ℝ} {v w : ℝ}
    (hf : ∀ m : ℕ, DifferentiableAt ℝ f (((p : ℝ)⁻¹) ^ (m + 1)))
    (hg : ∀ m : ℕ, DifferentiableAt ℝ g (((p : ℝ)⁻¹) ^ (m + 1)))
    (hs : HasSum (fun m : ℕ => (chi (m + 1) : ℝ) * theta f
      (((p : ℝ)⁻¹) ^ (m + 1))) v)
    (ht : HasSum (fun m : ℕ => (chi (m + 1) : ℝ) * theta g
      (((p : ℝ)⁻¹) ^ (m + 1))) w) :
    HasSum (fun m : ℕ => (chi (m + 1) : ℝ) * theta (f + g)
      (((p : ℝ)⁻¹) ^ (m + 1))) (v + w) := by
  apply (hs.add ht).congr_fun
  intro m
  rw [theta_add (hf m) (hg m), mul_add]

theorem hasSum_functional_congr {p : ℕ} {f g : ℝ → ℝ} {v : ℝ}
    (he : ∀ m : ℕ, f =ᶠ[𝓝 (((p : ℝ)⁻¹) ^ (m + 1))] g)
    (hs : HasSum (fun m : ℕ => (chi (m + 1) : ℝ) * theta g
      (((p : ℝ)⁻¹) ^ (m + 1))) v) :
    HasSum (fun m : ℕ => (chi (m + 1) : ℝ) * theta f
      (((p : ℝ)⁻¹) ^ (m + 1))) v := by
  apply hs.congr_fun
  intro m
  simp only [theta, (he m).deriv_eq]

theorem contDiffAt_ratPolynomial (P : ℚ[X]) (x : ℝ) :
    ContDiffAt ℝ 2 (fun y => P.eval₂ (Rat.castHom ℝ) y) x := by
  simp only [eval₂_eq_sum, Polynomial.sum_def]
  apply ContDiffAt.sum
  intro j hj
  exact contDiffAt_const.mul (contDiffAt_id.pow j)

theorem contDiffAt_simplePole {p a : ℕ} (hp : 2 ≤ p) (m : ℕ) :
    ContDiffAt ℝ 2 (fun x => (1 - ((p : ℝ)⁻¹) ^ (2 * a) * x)⁻¹)
      (((p : ℝ)⁻¹) ^ (m + 1)) := by
  have hn : 1 - ((p : ℝ)⁻¹) ^ (2 * a) * ((p : ℝ)⁻¹) ^ (m + 1) ≠ 0 := by
    rw [← pow_add]
    exact ne_of_gt (sub_pos.mpr (inv_base_pow_lt_one hp (by omega)))
  exact (contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id)).inv hn

end QCatalan
