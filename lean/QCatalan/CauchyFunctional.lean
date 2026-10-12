import QCatalan.CauchyAtInfinity

open Finset Filter Topology
namespace QCatalan

noncomputable abbrev cauchyF (p : ℕ) (z : ℝ) : ℝ := cauchySeries p z

/-- The first Euler derivative of the Cauchy kernel, away from its pole. -/
theorem theta_inv_sub (z x : ℝ) (hx : x ≠ z) :
    theta (fun y : ℝ => (z-y)⁻¹) x = x/(z-x)^2 := by
  have hzx : z-x ≠ 0 := sub_ne_zero.mpr hx.symm
  have h1 : HasDerivAt (fun y : ℝ => z-y) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub z
  have h2 : HasDerivAt (fun y : ℝ => (z-y)⁻¹) (-(-1)/(z-x)^2) x := h1.inv hzx
  rw [theta, h2.deriv]
  simp only [neg_neg, one_div]
  rfl

/-- The series Cauchy transform is precisely the signed derivative functional. -/
theorem cauchyF_eq (p : ℕ) (z : ℝ) (hz : ∀ m : ℕ, z ≠ ((p:ℝ)⁻¹)^(m+1)) :
    cauchyF p z = Lfun p (fun x => (z-x)⁻¹) := by
  unfold cauchyF cauchySeries Lfun
  refine tsum_congr fun m => ?_
  rw [theta_inv_sub z _ (hz m).symm]
  ring

end QCatalan
