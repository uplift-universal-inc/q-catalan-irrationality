import QCatalan.CauchyPole
import QZeta3.CauchyMeromorphic

open Filter Topology Polynomial
namespace QCatalan

theorem meromorphicAt_cauchyKernel (p n : ℕ) (z : ℝ) :
    MeromorphicAt (cauchyKernel p n) z := by
  unfold cauchyKernel
  exact (MeromorphicAt.const _ z).div
    (((MeromorphicAt.id z).sub (MeromorphicAt.const _ z)).pow 2)

/-- The even-shift identity provides a finite rational head and analytic tail
near every positive real point, including the odd support points. -/
theorem meromorphicOn_cauchySeries_pos {p : ℕ} (hp : 2 ≤ p) :
    MeromorphicOn (cauchySeries p) (Set.Ioi 0) := by
  intro z hz
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hz (inv_base_lt_one hp)
  have hN' : ((p:ℝ)⁻¹)^(2*N) < z :=
    lt_of_le_of_lt (pow_le_pow_of_le_one (inv_base_pos hp).le
      (inv_base_lt_one hp).le (by omega : N ≤ 2*N)) hN
  let t := ((p:ℝ)⁻¹)^(2*N)
  have ht : 0 < t := pow_pos (inv_base_pos hp) _
  have hzt : 1 < z/t := (lt_div_iff₀ ht).mpr (by simpa [t] using hN')
  have hhead : MeromorphicAt
      (fun y : ℝ => ∑ n ∈ Finset.range (2*N), cauchyKernel p n y) z :=
    MeromorphicAt.fun_sum (fun n _ => meromorphicAt_cauchyKernel p n z)
  have hscale : AnalyticAt ℝ (fun y : ℝ => y/t) z := analyticAt_id.div_const
  have htail : AnalyticAt ℝ (fun y : ℝ => (-1:ℝ)^N*t⁻¹*cauchySeries p (y/t)) z :=
    analyticAt_const.mul ((analyticAt_cauchySeries_of_gt_one hp hzt).comp
      (f := fun y : ℝ => y/t) hscale)
  apply (hhead.add htail.meromorphicAt).congr
  have hn : ∀ᶠ y : ℝ in 𝓝 z, t < y := eventually_gt_nhds hN'
  filter_upwards [hn.filter_mono nhdsWithin_le_nhds] with y hy
  have hyt : (p:ℝ)⁻¹ < y/t := lt_trans (inv_base_lt_one hp)
    ((lt_div_iff₀ ht).mpr (by simpa using hy))
  exact (cauchySeries_split_even hp N y (summable_cauchyKernel_of_gt_q hp hyt)).symm

/-- A genuine second-order pole forces every denominator of a rational germ
identity to vanish at the pole. -/
theorem polynomial_root_of_double_pole {f : ℝ → ℝ} {a c : ℝ} (hc : c ≠ 0)
    (hpole : Tendsto (fun z : ℝ => (z-a)^2*f z) (𝓝[≠] a) (𝓝 c))
    (P Q : ℝ[X]) (heq : ∀ᶠ z : ℝ in 𝓝[≠] a, f z*Q.eval z-P.eval z=0) :
    Q.eval a = 0 := by
  have hQ : Tendsto (fun z : ℝ => Q.eval z) (𝓝[≠] a) (𝓝 (Q.eval a)) :=
    (QZeta3.analyticAt_polynomial_eval Q a).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hP : Tendsto (fun z : ℝ => P.eval z) (𝓝[≠] a) (𝓝 (P.eval a)) :=
    (QZeta3.analyticAt_polynomial_eval P a).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hz : Tendsto (fun z : ℝ => (z-a)^2) (𝓝[≠] a) (𝓝 0) := by
    convert ((tendsto_id.sub_const a).pow 2).mono_left nhdsWithin_le_nhds using 1 <;> simp
  have hlim : Tendsto (fun z : ℝ => (z-a)^2*(f z*Q.eval z-P.eval z))
      (𝓝[≠] a) (𝓝 (c*Q.eval a)) := by
    convert (hpole.mul hQ).sub (hz.mul hP) using 1
    · ext z; ring
    · simp
  have hlim0 : Tendsto (fun z : ℝ => (z-a)^2*(f z*Q.eval z-P.eval z))
      (𝓝[≠] a) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [heq] with z hz
    simp [hz]
  exact (mul_eq_zero.mp (tendsto_nhds_unique hlim hlim0)).resolve_left hc

/-- Infinitely many distinct odd geometric nodes force a polynomial to vanish. -/
theorem polynomial_eq_zero_of_odd_geometric_roots {p : ℕ} (hp : 2 ≤ p) (Q : ℝ[X])
    (hQ : ∀ n : ℕ, Q.eval (((p:ℝ)⁻¹)^(2*n+1)) = 0) : Q = 0 := by
  apply Q.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (f := fun n : Fin (Q.natDegree+1) => ((p:ℝ)⁻¹)^(2*n.val+1))
  · intro a b hab
    have hab' := (pow_right_strictAnti₀ (inv_base_pos hp) (inv_base_lt_one hp)).injective hab
    apply Fin.ext
    omega
  · intro n; exact hQ n.val
  · simp

/-- The actual signed Cauchy transform has no rational germ at infinity. -/
theorem cauchySeries_nonrational {p : ℕ} (hp : 2 ≤ p) (P Q : ℝ[X]) (hQ : Q ≠ 0) :
    ¬ ∀ᶠ x : ℝ in atTop, cauchySeries p x * Q.eval x - P.eval x = 0 := by
  intro hzero
  apply hQ
  apply polynomial_eq_zero_of_odd_geometric_roots hp Q
  intro m
  have hnode : 0 < ((p:ℝ)⁻¹)^(2*m+1) := pow_pos (inv_base_pos hp) _
  have herr : MeromorphicOn (fun x => cauchySeries p x * Q.eval x - P.eval x)
      (Set.Ioi 0) := by
    intro x hx
    exact (((meromorphicOn_cauchySeries_pos hp) x hx).mul
      (QZeta3.analyticAt_polynomial_eval Q x).meromorphicAt).sub
      (QZeta3.analyticAt_polynomial_eval P x).meromorphicAt
  have heq := QZeta3.meromorphicOn_Ioi_eventually_zero_of_atTop herr hzero hnode
  apply polynomial_root_of_double_pole (f := cauchySeries p)
    (c := (-1:ℝ)^m * ((p:ℝ)⁻¹)^(2*m+1)) _ (cauchySeries_double_pole hp m) P Q heq
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (ne_of_gt hnode)

end QCatalan
