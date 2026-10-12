import QCatalan.CauchyExterior

open Filter Topology Finset
namespace QCatalan

noncomputable def cauchyKernel (p n : ℕ) (z : ℝ) : ℝ :=
  (chi (n+1) : ℝ) * ((p : ℝ)⁻¹)^(n+1) / (z - ((p : ℝ)⁻¹)^(n+1))^2

theorem summable_cauchyKernel_of_gt_q {p : ℕ} (hp : 2 ≤ p) {z : ℝ}
    (hz : (p : ℝ)⁻¹ < z) : Summable (fun n : ℕ => cauchyKernel p n z) := by
  let q := (p : ℝ)⁻¹
  have hq0 : 0 < q := inv_base_pos hp
  have hq1 : q < 1 := inv_base_lt_one hp
  have hg : Summable (fun n : ℕ => q^(n+1)) :=
    (summable_nat_add_iff (f := fun n : ℕ => q^n) 1).mpr
      (hasSum_geometric_of_lt_one hq0.le hq1).summable
  apply Summable.of_norm_bounded (hg.mul_right ((z-q)^2)⁻¹)
  intro n
  have hqn : 0 < q^(n+1) := pow_pos hq0 _
  have hqnq : q^(n+1) ≤ q := by
    simpa only [pow_one] using pow_le_pow_of_le_one hq0.le hq1.le (show 1 ≤ n+1 by omega)
  have hdz : 0 < z-q^(n+1) := by linarith
  change |(chi (n+1):ℝ)*q^(n+1)/(z-q^(n+1))^2| ≤ _
  rw [abs_div, abs_mul, abs_of_pos hqn, abs_of_pos (sq_pos_of_pos hdz)]
  calc |(chi (n+1):ℝ)| * q^(n+1) / (z-q^(n+1))^2
      ≤ q^(n+1) / (z-q^(n+1))^2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        simpa using mul_le_mul_of_nonneg_right (abs_chi_le (n+1)) hqn.le
    _ ≤ q^(n+1) / (z-q)^2 := by
      apply div_le_div_of_nonneg_left hqn.le (by positivity)
      exact pow_le_pow_left₀ (by linarith) (by linarith) 2
    _ = q^(n+1) * ((z-q)^2)⁻¹ := div_eq_mul_inv _ _

/-- An even shift preserves the character up to its exact alternating sign. -/
theorem cauchyKernel_shift_even {p : ℕ} (hp : 2 ≤ p) (N n : ℕ) (z : ℝ) :
    cauchyKernel p (n+2*N) z = (-1:ℝ)^N * (((p:ℝ)⁻¹)^(2*N))⁻¹ *
      cauchyKernel p n (z / ((p:ℝ)⁻¹)^(2*N)) := by
  let t := ((p:ℝ)⁻¹)^(2*N)
  let a := ((p:ℝ)⁻¹)^(n+1)
  have ht : t ≠ 0 := ne_of_gt (pow_pos (inv_base_pos hp) _)
  have hpow : ((p:ℝ)⁻¹)^((n+1)+2*N) = t*a := by
    dsimp [t, a]; rw [← pow_add]; congr 1; omega
  have hindex : n+2*N+1 = (n+1)+2*N := by omega
  have hminus : z-t*a = t*(z/t-a) := by field_simp
  simp only [cauchyKernel, hindex, hpow, chi_shift, Int.cast_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one]
  change ((-1:ℝ)^N * (chi (n+1):ℝ))*(t*a)/(z-t*a)^2 =
    (-1:ℝ)^N*t⁻¹*((chi (n+1):ℝ)*a/(z/t-a)^2)
  rw [hminus, mul_pow]
  simp only [div_eq_mul_inv, mul_inv]
  field_simp [ht]

theorem cauchySeries_tail_even {p : ℕ} (hp : 2 ≤ p) (N : ℕ) (z : ℝ) :
    (∑' n : ℕ, cauchyKernel p (n+2*N) z) =
      (-1:ℝ)^N * (((p:ℝ)⁻¹)^(2*N))⁻¹ * cauchySeries p (z / ((p:ℝ)⁻¹)^(2*N)) := by
  simp_rw [cauchyKernel_shift_even hp]
  rw [tsum_mul_left]
  rfl

theorem cauchySeries_split_even {p : ℕ} (hp : 2 ≤ p) (N : ℕ) (z : ℝ)
    (hs : Summable (fun n : ℕ => cauchyKernel p n (z / ((p:ℝ)⁻¹)^(2*N)))) :
    cauchySeries p z = (∑ n ∈ range (2*N), cauchyKernel p n z) +
      (-1:ℝ)^N * (((p:ℝ)⁻¹)^(2*N))⁻¹ * cauchySeries p (z / ((p:ℝ)⁻¹)^(2*N)) := by
  have htail : Summable (fun n : ℕ => cauchyKernel p (n+2*N) z) := by
    simp only [cauchyKernel_shift_even hp]
    exact hs.mul_left _
  have hall : Summable (fun n : ℕ => cauchyKernel p n z) :=
    (summable_nat_add_iff (f := fun n : ℕ => cauchyKernel p n z) (2*N)).mp htail
  have heq := hall.sum_add_tsum_nat_add (2*N)
  rw [cauchySeries_tail_even hp N z] at heq
  exact heq.symm

/-- Each odd support point is a genuine double pole with its signed nonzero residue. -/
theorem cauchySeries_double_pole {p : ℕ} (hp : 2 ≤ p) (m : ℕ) :
    Tendsto (fun z : ℝ => (z-((p:ℝ)⁻¹)^(2*m+1))^2 * cauchySeries p z)
      (𝓝[≠] (((p:ℝ)⁻¹)^(2*m+1)))
      (𝓝 ((-1:ℝ)^m * ((p:ℝ)⁻¹)^(2*m+1))) := by
  let q := (p:ℝ)⁻¹
  let r := q^(2*m+1)
  let t := q^(2*(m+1))
  let s := (range (2*(m+1))).erase (2*m)
  let R : ℝ → ℝ := fun z => (∑ n ∈ s, cauchyKernel p n z) +
    (-1:ℝ)^(m+1)*t⁻¹*cauchySeries p (z/t)
  have hq0 : 0 < q := inv_base_pos hp
  have hq1 : q < 1 := inv_base_lt_one hp
  have ht : t ≠ 0 := ne_of_gt (pow_pos hq0 _)
  have hscale : r/t = (p:ℝ) := by
    have hpw : t = r*q := by dsimp [r,t]; rw [show 2*(m+1) = (2*m+1)+1 by omega, pow_succ]
    rw [hpw, div_mul_eq_div_div, div_self (ne_of_gt (pow_pos hq0 _)), one_div]
    exact inv_inv (p:ℝ)
  have hp1 : (1:ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hhead : ContinuousAt (fun z => ∑ n ∈ s, cauchyKernel p n z) r := by
    apply tendsto_finsetSum
    intro n hn
    have hnm : n ≠ 2*m := (mem_erase.mp hn).1
    have hdiff : r-q^(n+1) ≠ 0 := by
      apply sub_ne_zero.mpr
      intro heq
      have hmn := pow_right_injective₀ hq0 (ne_of_lt hq1) heq
      exact hnm (by omega)
    exact continuousAt_const.div ((continuousAt_id.sub continuousAt_const).pow 2)
      (pow_ne_zero 2 hdiff)
  have htail : ContinuousAt (fun z => (-1:ℝ)^(m+1)*t⁻¹*cauchySeries p (z/t)) r := by
    have hf : ContinuousAt (cauchySeries p) (r/t) := by
      rw [hscale]
      exact (analyticAt_cauchySeries_of_gt_one hp hp1).continuousAt
    exact continuousAt_const.mul (hf.comp (f := fun z : ℝ => z/t) (x := r) (continuousAt_id.div_const t))
  have hR : ContinuousAt R r := hhead.add htail
  have hnear : ∀ᶠ z : ℝ in 𝓝 r, q < z/t :=
    continuousAt_const.eventually_lt
      (show ContinuousAt (fun z : ℝ => z/t) r from continuousAt_id.div_const t)
      (by rw [hscale]; linarith)
  have hsplit : ∀ᶠ z : ℝ in 𝓝 r, cauchySeries p z = cauchyKernel p (2*m) z + R z := by
    filter_upwards [hnear] with z hz
    rw [cauchySeries_split_even hp (m+1) z (summable_cauchyKernel_of_gt_q hp hz)]
    rw [← Finset.sum_erase_add (range (2*(m+1))) (fun n => cauchyKernel p n z)
      (a := 2*m) (by simp)]
    dsimp [R,s,t]
    ring
  have hlim : Tendsto (fun z : ℝ => (-1:ℝ)^m*r + (z-r)^2*R z)
      (𝓝 r) (𝓝 ((-1:ℝ)^m*r)) := by
    have hc : ContinuousAt (fun z : ℝ => (-1:ℝ)^m*r + (z-r)^2*R z) r :=
      continuousAt_const.add (((continuousAt_id.sub continuousAt_const).pow 2).mul hR)
    simpa using hc.tendsto
  apply (hlim.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [hsplit.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzr
  have hzr' : z-r ≠ 0 := sub_ne_zero.mpr (by simpa only [r,q,inv_pow,Set.mem_compl_iff,Set.mem_singleton_iff] using hzr)
  rw [hz]
  simp only [cauchyKernel, chi_odd, Int.cast_pow, Int.cast_neg, Int.cast_one]
  change (-1:ℝ)^m*r + (z-r)^2*R z = (z-r)^2*((-1:ℝ)^m*r/(z-r)^2 + R z)
  field_simp

end QCatalan
