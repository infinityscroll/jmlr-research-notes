import GaussianExteriorRoutingGeometry

/-! Actual local orbit-error payment and a simultaneously close, deficit-paid
regular reference. The infimum need not be assumed attained. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology RealInnerProductSpace Classical
namespace NegativeVotingLocalOrbitDeficitPayment
open NegativeVotingGlobalCovarianceDeficit NegativeVotingProcrustes
  NegativeVotingBalancedReference NegativeVotingRegularCovarianceDeficit
  NegativeVotingGaussianMaximumMean NegativeVotingGaussianMaximum
  NegativeVotingCentroidOptimization NegativeVotingExteriorRoutingGeometry
  NegativeVotingRegularSecondGap

lemma short_orbit_ray_payment (α d m L c R : ℝ)
    (hα : 0 < α) (hd : 0 ≤ d) (hdα : d ≤ α)
    (hm : 0 < m) (hL : 1 ≤ L) (hc : 0 < c) (hc1 : c ≤ 1) (hR : 0 ≤ R)
    (hbound : α^2*(d/α)^2/(48*m)*min 1 ((c/L)/(d/α)) ≤ R) :
    d^2 ≤ (48/c)*m*L*R := by
  by_cases hd0 : d=0
  · subst d
    simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0)]
    positivity
  have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
  have hq : 0 < d/α := div_pos hdpos hα
  have hq1 : d/α ≤ 1 := (div_le_one hα).mpr hdα
  have hL0 : 0 < L := by linarith
  have hcL : 0 < c/L := div_pos hc hL0
  have hmin : c/L ≤ min 1 ((c/L)/(d/α)) := by
    apply le_min
    · exact (div_le_one hL0).mpr (hc1.trans hL)
    · exact (le_div_iff₀ hq).mpr (by nlinarith)
  have heq : α^2*(d/α)^2/(48*m)=d^2/(48*m) := by field_simp
  rw [heq] at hbound
  have hh := (mul_le_mul_of_nonneg_left hmin (show 0 ≤ d^2/(48*m) by positivity)).trans hbound
  have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ 48*m*L/c by positivity)
  convert hh' using 1 <;> field_simp <;> ring

theorem eventually_local_orbit_payment :
    ∀ᶠ n : ℕ in atTop, ∀ (e:ℕ) (he:n+1 ≤ e)
      (B:Fin (n+2)→FSC.Coord e), (∑i,B i)=0 →
      0 ≤ regularCovarianceDeficit n B →
      regularOrbitDistance n B ≤ 1/((n:ℝ)+2) →
      (regularOrbitDistance n B)^2 ≤ (48/globalRadius)*((n:ℝ)+2)*
        (1+Real.log ((n:ℝ)+2))*regularCovarianceDeficit n B := by
  filter_upwards [eventually_uniform_global_orbit_bound,eventually_maximum_mean_sq_ge_one]
    with n hbound hmean
  intro e he B hB hR hlocal
  have hb := referenceBasis_spec n
  have hd := (regularOrbitDistance_nonneg_and_le (referenceBasis n) hb.2.1 hb.2.2
    (show n+2-1 ≤ e by omega) B hB).1
  have hα := referenceScale_pos n
  have hM : 1 ≤ maximumMean n :=
    (sq_le_sq₀ (by norm_num : (0:ℝ) ≤ 1) (maximumMean_pos n).le).mp (by simpa using hmean)
  have hαlower : 1/((n:ℝ)+2) ≤ referenceScale n := by
    unfold referenceScale
    calc
      _ ≤ 1/((n:ℝ)+1) := by gcongr;linarith
      _ ≤ _ := div_le_div_of_nonneg_right hM (by positivity)
  exact short_orbit_ray_payment (referenceScale n) (regularOrbitDistance n B) ((n:ℝ)+2)
    (1+Real.log ((n:ℝ)+2)) globalRadius (regularCovarianceDeficit n B)
    hα hd (hlocal.trans hαlower) (by positivity)
    (by linarith [Real.log_nonneg (show (1:ℝ) ≤ (n:ℝ)+2 by linarith [Nat.cast_nonneg (α:=ℝ) n])])
    globalRadius_bounds.1 globalRadius_bounds.2 hR (hbound e he B hB)

/-- A strict-positive deficit permits a regular reference close on both
the absolute 2/m scale and the relative covariance-deficit scale. -/
theorem eventually_exists_local_paid_reference :
    ∀ᶠ n : ℕ in atTop, ∀ (e:ℕ) (he:n+1 ≤ e)
      (B:Fin (n+2)→FSC.Coord e), (∑i,B i)=0 →
      0 < regularCovarianceDeficit n B →
      regularOrbitDistance n B ≤ 1/((n:ℝ)+2) →
      ∃ U:Fin (n+2)→FSC.Coord e, ScaledRegularGram n U ∧
        rowEnergy (B-U) ≤ 4/((n:ℝ)+2)^2 ∧
        rowEnergy (B-U) ≤ (96/globalRadius)*((n:ℝ)+2)*
          (1+Real.log ((n:ℝ)+2))*regularCovarianceDeficit n B := by
  filter_upwards [eventually_local_orbit_payment] with n hpay
  intro e he B hB hR hlocal
  let Q : ℝ := (48/globalRadius)*((n:ℝ)+2)*(1+Real.log ((n:ℝ)+2))*regularCovarianceDeficit n B
  have hL : 0 < 1+Real.log ((n:ℝ)+2) := by
    linarith [Real.log_nonneg (show (1:ℝ) ≤ (n:ℝ)+2 by linarith [Nat.cast_nonneg (α:=ℝ) n])]
  have hQ : 0 < Q := by dsimp [Q];positivity [globalRadius_bounds.1]
  have hsq : (regularOrbitDistance n B)^2 ≤ Q := hpay e he B hB hR.le hlocal
  have hs : regularOrbitDistance n B < Real.sqrt (2*Q) := by
    have hr := Real.sq_sqrt (show 0 ≤ 2*Q by positivity)
    have hr0 := Real.sqrt_nonneg (2*Q)
    nlinarith
  have hr : regularOrbitDistance n B < min (2/((n:ℝ)+2)) (Real.sqrt (2*Q)) := by
    apply lt_min
    · exact hlocal.trans_lt (by apply div_lt_div_of_pos_right (by norm_num);positivity)
    · exact hs
  have hb := referenceBasis_spec n
  obtain ⟨U,hU,hclose⟩ := exists_regular_rows_near_infimum (referenceBasis n) hb.2.1 hb.2.2
    (show n+2-1 ≤ e by omega) B hB _ hr
  have hclose1 := hclose.trans_le (min_le_left _ _)
  have hclose2 := hclose.trans_le (min_le_right _ _)
  have hnon : 0 ≤ rowEnergy (U-B) := Finset.sum_nonneg fun i _ => sq_nonneg _
  have heq : rowEnergy (B-U)=rowEnergy (U-B) := by
    simp only [rowEnergy,Pi.sub_apply,norm_sub_rev]
  refine ⟨U,hU,?_,?_⟩
  · rw [heq]
    have hh := pow_le_pow_left₀ (Real.sqrt_nonneg _) hclose1.le 2
    rw [Real.sq_sqrt hnon,div_pow] at hh
    norm_num at hh ⊢
    exact hh
  · rw [heq]
    have hh := pow_le_pow_left₀ (Real.sqrt_nonneg _) hclose2.le 2
    rw [Real.sq_sqrt hnon,Real.sq_sqrt (show 0 ≤ 2*Q by positivity)] at hh
    convert hh using 1 <;> dsimp [Q] <;> ring

end NegativeVotingLocalOrbitDeficitPayment
