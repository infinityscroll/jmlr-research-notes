import GaussianTwoCellScalar
import GaussianTwoCellSplit

/-! Quantitative centroid separation at an actual global Gaussian optimum.
The competing fractional assignment and its exact mass-preserving threshold
are constructed; no split, density bound, or centroid formula is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology RealInnerProductSpace
namespace NegativeVotingTwoCell
open NegativeVoting NegativeVotingAssignmentDuality NegativeVotingCentroidOptimization
  NegativeVotingMassCentroid
variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

theorem resplitPair_energy_difference (f : FSC.Coord d → ι → ℝ)
    (i j : ι) (hij : i≠j) (v : FSC.Coord d) (t : ℝ) :
    centroidEnergy (resplitPair f i j v t)-centroidEnergy f=
      (‖centroidRows (resplitPair f i j v t) i‖^2-‖centroidRows f i‖^2)+
      (‖centroidRows (resplitPair f i j v t) j‖^2-‖centroidRows f j‖^2) := by
  unfold centroidEnergy rowEnergy
  rw [←Finset.sum_sub_distrib]
  have he (k : ι) : ‖centroidRows (resplitPair f i j v t) k‖^2-‖centroidRows f k‖^2=
      (if k=i then ‖centroidRows (resplitPair f i j v t) i‖^2-‖centroidRows f i‖^2 else 0)+
      (if k=j then ‖centroidRows (resplitPair f i j v t) j‖^2-‖centroidRows f j‖^2 else 0) := by
    by_cases hki : k=i
    · subst k; simp [hij]
    · by_cases hkj : k=j
      · subst k; simp [hij.symm]
      · simp [centroidRows,resplitPair,hki,hkj]
  calc
    _ = ∑ k, ((if k=i then ‖centroidRows (resplitPair f i j v t) i‖^2-‖centroidRows f i‖^2 else 0)+
        (if k=j then ‖centroidRows (resplitPair f i j v t) j‖^2-‖centroidRows f j‖^2 else 0)) :=
      Finset.sum_congr rfl (fun k _ => he k)
    _ = _ := by simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

/-- At a global optimum, re-splitting a pair cannot increase the distance
between its actual unnormalized centroids. -/
theorem optimal_pair_distance_comparison (p : ι → ℝ) (f : FSC.Coord d → ι → ℝ)
    (hf : Feasible p f)
    (hopt : ∀ g : FSC.Coord d → ι → ℝ, Feasible p g → centroidEnergy g ≤ centroidEnergy f)
    (i j : ι) (hij : i≠j) (v : FSC.Coord d) (t : ℝ)
    (hg : Feasible p (resplitPair f i j v t)) :
    ‖centroidRows (resplitPair f i j v t) i-centroidRows (resplitPair f i j v t) j‖ ≤
      ‖centroidRows f i-centroidRows f j‖ := by
  have ho := hopt (resplitPair f i j v t) hg
  have he := resplitPair_energy_difference f i j hij v t
  have hpair : ‖centroidRows (resplitPair f i j v t) i‖^2+
      ‖centroidRows (resplitPair f i j v t) j‖^2 ≤ ‖centroidRows f i‖^2+‖centroidRows f j‖^2 := by
    linarith
  have hsum := resplitPair_centroid_sum p f hf i j hij v t
  have hpara (a b : FSC.Coord d) : ‖a+b‖^2+‖a-b‖^2=2*(‖a‖^2+‖b‖^2) := by
    rw [norm_add_sq_real,norm_sub_sq_real]
    ring
  have hfg := hpara (centroidRows f i) (centroidRows f j)
  have hgg := hpara (centroidRows (resplitPair f i j v t) i)
    (centroidRows (resplitPair f i j v t) j)
  rw [hsum] at hgg
  nlinarith [norm_nonneg (centroidRows f i-centroidRows f j),
    norm_nonneg (centroidRows (resplitPair f i j v t) i-centroidRows (resplitPair f i j v t) j)]

/-- The actual two-cell centroid separation. The only optimizing hypothesis
is global maximality over completed-measurable fractional simplex assignments
with the same prescribed masses. -/
theorem centroid_separation_at_global_optimum (p : ι → ℝ) (f : FSC.Coord d → ι → ℝ)
    (hf : Feasible p f)
    (hopt : ∀ g : FSC.Coord d → ι → ℝ, Feasible p g → centroidEnergy g ≤ centroidEnergy f)
    (hdim : 2 ≤ d) (i j : ι) (hij : i≠j) (hpi : 0 < p i) (hpj : 0 < p j) :
    Real.sqrt (2*Real.pi)*p i*p j ≤ ‖centroidRows f i-centroidRows f j‖ := by
  have hd : 2 ≤ Module.finrank ℝ (FSC.Coord d) := by simpa [FSC.Coord] using hdim
  obtain ⟨v,hv,hperp⟩ := exists_unit_perpendicular hd (centroidRows f i+centroidRows f j)
  let u := pairUnion f i j
  let ν := projectedFractionalGaussian u v
  let c := (Real.sqrt (2*Real.pi))⁻¹
  have hu := pairUnion_measurable p f hf i j
  have h01 := pairUnion_bounds p f hf i j hij
  have h0 := h01.mono (fun _ h => h.1)
  have h1 := h01.mono (fun _ h => h.2)
  letI : IsFiniteMeasure ν := projectedFractionalGaussian_finite u v hv h1
  have hdom : ν ≤ ENNReal.ofReal c • volume := projectedFractionalGaussian_density_bound u v hv h1
  have hc : 0 < c := by dsimp [c]; positivity
  have htotal : ν.real univ=p i+p j :=
    (projectedFractionalGaussian_total u hu h0 v).trans (pairUnion_mass p f hf i j)
  obtain ⟨t,ht⟩ := bounded_density_threshold ν c hc.le hdom (p j) hpj (by rw [htotal]; linarith)
  have hupper : ν.real (Ioi t)=p i := by
    have hh := measureReal_add_measureReal_compl (μ:=ν) (s:=Iic t) measurableSet_Iic
    rw [compl_Iic,ht,htotal] at hh
    linarith
  have hg := resplitPair_feasible p f hf i j hij v t hupper ht
  have hmean : ∫ y,y ∂ν=0 := pairProjection_mean_zero p f hf i j hij v hperp
  have hsep := bounded_density_split_separation ν c hc hdom
    (projectedFractionalGaussian_integrable_id u v hv h1) hmean t
    (by rw [hupper]; exact hpi) (by rw [ht]; exact hpj)
  rw [hupper,ht] at hsep
  have hproj : inner ℝ v
      (centroidRows (resplitPair f i j v t) i-centroidRows (resplitPair f i j v t) j)=
      (∫ y in Ioi t,y ∂ν)-(∫ y in Iic t,y ∂ν) := by
    rw [inner_sub_right]
    simp only [centroidRows,resplitPair,ite_true,ite_eq_right hij.symm]
    rw [upperPair_projection p f hf i j hij v t,lowerPair_projection p f hf i j hij v t]
  calc
    Real.sqrt (2*Real.pi)*p i*p j=p i*p j/c := by dsimp [c]; rw [div_inv_eq_mul]; ring
    _ ≤ (∫ y in Ioi t,y ∂ν)-(∫ y in Iic t,y ∂ν) := hsep
    _ = inner ℝ v
        (centroidRows (resplitPair f i j v t) i-centroidRows (resplitPair f i j v t) j) := hproj.symm
    _ ≤ ‖centroidRows (resplitPair f i j v t) i-centroidRows (resplitPair f i j v t) j‖ := by
      simpa only [hv,one_mul] using real_inner_le_norm v
        (centroidRows (resplitPair f i j v t) i-centroidRows (resplitPair f i j v t) j)
    _ ≤ ‖centroidRows f i-centroidRows f j‖ := optimal_pair_distance_comparison p f hf hopt i j hij v t hg

/-- Positive masses force distinct actual centroid rows at every global optimum. -/
theorem centroidRows_injective_at_global_optimum (p : ι → ℝ) (hp : ∀ i,0 < p i)
    (f : FSC.Coord d → ι → ℝ) (hf : Feasible p f)
    (hopt : ∀ g : FSC.Coord d → ι → ℝ, Feasible p g → centroidEnergy g ≤ centroidEnergy f)
    (hdim : 2 ≤ d) : Function.Injective (centroidRows f) := by
  intro i j he
  by_contra hij
  have hh := centroid_separation_at_global_optimum p f hf hopt hdim i j hij (hp i) (hp j)
  rw [he,sub_self,norm_zero] at hh
  have hpi := hp i
  have hpj := hp j
  have hpos : 0 < Real.sqrt (2*Real.pi)*p i*p j := by positivity
  linarith

/-- The upper edge bound uses the actual Gaussian centroid entropy estimate
and does not require optimality. -/
theorem centroid_edge_upper_bound (p : ι → ℝ) (f : FSC.Coord d → ι → ℝ)
    (hf : Feasible p f) (m C : ℝ) (hm : 1 ≤ m)
    (i j : ι) (hi : p i ≤ C/m) (hj : p j ≤ C/m) :
    ‖centroidRows f i-centroidRows f j‖ ≤
      2*(C*Real.sqrt (2*Real.log m)+(Real.sqrt (2*Real.pi))⁻¹)/m := by
  have hci := gaussianCentroid_norm_le_logarithmic_mass_bound (fun x => f x i) m C hm
    (hf.1 i) (feasible_coordinate_bounds p f hf i) (by rw [hf.2.2 i]; exact hi)
  have hcj := gaussianCentroid_norm_le_logarithmic_mass_bound (fun x => f x j) m C hm
    (hf.1 j) (feasible_coordinate_bounds p f hf j) (by rw [hf.2.2 j]; exact hj)
  calc
    _ ≤ ‖centroidRows f i‖+‖centroidRows f j‖ := norm_sub_le _ _
    _ ≤ (C*Real.sqrt (2*Real.log m)+(Real.sqrt (2*Real.pi))⁻¹)/m+
        (C*Real.sqrt (2*Real.log m)+(Real.sqrt (2*Real.pi))⁻¹)/m := add_le_add hci hcj
    _ = _ := by ring

/-- Uniform mass-box geometry for every actual centroid-energy maximizer. -/
theorem centroid_edges_in_mass_window (p : ι → ℝ) (f : FSC.Coord d → ι → ℝ)
    (hf : Feasible p f)
    (hopt : ∀ g : FSC.Coord d → ι → ℝ, Feasible p g → centroidEnergy g ≤ centroidEnergy f)
    (hdim : 2 ≤ d) (p0 m C : ℝ) (hp0 : 0 < p0) (hm : 1 ≤ m)
    (hlo : ∀ i,p0 ≤ p i) (hhi : ∀ i,p i ≤ C/m) (i j : ι) (hij : i≠j) :
    Real.sqrt (2*Real.pi)*p0^2 ≤ ‖centroidRows f i-centroidRows f j‖ ∧
    ‖centroidRows f i-centroidRows f j‖ ≤
      2*(C*Real.sqrt (2*Real.log m)+(Real.sqrt (2*Real.pi))⁻¹)/m := by
  refine ⟨?_,centroid_edge_upper_bound p f hf m C hm i j (hhi i) (hhi j)⟩
  have hmul : p0^2 ≤ p i*p j := by
    simpa only [pow_two] using mul_le_mul (hlo i) (hlo j) hp0.le (hp0.le.trans (hlo i))
  calc
    _ ≤ Real.sqrt (2*Real.pi)*(p i*p j) := mul_le_mul_of_nonneg_left hmul (Real.sqrt_nonneg _)
    _ = Real.sqrt (2*Real.pi)*p i*p j := by ring
    _ ≤ _ := centroid_separation_at_global_optimum p f hf hopt hdim i j hij
      (hp0.trans_le (hlo i)) (hp0.trans_le (hlo j))

end NegativeVotingTwoCell
