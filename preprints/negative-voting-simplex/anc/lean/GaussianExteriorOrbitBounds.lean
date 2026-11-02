import GaussianExteriorReferenceBounds

/-! Exterior covariance-deficit floors and regular-orbit control, attached to
the actual Gaussian value. The quantitative local curvature interface remains
explicit until the separate balanced facet continuation discharges it. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology RealInnerProductSpace Classical
universe u
namespace NegativeVotingExteriorOrbit
open NegativeVoting NegativeVotingExteriorReference NegativeVotingProcrustes
  NegativeVotingRayDeficit NegativeVotingBalancedReference NegativeVotingGaussianMaximumMean
  NegativeVotingRegularCovarianceDeficit NegativeVotingCentroidOptimization
  NegativeVotingAffineLogMassBound NegativeVotingAssignmentCoordinateBridge
  NegativeVotingAssignmentDuality NegativeVotingFractionalMass
variable {n d e:ℕ}

theorem reference_energy_scale (n:ℕ):
    (referenceScale n)^2*((n:ℝ)+1)=referenceFirstWeight n:=by
  unfold referenceScale referenceFirstWeight
  field_simp

theorem scaled_regular_row_energy (R:Fin (n+2)→FSC.Coord e) (hR:ScaledRegularGram n R):
    rowEnergy R=referenceFirstWeight n:=by
  unfold rowEnergy
  have hdiag (i:Fin (n+2)):‖R i‖^2=(referenceScale n)^2*(1-1/((n:ℝ)+2)):=by
    simpa only [real_inner_self_eq_norm_sq,ite_true] using hR i i
  simp_rw [hdiag]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_add,Nat.cast_ofNat]
  rw [←reference_energy_scale]
  field_simp
  ring

/-- A true regular reference bounds the literal infimum distance, without
assuming attainment of that infimum. -/
theorem regular_orbit_distance_sq_le_energy
    (b:AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG:∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP:∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hde:d≤ e) (B:Fin (n+2)→FSC.Coord e) (hB:(∑i,B i)=0):
    (regularOrbitDistance n B)^2≤2*rowEnergy B+2*referenceFirstWeight n:=by
  obtain ⟨R,hR,_⟩:=exists_regular_rows_with_distance_bound b hG hP hde B hB
  have hnonneg:0≤ regularOrbitDistance n B:=(regularOrbitDistance_nonneg_and_le b hG hP hde B hB).1
  have hbdd:BddBelow {r:ℝ|∃T:Fin (n+2)→FSC.Coord e,ScaledRegularGram n T ∧
      r=Real.sqrt (∑i,‖B i-T i‖^2)}:=by
    refine ⟨0,?_⟩
    rintro x ⟨T,_,rfl⟩
    exact Real.sqrt_nonneg _
  have hd:regularOrbitDistance n B≤ Real.sqrt (∑i,‖B i-R i‖^2):=
    csInf_le hbdd ⟨R,hR,rfl⟩
  have hd2:=pow_le_pow_left₀ hnonneg hd 2
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _=>sq_nonneg _))] at hd2
  have hs:(∑i,‖B i-R i‖^2)≤2*rowEnergy B+2*rowEnergy R:=by
    calc
      _≤∑i,(2*‖B i‖^2+2*‖R i‖^2):=by
        apply Finset.sum_le_sum
        intro i _
        have hh:=pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (B i) (R i)) 2
        nlinarith [sq_nonneg (‖B i‖-‖R i‖)]
      _=_:=by simp only [rowEnergy,Finset.sum_add_distrib,Finset.mul_sum]
  rw [scaled_regular_row_energy R hR] at hs
  exact hd2.trans hs

theorem normalized_orbit_distance_le_sqrt_size
    (b:AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG:∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP:∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hde:d≤ e) (B:Fin (n+2)→FSC.Coord e) (hB:(∑i,B i)=0)
    (hW:rowEnergy B≤2*referenceFirstWeight n):
    regularOrbitDistance n B/referenceScale n≤3*Real.sqrt ((n:ℝ)+2):=by
  have he:=regular_orbit_distance_sq_le_energy b hG hP hde B hB
  have hzero:0≤ regularOrbitDistance n B:=(regularOrbitDistance_nonneg_and_le b hG hP hde B hB).1
  have ha:=referenceScale_pos n
  apply (sq_le_sq₀ (div_nonneg hzero ha.le) (by positivity)).mp
  rw [div_pow,mul_pow,Real.sq_sqrt (show 0≤(n:ℝ)+2 by positivity)]
  apply (div_le_iff₀ (sq_pos_of_pos ha)).mpr
  rw [←reference_energy_scale] at he hW
  nlinarith [sq_nonneg (referenceScale n),
    mul_nonneg (sq_nonneg (referenceScale n)) (Nat.cast_nonneg (α:=ℝ) n)]

/-- Exact exterior-scale algebra after the actual Gaussian ray estimate.
The local-to-global curvature loss, singular endpoints and orbit infimum
have already been handled before this numerical step. -/
theorem exterior_ray_algebra (m L a dist R c:ℝ)
    (hm:0< m) (hL:25≤ L) (ha:0< a) (hc:0< c) (hc1:c≤1)
    (halow:L/m^2≤ a^2) (haupp:a^2≤20*L/m^2)
    (hd:1/m< dist) (hq:dist/a≤3*Real.sqrt m)
    (hray:a^2*(dist/a)^2/(48*m)*min 1 ((c/L)/(dist/a))≤ R):
    c/(240*m^3*Real.sqrt L)≤ R ∧
      dist^2≤(144/c)*(m*Real.sqrt m)*L*R:=by
  let q:=dist/a
  have hLpos:0< L:=by linarith
  have hsL:0< Real.sqrt L:=Real.sqrt_pos.mpr hLpos
  have hqpos:0< q:=div_pos (lt_trans (one_div_pos.mpr hm) hd) ha
  have haU:a*m≤5*Real.sqrt L:=by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow,mul_pow,Real.sq_sqrt hLpos.le]
    have hh:=(le_div_iff₀ (sq_pos_of_pos hm)).mp haupp
    nlinarith
  have hqfloor:1/(5*Real.sqrt L)≤ q:=by
    apply (le_div_iff₀ ha).mpr
    calc
      _=a/(5*Real.sqrt L):=by ring
      _≤1/m:=(div_le_div_iff₀ (by positivity) hm).mpr (by nlinarith [haU])
      _≤ dist:=hd.le
  have hs5:5≤ Real.sqrt L:=by
    have hh:=Real.sqrt_le_sqrt hL
    norm_num at hh
    exact hh
  have hradius:c/L≤ q:=by
    apply le_trans _ hqfloor
    apply (div_le_div_iff₀ hLpos (by positivity)).mpr
    have hh:=mul_le_mul_of_nonneg_right hs5 (Real.sqrt_nonneg L)
    have hh':=mul_le_mul_of_nonneg_right hc1 (show 0≤5*Real.sqrt L by positivity)
    nlinarith [Real.sq_sqrt hLpos.le]
  have hmin:min 1 ((c/L)/q)=(c/L)/q:=
    min_eq_right ((div_le_one hqpos).mpr hradius)
  change a^2*q^2/(48*m)*min 1 ((c/L)/q)≤ R at hray
  rw [hmin] at hray
  have hlin:a^2*q*c/(48*m*L)≤ R:=by
    convert hray using 1 <;> field_simp <;> ring
  have hR:0≤ R:=(show 0≤ a^2*q*c/(48*m*L) by positivity).trans hlin
  constructor
  · have hcoeff:(L/m^2)/(48*m)*(c/L)≤ a^2/(48*m)*(c/L):=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right halow (by positivity)) (by positivity)
    have hh:=mul_le_mul hcoeff hqfloor (by positivity)
      (show 0≤ a^2/(48*m)*(c/L) by positivity)
    calc
      c/(240*m^3*Real.sqrt L)=(L/m^2)/(48*m)*(c/L)*(1/(5*Real.sqrt L)):=by
        field_simp
        ring
      _≤ a^2/(48*m)*(c/L)*q:=hh
      _=a^2*q*c/(48*m*L):=by ring
      _≤ R:=hlin
  · have hh:=mul_le_mul_of_nonneg_left hlin
      (show 0≤(48*m*L/c)*q by positivity)
    have hstep:a^2*q^2≤(48*m*L/c)*q*R:=by
      convert hh using 1 <;> field_simp <;> ring
    have he:dist=a*q:=by dsimp [q];field_simp
    calc
      dist^2=a^2*q^2:=by rw [he,mul_pow]
      _≤(48*m*L/c)*q*R:=hstep
      _≤(48*m*L/c)*(3*Real.sqrt m)*R:=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq (by positivity)) hR
      _=(144/c)*(m*Real.sqrt m)*L*R:=by ring

/-- Actual Gaussian exterior floor and distance control, with the exact local
curvature premise visible. No rank condition is imposed on the competitor. -/
theorem actual_exterior_bounds (hn:0< n)
    (b:AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG:∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP:∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (c:ℝ) (hc:0< c) (hc1:c≤1)
    (hL:25≤1+Real.log ((n:ℝ)+2))
    (hscale:(1+Real.log ((n:ℝ)+2))/((n:ℝ)+2)^2≤(referenceScale n)^2 ∧
      (referenceScale n)^2≤20*(1+Real.log ((n:ℝ)+2))/((n:ℝ)+2)^2)
    (hcurv:LocalGaussianCurvature b (uniformMass n) (c/(1+Real.log ((n:ℝ)+2)))
      (referenceScale n/(12*((n:ℝ)+2))))
    (hde:d≤ e) (B:Fin (n+2)→FSC.Coord e) (hB:(∑i,B i)=0)
    (hW:rowEnergy B≤2*referenceFirstWeight n)
    (hd:1/((n:ℝ)+2)< regularOrbitDistance n B):
    c/(240*((n:ℝ)+2)^3*Real.sqrt (1+Real.log ((n:ℝ)+2)))≤ regularCovarianceDeficit n B ∧
      (regularOrbitDistance n B)^2≤(144/c)*
        (((n:ℝ)+2)*Real.sqrt ((n:ℝ)+2))*(1+Real.log ((n:ℝ)+2))*regularCovarianceDeficit n B:=by
  have hLp:0<1+Real.log ((n:ℝ)+2):=by linarith
  have hr:=regularCovarianceDeficit_orbit_bound hn b hG hP
    (c/(1+Real.log ((n:ℝ)+2))) (div_pos hc hLp) hcurv hde B hB
  exact exterior_ray_algebra ((n:ℝ)+2) (1+Real.log ((n:ℝ)+2))
    (referenceScale n) (regularOrbitDistance n B) (regularCovarianceDeficit n B) c
    (by positivity) hL (referenceScale_pos n) hc hc1 hscale.1 hscale.2 hd
    (normalized_orbit_distance_le_sqrt_size b hG hP hde B hB hW) hr

/-- One numerical threshold precedes every dimension and row realization. -/
theorem eventually_uniform_exterior_bounds (c:ℝ) (hc:0< c) (hc1:c≤1):
    ∀ᶠ n:ℕ in atTop,∀(d e:ℕ) (b:AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
      (hG:∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
      (hP:∀x,(∑i,inner ℝ (b i) x • b i)=x)
      (hcurv:LocalGaussianCurvature b (uniformMass n) (c/(1+Real.log ((n:ℝ)+2)))
        (referenceScale n/(12*((n:ℝ)+2))))
      (hde:d≤ e) (B:Fin (n+2)→FSC.Coord e) (hB:(∑i,B i)=0)
      (hW:rowEnergy B≤2*referenceFirstWeight n)
      (hd:1/((n:ℝ)+2)< regularOrbitDistance n B),
      c/(240*((n:ℝ)+2)^3*Real.sqrt (1+Real.log ((n:ℝ)+2)))≤ regularCovarianceDeficit n B ∧
      (regularOrbitDistance n B)^2≤(144/c)*
        (((n:ℝ)+2)*Real.sqrt ((n:ℝ)+2))*(1+Real.log ((n:ℝ)+2))*regularCovarianceDeficit n B:=by
  filter_upwards [eventually_reference_scale_bounds,eventually_gt_atTop (0:ℕ),
    (Real.tendsto_log_atTop.comp NegativeVotingGaussianMaximumSecondMoment.size_tendsto).eventually_ge_atTop 24]
    with n hscale hn hlog
  simp only [Function.comp_def] at hlog
  intro d e b hG hP hcurv hde B hB hW hd
  exact actual_exterior_bounds hn b hG hP c hc hc1 (by linarith) hscale hcurv hde B hB hW hd

/-- Actual product-Gaussian competitors yield the required centered Euclidean
row system and its energy cap. No row-norm or centroid-realization premise is
supplied; only the separately named local curvature interface remains. -/
theorem eventually_uniform_competitive_exterior_bounds (c:ℝ) (hc:0< c) (hc1:c≤1):
    ∀ᶠ n:ℕ in atTop,∀(κ:Type u) [Fintype κ]
      (Ref:Fin (n+2)→κ→ℝ) (hRef:RegularSimplexGram Ref)
      (f:(κ→ℝ)→Fin (n+2)→ℝ)
      (hf:∀i,AEMeasurable (fun x=>f x i) (standardGaussian κ))
      (hp:∀ᵐ x ∂standardGaussian κ,SimplexWeights (f x))
      (r:ℝ) (hr0:0< r) (hr:r≤1/((n:ℝ)+1))
      (hcomp:gaussianNoiseStability (-r) f≤ gaussianNoiseStability (-r) (regularAssignment Ref))
      (d e:ℕ) (coord:FSC.Coord e≃ₗᵢ[ℝ]EuclideanSpace ℝ κ)
      (b:AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
      (hG:∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
      (hP:∀x,(∑i,inner ℝ (b i) x • b i)=x) (hde:d≤ e)
      (hcurv:LocalGaussianCurvature b (uniformMass n) (c/(1+Real.log ((n:ℝ)+2)))
        (referenceScale n/(12*((n:ℝ)+2)))),
      let B:=centroidRows (coordinateRule coord f)
      1/((n:ℝ)+2)< regularOrbitDistance n B →
      c/(240*((n:ℝ)+2)^3*Real.sqrt (1+Real.log ((n:ℝ)+2)))≤ regularCovarianceDeficit n B ∧
      (regularOrbitDistance n B)^2≤(144/c)*
        (((n:ℝ)+2)*Real.sqrt ((n:ℝ)+2))*(1+Real.log ((n:ℝ)+2))*regularCovarianceDeficit n B:=by
  filter_upwards [eventually_uniform_exterior_bounds c hc hc1,
    eventually_uniform_competitive_row_energy_bound] with n hext henergy
  intro κ _ Ref hRef f hf hp r hr0 hr hcomp d e coord b hG hP hde hcurv
  dsimp only
  intro hd
  have hfeas:=coordinateRule_feasible coord f hf hp
  have hcenter:=centroidRows_sum_zero (assignmentMass f) (coordinateRule coord f) hfeas
  have hW:rowEnergy (centroidRows (coordinateRule coord f))≤2*referenceFirstWeight n:=by
    change centroidEnergy (coordinateRule coord f)≤_
    rw [coordinateRule_centroidEnergy coord f hf hp]
    exact henergy κ Ref hRef f hf hp r hr0 hr hcomp
  exact hext d e b hG hP hcurv hde _ hcenter hW hd

end NegativeVotingExteriorOrbit
