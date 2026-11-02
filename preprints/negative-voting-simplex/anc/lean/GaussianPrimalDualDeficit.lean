import GaussianArbitraryRowOffsetCertificate
import GaussianMassCentroid

/-! Actual Gaussian primal/dual transfer from the balanced covariance deficit
to the first-moment deficit and mass deviation. Singular and duplicate rows
are included by the constructed optimal-dual offset certificate. -/
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped BigOperators Topology RealInnerProductSpace
namespace NegativeVotingPrimalDualDeficit
open NegativeVotingArbitraryOffsetCertificate NegativeVotingBoundedOffsetCertificate
open NegativeVotingFan NegativeVotingFanInverse NegativeVotingFanValue NegativeVotingBalancedReference
open NegativeVotingRegularCovarianceDeficit NegativeVotingOptimizerConstants
open NegativeVotingCentroidOptimization NegativeVotingAssignmentDuality
open NegativeVotingMassCentroid NegativeVotingGaussianMaximumMean
variable {n d:ℕ}

theorem dual_mass_shift (B:Fin (n+2)→FSC.Coord d) (p h:Fin (n+2)→ℝ):
    potential B p h=potential B (uniformMass n) h-h ⬝ᵥ (p-uniformMass n):=by
  unfold potential dotProduct
  simp only [Pi.sub_apply,mul_sub,Finset.sum_sub_distrib,mul_comm]
  ring

/-- Actual balanced optimality and the proved offset certificate give the
covariance-deficit transfer, with no row normalization or nondegeneracy. -/
theorem row_deficit_from_primal_value (hn:numericThreshold≤ n+2)
    (B:Fin (n+2)→FSC.Coord d) (hc:(∑i,B i)=0)
    (hB:∀i,‖B i‖≤4*Real.sqrt (1+Real.log ((n:ℝ)+2))/((n:ℝ)+2))
    (p:Fin (n+2)→ℝ) (hp:∀i,0≤ p i) (hs:∑i,p i=1)
    (hprimal:rowEnergy B≤ optimizedValue B p):
    regularCovarianceDeficit n B≤ referenceFirstWeight n-rowEnergy B+
      4*certificateQuadraticConstant*(1+Real.log ((n:ℝ)+2))^2*
        (∑i,(p i-uniformMass n i)^2):=by
  obtain ⟨h,hpot,henergy⟩:=exists_balanced_optimal_dual_with_energy_bound hn B hc hB
  let T:ℝ:=certificateQuadraticConstant*(1+Real.log ((n:ℝ)+2))^2
  have hT:0< T:=by
    have hC:0< certificateQuadraticConstant:=lt_of_lt_of_le (by norm_num) certificateQuadraticConstant_ge_thirtytwo
    have hl:0≤ Real.log ((n:ℝ)+2):=Real.log_nonneg (by have hh:0≤(n:ℝ):=Nat.cast_nonneg n;linarith)
    dsimp [T]
    positivity
  let z:Fin (n+2)→ℝ:=p-uniformMass n
  have hupper:=optimizedValue_le_potential B p hp hs h
  rw [dual_mass_shift B p h,hpot] at hupper
  have hfirst:regularCovarianceDeficit n B≤(referenceFirstWeight n-rowEnergy B)/2-(h:Fin (n+2)→ℝ) ⬝ᵥ z:=by
    unfold regularCovarianceDeficit
    change _≤_/2-(h:Fin (n+2)→ℝ) ⬝ᵥ (p-uniformMass n)
    linarith
  have hsq:0≤∑i,((h:Fin (n+2)→ℝ) i+4*T*z i)^2:=Finset.sum_nonneg fun i _=>sq_nonneg _
  have he:(∑i,((h:Fin (n+2)→ℝ) i+4*T*z i)^2)=
      (∑i,((h:Fin (n+2)→ℝ) i)^2)+8*T*((h:Fin (n+2)→ℝ) ⬝ᵥ z)+16*T^2*(∑i,(z i)^2):=by
    have hh (i:Fin (n+2)):((h:Fin (n+2)→ℝ) i+4*T*z i)^2=
        ((h:Fin (n+2)→ℝ) i)^2+8*T*((h:Fin (n+2)→ℝ) i*z i)+16*T^2*(z i)^2:=by ring
    simp only [hh,Finset.sum_add_distrib,←Finset.mul_sum,dotProduct]
  rw [he] at hsq
  have henergy':(∑i,((h:Fin (n+2)→ℝ) i)^2)≤4*T*regularCovarianceDeficit n B:=by
    simpa only [T,mul_assoc] using henergy
  have hscaled:=mul_le_mul_of_nonneg_left hfirst (show 0≤8*T by positivity)
  have hout:(4*T)*regularCovarianceDeficit n B≤(4*T)*
      (referenceFirstWeight n-rowEnergy B+4*T*(∑i,(z i)^2)):=by nlinarith
  have hh:regularCovarianceDeficit n B≤ referenceFirstWeight n-rowEnergy B+4*T*(∑i,(z i)^2):=
    (mul_le_mul_iff_right₀ (show 0<4*T by positivity)).mp hout
  simpa only [T,z,Pi.sub_apply,mul_assoc] using hh

/-- Actual probability mass at most2/m supplies the required row cap. -/
theorem feasible_centroid_norm_le (p:Fin (n+2)→ℝ) (f:FSC.Coord d→Fin (n+2)→ℝ)
    (hf:Feasible p f) (hmass:∀i,p i≤2/((n:ℝ)+2)) (i:Fin (n+2)):
    ‖centroidRows f i‖≤4*Real.sqrt (1+Real.log ((n:ℝ)+2))/((n:ℝ)+2):=by
  let m:ℝ:=(n:ℝ)+2
  let L:ℝ:=1+Real.log m
  have hm:1≤ m:=by dsimp [m];have hh:0≤(n:ℝ):=Nat.cast_nonneg n;linarith
  have hmp:0< m:=by linarith
  have hlog:0≤ Real.log m:=Real.log_nonneg hm
  have hL:0≤ L:=by dsimp [L];linarith
  have hroot:Real.sqrt (2*Real.log m)≤(3/2)*Real.sqrt L:=by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt hL,Real.sq_sqrt (by positivity)]
    dsimp [L]
    nlinarith
  have hs:1≤ Real.sqrt L:=by simpa [L] using Real.sqrt_le_sqrt (show (1:ℝ)≤ L by dsimp [L];linarith)
  have hp:1≤ Real.sqrt (2*Real.pi):=by
    simpa using Real.sqrt_le_sqrt (show (1:ℝ)≤2*Real.pi by linarith [Real.pi_gt_three])
  have hinv:(Real.sqrt (2*Real.pi))⁻¹≤1:=by
    rw [inv_eq_one_div]
    exact (div_le_one (by positivity)).mpr hp
  have hh:=gaussianCentroid_norm_le_logarithmic_mass_bound (fun x=>f x i) m 2 hm
    (hf.1 i) (feasible_coordinate_bounds p f hf i) (by rw [hf.2.2 i];exact hmass i)
  apply hh.trans
  apply div_le_div_of_nonneg_right _ hmp.le
  linarith

/-- No primal-value premise remains for actual feasible Gaussian assignments. -/
theorem feasible_covariance_deficit_bound (hn:numericThreshold≤ n+2)
    (p:Fin (n+2)→ℝ) (hp:∀i,0≤ p i) (hs:∑i,p i=1)
    (f:FSC.Coord d→Fin (n+2)→ℝ) (hf:Feasible p f)
    (hmass:∀i,p i≤2/((n:ℝ)+2)):
    regularCovarianceDeficit n (centroidRows f)≤ referenceFirstWeight n-centroidEnergy f+
      4*certificateQuadraticConstant*(1+Real.log ((n:ℝ)+2))^2*
        (∑i,(p i-uniformMass n i)^2):=by
  have hprimal:rowEnergy (centroidRows f)≤ optimizedValue (centroidRows f) p:=by
    have hh:=assignmentValue_le_optimizedValue (centroidRows f) p f hf
    rwa [assignmentValue_centroid p f hf] at hh
  exact row_deficit_from_primal_value hn (centroidRows f) (centroidRows_sum_zero p f hf)
    (feasible_centroid_norm_le p f hf hmass) p hp hs hprimal

end NegativeVotingPrimalDualDeficit
