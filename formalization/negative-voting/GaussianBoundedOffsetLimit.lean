import GaussianBoundedOffsetCertificate
import Mathlib.Topology.MetricSpace.Sequences

/-! Compactness of actual optimal dual offsets. Only actual potentials and
values are passed to the limit; no singular selected inverse or assignment
convergence is presumed. The explicit affine approximation is separate. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped BigOperators Topology RealInnerProductSpace
namespace NegativeVotingBoundedOffsetLimit
open NegativeVotingBoundedOffsetCertificate NegativeVotingFan NegativeVotingFanInverse
open NegativeVotingFanSelectedOffsets NegativeVotingFanValue NegativeVotingBalancedReference
open NegativeVotingRegularCovarianceDeficit NegativeVotingCentroidOptimization
open NegativeVotingOptimizerConstants NegativeVotingAffineBasisLower
variable {n d:ℕ}

theorem potential_tendsto_rows_offsets {V:Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B:ℕ→V→FSC.Coord d) (B0:V→FSC.Coord d) (h:ℕ→V→ℝ) (h0 p:V→ℝ)
    (hB:Tendsto B atTop (𝓝 B0)) (hh:Tendsto h atTop (𝓝 h0)):
    Tendsto (fun k=>potential (B k) p (h k)) atTop (𝓝 (potential B0 p h0)):=by
  let J:ℝ:=∫x:FSC.Coord d,‖x‖∂stdGaussian (FSC.Coord d)
  have hlim:Tendsto (fun k=>‖B k-B0‖*J) atTop (𝓝 0):=by
    simpa using ((hB.sub (tendsto_const_nhds : Tendsto (fun _:ℕ=>B0) atTop (𝓝 B0))).norm.mul_const J)
  have hbound (k:ℕ):‖potential (B k) p (h k)-potential B0 p (h k)‖≤‖B k-B0‖*J:=by
    simpa only [Real.norm_eq_abs] using (potential_rows_sub_bound (B k) B0 p (h k))
  have hd:Tendsto (fun k=>potential (B k) p (h k)-potential B0 p (h k)) atTop (𝓝 0):=
    squeeze_zero_norm hbound hlim
  have hf:=((potential_continuous B0 p).continuousAt.tendsto).comp hh
  simpa only [Function.comp_def,sub_add_cancel,zero_add] using hd.add hf

theorem regularCovarianceDeficit_continuous_rows (n d:ℕ):
    Continuous (fun B:Fin (n+2)→FSC.Coord d=>regularCovarianceDeficit n B):=by
  have hE:Continuous (fun B:Fin (n+2)→FSC.Coord d=>rowEnergy B):=by unfold rowEnergy;fun_prop
  have hV:=optimizedValue_continuous_rows (d:=d) (uniformMass n)
    (fun i=>(uniformMass_pos n i).le) (uniformMass_sum n)
  exact ((continuous_const.add hE).div_const 2).sub hV

/-- A single bounded sequence of actual balanced offsets yields a genuine
optimal limiting dual offset and the same deficit-relative energy bound.
The supplied rows may converge to a singular or duplicate-site system. -/
theorem exists_limiting_balanced_dual (hn:numericThreshold≤ n+2)
    (B:Fin (n+2)→FSC.Coord d)
    (b:ℕ→AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hc:∀k,(∑i,b k i)=0)
    (hcap:∀k i,‖b k i‖≤8*Real.sqrt (1+Real.log ((n:ℝ)+2))/((n:ℝ)+2))
    (hB:Tendsto (fun k=>(b k:Fin (n+2)→FSC.Coord d)) atTop (𝓝 B)):
    ∃h:centeredGauge (Fin (n+2)),
      potential B (uniformMass n) h=optimizedValue B (uniformMass n)∧
      (∑i,((h:Fin (n+2)→ℝ) i)^2)≤
        4*certificateQuadraticConstant*(1+Real.log ((n:ℝ)+2))^2*regularCovarianceDeficit n B:=by
  let u:ℕ→centeredGauge (Fin (n+2)):=fun k=>selectedOffsets (b k) (uniformMass n)
  let H:ℝ:=32*(1+Real.log ((n:ℝ)+2))/((n:ℝ)+2)
  have hH:0≤ H:=by
    dsimp [H]
    have hl:0≤ Real.log ((n:ℝ)+2):=Real.log_nonneg (by have hh:0≤(n:ℝ):=Nat.cast_nonneg n;linarith)
    positivity
  have hball:∀k,u k∈Metric.closedBall (0:centeredGauge (Fin (n+2))) H:=by
    intro k
    rw [Metric.mem_closedBall,dist_zero_right]
    change ‖(u k:Fin (n+2)→ℝ)‖≤ H
    apply (pi_norm_le_iff_of_nonneg hH).mpr
    intro i
    rw [Real.norm_eq_abs]
    exact balanced_selected_offset_abs_bound (b k) (hcap k) i
  obtain ⟨h,hhball,φ,hφ,huh⟩:=(isCompact_closedBall (0:centeredGauge (Fin (n+2))) H).tendsto_subseq hball
  have hBs:Tendsto (fun k=>(b (φ k):Fin (n+2)→FSC.Coord d)) atTop (𝓝 B):=
    hB.comp hφ.tendsto_atTop
  have hhs:Tendsto (fun k=>(u (φ k):Fin (n+2)→ℝ)) atTop (𝓝 (h:Fin (n+2)→ℝ)):=
    (centeredGauge (Fin (n+2))).subtypeL.continuous.continuousAt.tendsto.comp huh
  have hp:=potential_tendsto_rows_offsets (fun k=>(b (φ k):Fin (n+2)→FSC.Coord d)) B
    (fun k=>(u (φ k):Fin (n+2)→ℝ)) h (uniformMass n) hBs hhs
  have heq (k:ℕ):potential (b k) (uniformMass n) (u k)=optimizedValue (b k) (uniformMass n):=by
    obtain ⟨σ,hσ,hlower⟩:=exists_centeredSingularLowerBound (b k)
    exact (optimizedValue_eq_of_mass (b k) (uniformMass n) σ hσ hlower
      (uniformMass_pos n) (uniformMass_sum n) (u k)
      (selectedOffsets_mass (b k) (b k).ind.injective (uniformMass n) (uniformMass_pos n) (uniformMass_sum n))).symm
  simp_rw [heq] at hp
  have hV:=((optimizedValue_continuous_rows (d:=d) (uniformMass n)
    (fun i=>(uniformMass_pos n i).le) (uniformMass_sum n)).continuousAt.tendsto).comp hBs
  refine ⟨h,tendsto_nhds_unique hp hV,?_⟩
  have hEc:Continuous (fun q:centeredGauge (Fin (n+2))=>∑i,((q:Fin (n+2)→ℝ) i)^2):=by
    apply continuous_finset_sum
    intro i _
    exact ((continuous_apply i).comp (centeredGauge (Fin (n+2))).subtypeL.continuous).pow 2
  have hE:Tendsto (fun k=>∑i,((u (φ k):Fin (n+2)→ℝ) i)^2) atTop
      (𝓝 (∑i,((h:Fin (n+2)→ℝ) i)^2)):=hEc.continuousAt.tendsto.comp huh
  have hR:=((regularCovarianceDeficit_continuous_rows n d).continuousAt.tendsto.comp hBs).const_mul
    (4*certificateQuadraticConstant*(1+Real.log ((n:ℝ)+2))^2)
  exact le_of_tendsto_of_tendsto hE hR (Eventually.of_forall fun k=>
    actual_balanced_offset_energy (b (φ k)) hn (hc (φ k)) (hcap (φ k)))

end NegativeVotingBoundedOffsetLimit
