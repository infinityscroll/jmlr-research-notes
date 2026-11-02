import GaussianVariancePathSymmetry
import GaussianDiagonalSecondOffsetBound

/-! Two-sided local bounds for the actual selected variance path. Uniform
positive-time estimates at half the exponent are reflected exactly in time;
this supplies genuine neighborhoods for differentiation at both endpoints. -/
noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology
namespace NegativeVotingVarianceLocalBounds
open NegativeVotingDiagonalOffsetContinuation NegativeVotingDiagonalSecondOffsetBound
  NegativeVotingDiagonalSecondBalanceEquation NegativeVotingVariancePathSymmetry
  NegativeVotingFanInverse NegativeVotingDiagonalSecondForcingBound
  NegativeVotingDiagonalDerivativeEnvelopes NegativeVotingDiagonalOffsetComponentBound
  NegativeVotingHazardQuantileAsymptotics NegativeVotingGaussianMaximum
variable {n : ℕ}

def sigmaVelocity (ξ : Fin (n+2)→ℝ) (t : ℝ) : Fin (n+2)→ℝ :=
  fun i=>ξ i/(2*varianceSigma ξ t i)
def sigmaAcceleration (ξ : Fin (n+2)→ℝ) (t : ℝ) : Fin (n+2)→ℝ :=
  fun i=>-(ξ i)^2/(4*(varianceSigma ξ t i)^3)
def offsetVelocity (n : ℕ) (ξ : Fin (n+2)→ℝ) (t : ℝ) : Fin (n+2)→ℝ :=
  (deriv (varianceOffsets n ξ) t : centeredGauge (Fin (n+2)))
def offsetAcceleration (n : ℕ) (ξ : Fin (n+2)→ℝ) (t : ℝ) : Fin (n+2)→ℝ :=
  (deriv (deriv (varianceOffsets n ξ)) t : centeredGauge (Fin (n+2)))

lemma offsetVelocity_neg_neg (n : ℕ) (ξ : Fin (n+2)→ℝ) (t : ℝ) :
    offsetVelocity n (-ξ) (-t)= -offsetVelocity n ξ t := by
  unfold offsetVelocity
  rw [varianceOffsets_deriv_neg_neg]
  rfl
lemma offsetAcceleration_neg_neg (n : ℕ) (ξ : Fin (n+2)→ℝ) (t : ℝ) :
    offsetAcceleration n (-ξ) (-t)=offsetAcceleration n ξ t := by
  unfold offsetAcceleration
  rw [varianceOffsets_secondDeriv_neg_neg]

lemma actual_variance_coordinate_derivatives (ξ : Fin (n+2)→ℝ) (t : ℝ)
    (hσ : ∀i,0<varianceSigma ξ t i) :
    (∀i,HasDerivAt (fun s=>varianceSigma ξ s i) (sigmaVelocity ξ t i) t) ∧
    (∀i,HasDerivAt (fun s=>varianceOffsetVector n ξ s i) (offsetVelocity n ξ t i) t) ∧
    (∀i,HasDerivAt (fun s=>sigmaVelocity ξ s i) (sigmaAcceleration ξ t i) t) ∧
    (∀i,HasDerivAt (fun s=>offsetVelocity n ξ s i) (offsetAcceleration n ξ t i) t) := by
  have hp:∀i,0<1+t*ξ i:=fun i=>Real.sqrt_pos.mp (hσ i)
  have hh:HasDerivAt (varianceOffsets n ξ) (deriv (varianceOffsets n ξ) t) t:=
    ((varianceOffsets_contDiffAt ξ t hp).differentiableAt (by norm_num)).hasDerivAt
  have hv:HasDerivAt (deriv (varianceOffsets n ξ)) (deriv (deriv (varianceOffsets n ξ)) t) t:=
    (varianceOffsets_deriv_differentiableAt ξ t hp).hasDerivAt
  refine ⟨hasDerivAt_pi.mp (varianceSigma_hasDerivAt ξ t hp),?_,
    hasDerivAt_pi.mp (varianceSigma_first_hasDerivAt ξ t hp),?_⟩
  · exact hasDerivAt_pi.mp ((centeredGauge (Fin (n+2))).subtypeL.hasFDerivAt.comp_hasDerivAt t hh)
  · exact hasDerivAt_pi.mp ((centeredGauge (Fin (n+2))).subtypeL.hasFDerivAt.comp_hasDerivAt t hv)

/-- Constants may depend on n and the bounded-direction radius: they are
used only as a local integrable domination, never as a quantitative payoff. -/
theorem exists_variance_local_bounds (η A : ℝ) (hη : 0<η) (hA : 0≤A) :
    ∀ᶠ n:ℕ in atTop, ∀ (ξ : Fin (n+2)→ℝ), (∀i,|ξ i|≤A) →
      ∀t∈Icc 0 (((n:ℝ)+2)^(-30*η)),
      ∃ (G : Set ℝ) (H K₁ K₂ : ℝ), G∈𝓝 t ∧ 0≤H ∧ 0≤K₁ ∧ 0≤K₂ ∧
        ∀z∈G,∀i,
          (1/2:ℝ)≤varianceSigma ξ z i ∧ varianceSigma ξ z i≤2 ∧
          |varianceOffsetVector n ξ z i|≤H ∧
          |sigmaVelocity ξ z i|≤K₁ ∧ |offsetVelocity n ξ z i|≤K₁ ∧
          |sigmaAcceleration ξ z i|≤K₂ ∧ |offsetAcceleration n ξ z i|≤K₂ := by
  obtain ⟨a,ha,ha1,hcontrol⟩:=exists_uniform_variance_second_control (η/2) A (by linarith) hA
  filter_upwards [hcontrol] with n hn
  let m:ℝ:=(n:ℝ)+2
  let T:ℝ:=m^(-30*(η/2))
  let H:ℝ:=|a*upperQuantile n|
  let K₁:ℝ:=A+2*A*m^(3*(η/2))
  let K₂:ℝ:=2*A^2+m^(9*(η/2))*m*A^2
  have hm : (1:ℝ) < m :=by dsimp [m];linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hT:0<T:=Real.rpow_pos_of_pos (by linarith) _
  have hK₁:0≤K₁:=by dsimp [K₁];positivity
  have hK₂:0≤K₂:=by dsimp [K₂];positivity
  have hpositive (ξ : Fin (n+2)→ℝ) (hξ:∀i,|ξ i|≤A) (z:ℝ) (hz:z∈Icc 0 T) :
      (∀i,1/2≤varianceSigma ξ z i ∧ varianceSigma ξ z i≤2) ∧
      (∀i,|varianceOffsetVector n ξ z i|≤H) ∧
      (∀i,|offsetVelocity n ξ z i|≤K₁) ∧
      (∀i,|offsetAcceleration n ξ z i|≤K₂) := by
    obtain ⟨k,hk,hkb,hbox,hoff,hsource,hacc⟩:=hn.2 ξ hξ z hz
    have hhalf:∀i,(1/2:ℝ)≤varianceSigma ξ z i:=fun i=>by linarith [(hbox i).1]
    obtain ⟨v,hv,heq⟩:=exists_variance_second_balance ξ z hhalf
    have hkd:deriv (varianceOffsets n ξ) z=k:=hk.deriv
    rw [hkd] at heq
    have hav:=(hacc v heq).1
    have hvd:deriv (deriv (varianceOffsets n ξ)) z=v:=hv.deriv
    have hE:(∑i,(ξ i)^2)≤ m*A^2:=by
      have hb (i:Fin (n+2)):(ξ i)^2≤A^2:=by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (ξ i)) (hξ i) 2
      have hs:=Finset.sum_le_sum (s:=Finset.univ) (fun i _=>hb i)
      simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat,m] using hs
    refine ⟨fun i=>⟨hhalf i,by linarith [(hbox i).2]⟩,
      fun i=>(hoff i).trans (le_abs_self _),?_,?_⟩
    · intro i
      change |((deriv (varianceOffsets n ξ) z : centeredGauge (Fin (n+2))) : Fin (n+2)→ℝ) i|≤K₁
      rw [hkd]
      have hh:=mul_le_mul_of_nonneg_left (add_le_add (hξ i) (meanAbs_le ξ A hξ))
        (Real.rpow_nonneg (by linarith : (0:ℝ)≤ m) (3*(η/2)))
      change |(k:Fin (n+2)→ℝ) i|≤K₁
      have hh':m^(3*(η/2))*(|ξ i|+meanAbs ξ)≤2*A*m^(3*(η/2)):=by nlinarith
      exact (hkb i).trans (hh'.trans (by dsimp [K₁];linarith))
    · intro i
      change |((deriv (deriv (varianceOffsets n ξ)) z : centeredGauge (Fin (n+2))) : Fin (n+2)→ℝ) i|≤K₂
      rw [hvd]
      have hi:|(v:Fin (n+2)→ℝ) i|≤∑j,|(v:Fin (n+2)→ℝ) j|:=
        Finset.single_le_sum (f:=fun j=>|(v:Fin (n+2)→ℝ) j|) (fun j _=>abs_nonneg _) (Finset.mem_univ i)
      have hE':m^(9*(η/2))*(∑j,(ξ j)^2)≤ m^(9*(η/2))*m*A^2:=by
        convert mul_le_mul_of_nonneg_left hE (Real.rpow_nonneg (by linarith : (0:ℝ)≤ m) _) using 1 <;>ring
      exact (hi.trans hav).trans (hE'.trans (by dsimp [K₂];nlinarith [sq_nonneg A]))
  intro ξ hξ t ht
  have htt:t<T:=by
    have hexp : -30*η < -30*(η/2):=by linarith
    exact ht.2.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hm hexp)
  let G:=Ioo (-T) T
  have hG:G∈𝓝 t:=Ioo_mem_nhds (by linarith [ht.1]) htt
  refine ⟨G,H,K₁,K₂,hG,abs_nonneg _,hK₁,hK₂,?_⟩
  intro z hz
  have hzT:|z|≤T:=by rw [abs_le];exact ⟨hz.1.le,hz.2.le⟩
  have hb : (∀i,1/2≤varianceSigma ξ z i ∧ varianceSigma ξ z i≤2) ∧
      (∀i,|varianceOffsetVector n ξ z i|≤H) ∧
      (∀i,|offsetVelocity n ξ z i|≤K₁) ∧
      (∀i,|offsetAcceleration n ξ z i|≤K₂):=by
    by_cases hz0:0≤z
    · exact hpositive ξ hξ z ⟨hz0,(le_abs_self z).trans hzT⟩
    · have hneg:∀i,|(-ξ) i|≤A:=by intro i;simpa using hξ i
      have hp:=hpositive (-ξ) hneg (-z) ⟨by linarith,(neg_le_abs z).trans hzT⟩
      simpa only [varianceSigma_neg_neg,varianceOffsetVector_neg_neg,
        offsetVelocity_neg_neg,offsetAcceleration_neg_neg,Pi.neg_apply,abs_neg] using hp
  intro i
  have hs₁:|sigmaVelocity ξ z i|≤A:=
    (variance_speed_abs_le (varianceSigma ξ z i) (ξ i) (hb.1 i).1).trans (hξ i)
  have hs₂:|sigmaAcceleration ξ z i|≤2*A^2:=by
    have hh:=variance_acceleration_abs_le (varianceSigma ξ z i) (ξ i) (hb.1 i).1
    have hsq:(ξ i)^2≤A^2:=by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (ξ i)) (hξ i) 2
    exact hh.trans (by nlinarith)
  refine ⟨(hb.1 i).1,(hb.1 i).2,hb.2.1 i,?_,hb.2.2.1 i,?_,hb.2.2.2 i⟩
  · exact hs₁.trans (by dsimp [K₁];exact le_add_of_nonneg_right (by positivity))
  · exact hs₂.trans (by dsimp [K₂];exact le_add_of_nonneg_right (by positivity))

end NegativeVotingVarianceLocalBounds
