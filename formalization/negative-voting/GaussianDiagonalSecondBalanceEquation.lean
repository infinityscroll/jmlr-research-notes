import GaussianSelectedOffsetSecondDerivative
import GaussianHazardPolynomialIntegralDerivative
import GaussianDiagonalSecondForcingBound

/-! Actual second derivatives of the selected diagonal balancing path.
The offset acceleration is constructed from the proved local inverse; the
physical equation is obtained by differentiating the actual zero mass flux. -/
noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Classical Topology
namespace NegativeVotingDiagonalSecondBalanceEquation
open NegativeVotingFan NegativeVotingFanInverse NegativeVotingFanJointMass
  NegativeVotingFanJointInverse NegativeVotingFanJacobian NegativeVotingFanSelectedOffsets NegativeVotingFanScore
  NegativeVotingSelectedOffsetSecondDerivative NegativeVotingDiagonalWinnerIntegral
  NegativeVotingDiagonalFacetIntegral NegativeVotingDiagonalBalancedDerivative
  NegativeVotingDiagonalBalanceEquation NegativeVotingRegularDiagonalBalance
  NegativeVotingDiagonalOffsetContinuation NegativeVotingDiagonalHazardDifferentiation
  NegativeVotingHazardKernelPathDerivative NegativeVotingHazardRawIntegralDerivative
  NegativeVotingHazardPolynomialIntegralDerivative NegativeVotingHazardSecondDifferentiation
  NegativeVotingDiagonalSecondForcingBound NegativeVotingHazardIntegrability
  NegativeVotingCapTail NegativeVotingBalancedReference
variable {n m : ℕ}

lemma varianceSigma_contDiffAt (ξ : Fin (n+2)→ℝ) (t : ℝ)
    (hpos : ∀i,0<1+t*ξ i) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k (varianceSigma ξ) t := by
  apply contDiffAt_pi.mpr
  intro i
  exact (contDiffAt_const.add (contDiffAt_id.mul contDiffAt_const)).sqrt (hpos i).ne'

lemma varianceOffsets_contDiffAt (ξ : Fin (n+2)→ℝ) (t : ℝ)
    (hpos : ∀i,0<1+t*ξ i) : ContDiffAt ℝ 1 (varianceOffsets n ξ) t := by
  have hσ:∀i,0<varianceSigma ξ t i:=fun i=>Real.sqrt_pos.2 (hpos i)
  exact (selected_diagonal_parameters_contDiffAt _ hσ (uniformMass n)
    (uniformMass_pos n) (uniformMass_sum n)).comp t (varianceSigma_contDiffAt ξ t hpos 1)

/-- Actual second differentiability of the selected offsets on every positive
variance point, without a C2-continuity hypothesis. -/
theorem varianceOffsets_deriv_differentiableAt (ξ : Fin (n+2)→ℝ) (t : ℝ)
    (hpos : ∀i,0<1+t*ξ i) :
    DifferentiableAt ℝ (deriv (varianceOffsets n ξ)) t := by
  let B:=diagonalRows (varianceSigma ξ t)
  have hσ:∀i,0<varianceSigma ξ t i:=fun i=>Real.sqrt_pos.2 (hpos i)
  obtain ⟨b,hb,hB⟩:=exists_diagonal_singular_lower (varianceSigma ξ t) hσ
  let g:ℝ→JointCoordinates (n+2) (Fin (n+2)):=fun s=>(diagonalRows (varianceSigma ξ s),0)
  have hg : ContDiffAt ℝ 2 g t:=by
    apply ContDiffAt.prodMk
    · have hc:=(diagonalRowsCLM (n+2)).contDiff.contDiffAt.comp t (varianceSigma_contDiffAt ξ t hpos 2)
      simpa only [Function.comp_def,diagonalRowsCLM_apply] using hc
    · exact contDiffAt_const
  have hf:ContDiffAt ℝ 1 (selectedJoint (d:=n+2) (uniformMass n)) (g t):=
    selectedOffsets_joint_C1 B b hb hB (uniformMass n) (uniformMass_pos n) (uniformMass_sum n)
  have hdf:=differentiableAt_fderiv_selectedJoint B b hb hB
    (uniformMass n) (uniformMass_pos n) (uniformMass_sum n)
  have hd:=differentiableAt_deriv_comp_of_fderiv (selectedJoint (d:=n+2) (uniformMass n)) g t hf hdf hg
  simp only [g,selectedJoint,Submodule.coe_zero,add_zero] at hd
  convert hd using 1 <;> rfl

lemma varianceSigma_first_hasDerivAt (ξ : Fin (n+2)→ℝ) (t : ℝ)
    (hpos : ∀i,0<1+t*ξ i) :
    HasDerivAt (fun s=>fun i=>ξ i/(2*varianceSigma ξ s i))
      (fun i=>-(ξ i)^2/(4*(varianceSigma ξ t i)^3)) t := by
  apply hasDerivAt_pi.mpr
  intro i
  have hσ:HasDerivAt (fun s=>varianceSigma ξ s i) (ξ i/(2*varianceSigma ξ t i)) t:=
    hasDerivAt_pi.mp (varianceSigma_hasDerivAt ξ t hpos) i
  have hp:0<varianceSigma ξ t i:=Real.sqrt_pos.2 (hpos i)
  have hd:=(hasDerivAt_const t (ξ i)).div (hσ.const_mul 2) (by positivity : 2*varianceSigma ξ t i≠0)
  convert hd using 1
  · field_simp
    <;>ring

lemma pairAffineIntegral_hasDerivAt (σ h : ℝ→Fin m→ℝ) (t : ℝ)
    (hσ : ∀k,ContDiffAt ℝ 1 (fun z=>σ z k) t)
    (hh : ∀k,ContDiffAt ℝ 1 (fun z=>h z k) t)
    (hpos : ∀k,0<σ t k) (i j : Fin m)
    (a b : ℝ→ℝ) (a' b' : ℝ) (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) :
    HasDerivAt (fun z=>∫x,hazardPairDensity (σ z) (h z) x i j*(a z*x+b z))
      (∫x,hazardPairDensity (σ t) (h t) x i j*
        (hazardPairLogDerivative (σ t) (h t) (pathDerivative σ t) (pathDerivative h t) x i j*
          (a t*x+b t)+(a'*x+b'))) t := by
  have hD0:=hazardPairPolynomialIntegral_integrable_hasDerivAt σ h t hσ hh hpos i j
    (fun _=>1) continuous_const 0 1 (by norm_num) (by intro x;simp)
  have hD1:=hazardPairPolynomialIntegral_integrable_hasDerivAt σ h t hσ hh hpos i j
    (fun x=>x) continuous_id 1 1 (by norm_num) (by intro x;simp)
  simp only [mul_one] at hD0
  have hI0:Integrable (fun x=>hazardPairDensity (σ t) (h t) x i j) volume:=by
    simpa using integrable_hazardPairDensity_polynomial (σ t) (h t) hpos i j 0
  have hI1:Integrable (fun x=>hazardPairDensity (σ t) (h t) x i j*x) volume:=by
    simpa using integrable_hazardPairDensity_affine (σ t) (h t) hpos i j 1 0
  have hd:=(ha.mul hD1.2).add (hb.mul hD0.2)
  have he : (∫x,hazardPairDensity (σ t) (h t) x i j*
        (hazardPairLogDerivative (σ t) (h t) (pathDerivative σ t) (pathDerivative h t) x i j*
          (a t*x+b t)+(a'*x+b'))) =
      a'*(∫x,hazardPairDensity (σ t) (h t) x i j*x)+
        a t*(∫x,hazardPairDensity (σ t) (h t) x i j*
          hazardPairLogDerivative (σ t) (h t) (pathDerivative σ t) (pathDerivative h t) x i j*x)+
      (b'*(∫x,hazardPairDensity (σ t) (h t) x i j)+
        b t*(∫x,hazardPairDensity (σ t) (h t) x i j*
          hazardPairLogDerivative (σ t) (h t) (pathDerivative σ t) (pathDerivative h t) x i j)):=by
    have hf:(fun x=>hazardPairDensity (σ t) (h t) x i j*
        (hazardPairLogDerivative (σ t) (h t) (pathDerivative σ t) (pathDerivative h t) x i j*
          (a t*x+b t)+(a'*x+b')))=fun x=>
      a'*(hazardPairDensity (σ t) (h t) x i j*x)+
        a t*(hazardPairDensity (σ t) (h t) x i j*
          hazardPairLogDerivative (σ t) (h t) (pathDerivative σ t) (pathDerivative h t) x i j*x)+
      (b'*hazardPairDensity (σ t) (h t) x i j+
        b t*(hazardPairDensity (σ t) (h t) x i j*
          hazardPairLogDerivative (σ t) (h t) (pathDerivative σ t) (pathDerivative h t) x i j)):=by funext x;ring
    have hleft:Integrable (fun x=>a'*(hazardPairDensity (σ t) (h t) x i j*x)+
        a t*(hazardPairDensity (σ t) (h t) x i j*
          hazardPairLogDerivative (σ t) (h t) (pathDerivative σ t) (pathDerivative h t) x i j*x)) volume:=
      (hI1.const_mul a').add (hD1.1.const_mul (a t))
    have hright:Integrable (fun x=>b'*hazardPairDensity (σ t) (h t) x i j+
        b t*(hazardPairDensity (σ t) (h t) x i j*
          hazardPairLogDerivative (σ t) (h t) (pathDerivative σ t) (pathDerivative h t) x i j)) volume:=
      (hI0.const_mul b').add (hD0.1.const_mul (b t))
    rw [hf,integral_add hleft hright,
      integral_add (hI1.const_mul a') (hD1.1.const_mul (a t)),
      integral_add (hI0.const_mul b') (hD0.1.const_mul (b t))]
    simp only [integral_const_mul]
  rw [he]
  apply hd.congr_of_eventuallyEq
  have hnear:∀ᶠ z in 𝓝 t,∀k,0<σ z k:=by
    rw [Filter.eventually_all]
    intro k
    exact (hσ k).continuousAt.eventually (lt_mem_nhds (hpos k))
  filter_upwards [hnear] with z hz
  have h0:Integrable (fun x=>hazardPairDensity (σ z) (h z) x i j) volume:=by
    simpa using integrable_hazardPairDensity_polynomial (σ z) (h z) hz i j 0
  have h1:Integrable (fun x=>hazardPairDensity (σ z) (h z) x i j*x) volume:=by
    simpa using integrable_hazardPairDensity_affine (σ z) (h z) hz i j 1 0
  simp only [Pi.add_apply,Pi.mul_apply]
  rw [←integral_const_mul,←integral_const_mul,←integral_add (h1.const_mul (a z)) (h0.const_mul (b z))]
  apply integral_congr_ae
  filter_upwards with x
  ring

lemma pairFluxIntegral_hasDerivAt (σ h σ₁ h₁ : ℝ→Fin m→ℝ) (t : ℝ)
    (σ₂ h₂ : Fin m→ℝ)
    (hσ : ∀k,ContDiffAt ℝ 1 (fun z=>σ z k) t)
    (hh : ∀k,ContDiffAt ℝ 1 (fun z=>h z k) t)
    (hdσ : ∀k,HasDerivAt (fun z=>σ z k) (σ₁ t k) t)
    (hdh : ∀k,HasDerivAt (fun z=>h z k) (h₁ t k) t)
    (hdσ₁ : ∀k,HasDerivAt (fun z=>σ₁ z k) (σ₂ k) t)
    (hdh₁ : ∀k,HasDerivAt (fun z=>h₁ z k) (h₂ k) t)
    (hpos : ∀k,0<σ t k) (i j : Fin m) :
    HasDerivAt (fun z=>∫x,hazardPairDensity (σ z) (h z) x i j*
      (transportSpeed (σ z i) (h z i) (σ₁ z i) (h₁ z i) x-
        transportSpeed (σ z j) (h z j) (σ₁ z j) (h₁ z j) x))
      (∫x,hazardPairDensity (σ t) (h t) x i j*
        (hazardPairLogDerivative (σ t) (h t) (σ₁ t) (h₁ t) x i j*
          (transportSpeed (σ t i) (h t i) (σ₁ t i) (h₁ t i) x-
            transportSpeed (σ t j) (h t j) (σ₁ t j) (h₁ t j) x)+
          (transportAcceleration (σ t i) (h t i) (σ₁ t i) (h₁ t i) (σ₂ i) (h₂ i) x-
            transportAcceleration (σ t j) (h t j) (σ₁ t j) (h₁ t j) (σ₂ j) (h₂ j) x))) t := by
  let a:=fun z=>σ₁ z i/σ z i-σ₁ z j/σ z j
  let b:=fun z=>transportSpeed (σ z i) (h z i) (σ₁ z i) (h₁ z i) 0-
    transportSpeed (σ z j) (h z j) (σ₁ z j) (h₁ z j) 0
  let a':=(σ₂ i/σ t i-(σ₁ t i)^2/(σ t i)^2)-(σ₂ j/σ t j-(σ₁ t j)^2/(σ t j)^2)
  let b':=transportAcceleration (σ t i) (h t i) (σ₁ t i) (h₁ t i) (σ₂ i) (h₂ i) 0-
    transportAcceleration (σ t j) (h t j) (σ₁ t j) (h₁ t j) (σ₂ j) (h₂ j) 0
  have ha:HasDerivAt a a' t:=by
    convert ((hdσ₁ i).div (hdσ i) (hpos i).ne').sub ((hdσ₁ j).div (hdσ j) (hpos j).ne') using 1
    dsimp [a']
    field_simp
    <;>ring
  have hb:HasDerivAt b b' t:=
    (transportSpeed_hasDerivAt (fun z=>σ z i) (fun z=>h z i) (fun z=>σ₁ z i) (fun z=>h₁ z i)
      t (σ₂ i) (h₂ i) 0 (hdσ i) (hdh i) (hdσ₁ i) (hdh₁ i) (hpos i)).sub
    (transportSpeed_hasDerivAt (fun z=>σ z j) (fun z=>h z j) (fun z=>σ₁ z j) (fun z=>h₁ z j)
      t (σ₂ j) (h₂ j) 0 (hdσ j) (hdh j) (hdσ₁ j) (hdh₁ j) (hpos j))
  have hDs:pathDerivative σ t=σ₁ t:=by funext k;exact (hdσ k).deriv
  have hDh:pathDerivative h t=h₁ t:=by funext k;exact (hdh k).deriv
  have hd:=pairAffineIntegral_hasDerivAt σ h t hσ hh hpos i j a b a' b' ha hb
  rw [hDs,hDh] at hd
  convert hd using 1
  · funext z
    apply integral_congr_ae
    filter_upwards with x
    dsimp [a,b,transportSpeed]
    ring
  · apply integral_congr_ae
    filter_upwards with x
    dsimp [a,b,a',b',transportSpeed,transportAcceleration]
    ring

lemma selected_diagonal_path_flux_zero (σp : ℝ→Fin (n+2)→ℝ) (t : ℝ)
    (ζ : Fin (n+2)→ℝ) (hσ : HasDerivAt σp ζ t) (hpos : ∀i,0<σp t i)
    (p : Fin (n+2)→ℝ) (hp : ∀i,0<p i) (hs : ∑i,p i=1)
    (k : centeredGauge (Fin (n+2)))
    (hk : HasDerivAt (fun s=>selectedOffsets (diagonalRows (σp s)) p) k t) (i : Fin (n+2)) :
    massFlux (σp t) (selectedOffsets (diagonalRows (σp t)) p) ζ k i=0 := by
  obtain ⟨b,hb,hB⟩:=exists_diagonal_singular_lower (σp t) hpos
  have hr:HasDerivAt (fun s=>diagonalRows (σp s)) (diagonalRows ζ) t:=by
    simpa only [Function.comp_def,diagonalRowsCLM_apply] using
      (diagonalRowsCLM (n+2)).hasFDerivAt.comp_hasDerivAt t hσ
  have ho:HasDerivAt (fun s=>(selectedOffsets (diagonalRows (σp s)) p:Fin (n+2)→ℝ))
      (k:Fin (n+2)→ℝ) t:=
    (centeredGauge (Fin (n+2))).subtypeL.hasFDerivAt.comp_hasDerivAt t hk
  have hd:=(hasFDerivAt_mass_joint_component (diagonalRows (σp t))
    (selectedOffsets (diagonalRows (σp t)) p) b hb hB i).comp_hasDerivAt t (hr.prodMk ho)
  rw [jointMassDerivativeAt_diagonal _ _ ζ _ hpos i] at hd
  have hc:HasDerivAt (fun _ : ℝ=>p i)
      (massFlux (σp t) (selectedOffsets (diagonalRows (σp t)) p) ζ k i) t:=by
    apply hd.congr_of_eventuallyEq
    have hn:∀ᶠ s in 𝓝 t,∀j,0<σp s j:=by
      rw [Filter.eventually_all]
      intro j
      exact ((continuous_apply j).continuousAt.comp hσ.continuousAt).eventually (lt_mem_nhds (hpos j))
    filter_upwards [hn] with s hs'
    exact (congrFun (selectedOffsets_mass _ (diagonalRows_injective _ hs') p hp hs) i).symm
  exact hc.unique (hasDerivAt_const t (p i))

lemma secondFlux_eq_laplacian_add_forcing (σ h σ₁ h₁ σ₂ h₂ : Fin (n+2)→ℝ)
    (hσ : ∀i,(1/2:ℝ)≤σ i) (i : Fin (n+2)) :
    (∑j∈Finset.univ.erase i,∫x,hazardPairDensity σ h x i j*
      (hazardPairLogDerivative σ h σ₁ h₁ x i j*
        (transportSpeed (σ i) (h i) (σ₁ i) (h₁ i) x-
          transportSpeed (σ j) (h j) (σ₁ j) (h₁ j) x)+
        (transportAcceleration (σ i) (h i) (σ₁ i) (h₁ i) (σ₂ i) (h₂ i) x-
          transportAcceleration (σ j) (h j) (σ₁ j) (h₁ j) (σ₂ j) (h₂ j) x))) =
      offsetLaplacian σ h h₂ i+secondForcing σ h σ₁ h₁ σ₂ i := by
  have hpos:∀i,0<σ i:=fun i=>by linarith [hσ i]
  let H₀:=∑k,|h k|
  have hH:0≤H₀:=by dsimp [H₀];positivity
  have hh:∀k,|h k|≤H₀:=fun k=>Finset.single_le_sum (f:=fun l=>|h l|) (fun l _=>abs_nonneg _) (Finset.mem_univ k)
  have hsum0 : (∑j,facetWeight (diagonalRows σ) h i j*(h₂ i-h₂ j))=
      ∑j∈Finset.univ.erase i,facetWeight (diagonalRows σ) h i j*(h₂ i-h₂ j):=by
    rw [←Finset.sum_erase_add _ _ (Finset.mem_univ i)];simp
  have hsum1 : (∑j,∫x,secondForcingDensity σ h σ₁ h₁ σ₂ i j x)=
      ∑j∈Finset.univ.erase i,∫x,secondForcingDensity σ h σ₁ h₁ σ₂ i j x:=by
    rw [←Finset.sum_erase_add _ _ (Finset.mem_univ i),secondForcingDensity_diag];simp
  unfold offsetLaplacian secondForcing
  rw [hsum0,hsum1,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hij:i≠j:=Ne.symm (Finset.mem_erase.mp hj).1
  have h0:Integrable (fun x=>hazardPairDensity σ h x i j*(h₂ i-h₂ j)) volume:=by
    simpa using integrable_hazardPairDensity_affine σ h hpos i j 0 (h₂ i-h₂ j)
  have h1:=secondForcingDensity_integrable σ h σ₁ h₁ σ₂ H₀ hσ hH hh i j
  have he:(fun x=>hazardPairDensity σ h x i j*
      (hazardPairLogDerivative σ h σ₁ h₁ x i j*
        (transportSpeed (σ i) (h i) (σ₁ i) (h₁ i) x-
          transportSpeed (σ j) (h j) (σ₁ j) (h₁ j) x)+
        (transportAcceleration (σ i) (h i) (σ₁ i) (h₁ i) (σ₂ i) (h₂ i) x-
          transportAcceleration (σ j) (h j) (σ₁ j) (h₁ j) (σ₂ j) (h₂ j) x)))=
      fun x=>hazardPairDensity σ h x i j*(h₂ i-h₂ j)+secondForcingDensity σ h σ₁ h₁ σ₂ i j x:=by
    funext x
    unfold secondForcingDensity
    unfold transportAcceleration
    ring
  rw [he,integral_add h0 h1,integral_mul_const,←facetWeight_diagonal_integral σ h hpos i j hij]

/-- The literal selected variance path has a centered acceleration, and that
actual acceleration solves the physical differentiated balancing equation. -/
theorem exists_variance_second_balance (ξ : Fin (n+2)→ℝ) (t : ℝ)
    (hσ : ∀i,(1/2:ℝ)≤varianceSigma ξ t i) :
    ∃ k₂ : centeredGauge (Fin (n+2)),
      HasDerivAt (deriv (varianceOffsets n ξ)) k₂ t ∧
      ∀i,offsetLaplacian (varianceSigma ξ t) (varianceOffsetVector n ξ t) k₂ i =
        -secondForcing (varianceSigma ξ t) (varianceOffsetVector n ξ t)
          (fun j=>ξ j/(2*varianceSigma ξ t j))
          ((deriv (varianceOffsets n ξ) t : centeredGauge (Fin (n+2))) : Fin (n+2)→ℝ)
          (fun j=>-(ξ j)^2/(4*(varianceSigma ξ t j)^3)) i := by
  have hpos:∀i,0<1+t*ξ i:=fun i=>Real.sqrt_pos.mp (show 0<varianceSigma ξ t i from by linarith [hσ i])
  have hsigpos:∀i,0<varianceSigma ξ t i:=fun i=>by linarith [hσ i]
  let σp:=varianceSigma ξ
  let hp:=varianceOffsetVector n ξ
  let σ₁:=fun s=>fun i=>ξ i/(2*varianceSigma ξ s i)
  let h₁:=fun s=>((deriv (varianceOffsets n ξ) s : centeredGauge (Fin (n+2))) : Fin (n+2)→ℝ)
  let σ₂:=fun i=>-(ξ i)^2/(4*(varianceSigma ξ t i)^3)
  let k₂:=deriv (deriv (varianceOffsets n ξ)) t
  have hk₂:HasDerivAt (deriv (varianceOffsets n ξ)) k₂ t:=
    (varianceOffsets_deriv_differentiableAt ξ t hpos).hasDerivAt
  refine ⟨k₂,hk₂,?_⟩
  have hCs:∀i,ContDiffAt ℝ 1 (fun s=>σp s i) t:=
    contDiffAt_pi.mp (varianceSigma_contDiffAt ξ t hpos 1)
  have hCh:ContDiffAt ℝ 1 hp t:=
    (centeredGauge (Fin (n+2))).subtypeL.contDiff.contDiffAt.comp t (varianceOffsets_contDiffAt ξ t hpos)
  have hds:HasDerivAt σp (σ₁ t) t:=varianceSigma_hasDerivAt ξ t hpos
  have hdh:HasDerivAt hp (h₁ t) t:=
    (centeredGauge (Fin (n+2))).subtypeL.hasFDerivAt.comp_hasDerivAt t
      ((varianceOffsets_contDiffAt ξ t hpos).differentiableAt (by norm_num)).hasDerivAt
  have hds₁:HasDerivAt σ₁ σ₂ t:=varianceSigma_first_hasDerivAt ξ t hpos
  have hdh₁:HasDerivAt h₁ (k₂:Fin (n+2)→ℝ) t:=
    (centeredGauge (Fin (n+2))).subtypeL.hasFDerivAt.comp_hasDerivAt t hk₂
  intro i
  have hpair (j:Fin (n+2)):=pairFluxIntegral_hasDerivAt σp hp σ₁ h₁ t σ₂ k₂ hCs
    (contDiffAt_pi.mp hCh) (hasDerivAt_pi.mp hds) (hasDerivAt_pi.mp hdh)
    (hasDerivAt_pi.mp hds₁) (hasDerivAt_pi.mp hdh₁) hsigpos i j
  have hsum:=HasDerivAt.fun_sum (u:=Finset.univ.erase i) (fun j _=>hpair j)
  have hn:∀ᶠ s in 𝓝 t,∀j,0<1+s*ξ j:=by
    rw [Filter.eventually_all]
    intro j
    have hc:ContinuousAt (fun s:ℝ=>1+s*ξ j) t:=by fun_prop
    exact hc.eventually (lt_mem_nhds (hpos j))
  have he:(fun _ : ℝ=>(0:ℝ))=ᶠ[𝓝 t]
      fun s=>∑j∈Finset.univ.erase i,∫x,hazardPairDensity (σp s) (hp s) x i j*
        (transportSpeed (σp s i) (hp s i) (σ₁ s i) (h₁ s i) x-
          transportSpeed (σp s j) (hp s j) (σ₁ s j) (h₁ s j) x):=by
    filter_upwards [hn] with s hs
    exact (selected_diagonal_path_flux_zero (varianceSigma ξ) s (σ₁ s)
      (varianceSigma_hasDerivAt ξ s hs) (fun j=>Real.sqrt_pos.2 (hs j))
      (uniformMass n) (uniformMass_pos n) (uniformMass_sum n)
      (deriv (varianceOffsets n ξ) s)
      ((varianceOffsets_contDiffAt ξ s hs).differentiableAt (by norm_num)).hasDerivAt i).symm
  have hz: (∑j∈Finset.univ.erase i,∫x,hazardPairDensity (σp t) (hp t) x i j*
        (hazardPairLogDerivative (σp t) (hp t) (σ₁ t) (h₁ t) x i j*
          (transportSpeed (σp t i) (hp t i) (σ₁ t i) (h₁ t i) x-
            transportSpeed (σp t j) (hp t j) (σ₁ t j) (h₁ t j) x)+
          (transportAcceleration (σp t i) (hp t i) (σ₁ t i) (h₁ t i) (σ₂ i) ((k₂:Fin (n+2)→ℝ) i) x-
            transportAcceleration (σp t j) (hp t j) (σ₁ t j) (h₁ t j) (σ₂ j) ((k₂:Fin (n+2)→ℝ) j) x)))=0:=
    (hsum.congr_of_eventuallyEq he).unique (hasDerivAt_const t 0)
  rw [secondFlux_eq_laplacian_add_forcing (σp t) (hp t) (σ₁ t) (h₁ t) σ₂ k₂ hσ i] at hz
  change offsetLaplacian (σp t) (hp t) k₂ i= -secondForcing (σp t) (hp t) (σ₁ t) (h₁ t) σ₂ i
  linarith

end NegativeVotingDiagonalSecondBalanceEquation
