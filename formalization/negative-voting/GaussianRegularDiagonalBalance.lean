import GaussianRegularTieVariance
import GaussianRegularQuadraticRepresentation
import GaussianRegularReferenceNormalization
import GaussianRegularFacetSeed

/-! Exact normalization and balancing velocity at the regular independent
Gaussian scores. The tie law is linked to the existing regular-facet scale,
and the selected derivative is solved from its actual physical Laplacian. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter WeakSimplex
open scoped BigOperators RealInnerProductSpace ENNReal Classical Topology
namespace NegativeVotingRegularDiagonalBalance
open NegativeVotingRegularTieLaw NegativeVotingRegularTieVariance
  NegativeVotingDiagonalHazardDifferentiation NegativeVotingDiagonalWinnerIntegral
  NegativeVotingDiagonalFacetIntegral NegativeVotingDiagonalScoreRealization
  NegativeVotingDiagonalBalancedDerivative NegativeVotingDiagonalBalanceEquation
  NegativeVotingFan NegativeVotingFanJacobian NegativeVotingFanSelectedOffsets
  NegativeVotingFanInverse NegativeVotingRegularQuadraticRepresentation
  NegativeVotingRegularMaximum NegativeVotingRegularReferenceNormalization
  NegativeVotingRegularFacetSeed NegativeVotingBalancedReference
variable {n m : ℕ}

def standardCenter (n : ℕ) : FSC.Coord (n+2) := WithLp.toLp 2 (fun _=>1/((n:ℝ)+2))

theorem centered_standard_rows (n : ℕ) :
    (fun i=>diagonalRows (fun _ : Fin (n+2)=>(1:ℝ)) i-standardCenter n)=canonicalEuclideanRows n := by
  ext i k
  by_cases hik:i=k
  · subst k
    simp [diagonalRows,standardCenter,canonicalEuclideanRows,canonicalRows]
  · simp [diagonalRows,standardCenter,canonicalEuclideanRows,canonicalRows,hik,Ne.symm hik]

theorem canonicalEuclideanRows_gram (n : ℕ) :
    ∀i j,inner ℝ (canonicalEuclideanRows n i) (canonicalEuclideanRows n j)=
      (if i=j then 1 else 0)-1/((n:ℝ)+2) := by
  intro i j
  simpa only [canonicalEuclideanRows,PiLp.inner_apply,WithLp.ofLp_toLp,Real.inner_apply,Nat.cast_add,Nat.cast_ofNat]
    using canonicalRows_gram n i j

theorem standard_diagonal_mass_zero (n : ℕ) :
    mass (diagonalRows (fun _ : Fin (n+2)=>(1:ℝ))) 0=fun _=>((n:ℝ)+2)⁻¹ := by
  have he:=regular_mass_zero (canonicalEuclideanRows n) (by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using canonicalEuclideanRows_gram n)
  rw [←centered_standard_rows] at he
  funext i
  have hh:=congrFun he i
  rw [mass_common_row_sub _ (diagonalRows_injective _ (by intro i;norm_num))] at hh
  simpa only [Nat.cast_add,Nat.cast_ofNat] using hh

theorem standard_selectedOffsets_zero (n : ℕ) :
    selectedOffsets (diagonalRows (fun _ : Fin (n+2)=>(1:ℝ))) (fun _=>((n:ℝ)+2)⁻¹)=0 := by
  apply selectedOffsets_eq _ _ 1 (by norm_num) (diagonal_singular_lower _ 1 (by norm_num) (by intro i;norm_num))
    (0:centeredGauge (Fin (n+2)))
  exact standard_diagonal_mass_zero n

/-- The normalized tie mass is the actual regular physical-facet scale. -/
theorem tieMass_eq_referenceScale (n : ℕ) (hn : 0<n) :
    tieMass n=referenceScale n/((n:ℝ)+2) := by
  have hij : (0:Fin (n+2))≠1:=by intro he;have hh:=congrArg Fin.val he;norm_num at hh
  have he:=facetWeight_centered_diagonal_integral
    (fun _ : Fin (n+2)=>(1:ℝ)) (fun _=>0) (by intro i;norm_num) (standardCenter n) 0 1 hij
  rw [centered_standard_rows] at he
  simp only [regular_hazardPairDensity] at he
  have hr:=regular_facetWeight hn (canonicalEuclideanRows n) (canonicalEuclideanRows_gram n) 0 1 hij
  exact he.symm.trans hr

theorem standard_massFlux (n : ℕ) (ζ k : Fin (n+2)→ℝ) (i : Fin (n+2)) :
    massFlux (fun _=>1) (fun _=>0) ζ k i=
      tieMass n*(((n:ℝ)+2)*k i-∑j,k j)+
      (∫x,tieWeight n x*x)*(((n:ℝ)+2)*ζ i-∑j,ζ j) := by
  have he (j:Fin (n+2)) :
      (∫x,hazardPairDensity (fun _ : Fin (n+2)=>(1:ℝ)) (fun _=>0) x i j*
        (transportSpeed 1 0 (ζ i) (k i) x-transportSpeed 1 0 (ζ j) (k j) x))=
      tieMass n*(k i-k j)+(∫x,tieWeight n x*x)*(ζ i-ζ j):=by
    simp only [regular_hazardPairDensity,transportSpeed,div_one,sub_zero]
    have hf : (fun x=>tieWeight n x*(k i+ζ i*x-(k j+ζ j*x)))=
        fun x=>tieWeight n x*(k i-k j)+(tieWeight n x*x)*(ζ i-ζ j):=by funext x;ring
    rw [hf,integral_add ((tieWeight_integrable n).mul_const _) ((weighted_x_integrable n).mul_const _),
      integral_mul_const,integral_mul_const]
    rfl
  unfold massFlux
  simp_rw [he]
  have hall : (∑j∈Finset.univ.erase i,(tieMass n*(k i-k j)+(∫x,tieWeight n x*x)*(ζ i-ζ j)))=
      ∑j,(tieMass n*(k i-k j)+(∫x,tieWeight n x*x)*(ζ i-ζ j)):=by
    rw [←Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp
  rw [hall,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,
    Finset.sum_sub_distrib,Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat]

theorem standard_massFlux_centered (n : ℕ) (ζ k : Fin (n+2)→ℝ)
    (hζ : ∑j,ζ j=0) (hk : ∑j,k j=0) (i : Fin (n+2)) :
    massFlux (fun _=>1) (fun _=>0) ζ k i=
      ((n:ℝ)+2)*tieMass n*(k i+tieMean n*ζ i) := by
  rw [standard_massFlux n ζ k i,hζ,hk]
  unfold tieMean
  rw [integral_tieLaw]
  field_simp [(tieMass_pos n).ne']
  ring

/-- Exact derivative of the actual selected balancing offsets in every
centered standard-deviation direction. The velocity is not postulated. -/
theorem standard_selectedOffsets_hasDerivAt (n : ℕ) (ζ : Fin (n+2)→ℝ) (hζ : ∑i,ζ i=0) :
    HasDerivAt (fun t=>selectedOffsets (diagonalRows (parameterLine (fun _=>1) ζ t))
      (fun _=>((n:ℝ)+2)⁻¹))
      ⟨fun i=>-tieMean n*ζ i,by change (∑i,-tieMean n*ζ i)=0;rw [←Finset.mul_sum,hζ,mul_zero]⟩ 0 := by
  have hp : ∀i:Fin (n+2),0<((n:ℝ)+2)⁻¹:=by intro i;positivity
  have hs : (∑i:Fin (n+2),((n:ℝ)+2)⁻¹)=1:=by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat]
    field_simp
  obtain ⟨k,hk,hflux⟩:=exists_selected_diagonal_derivative_flux (fun _ : Fin (n+2)=>(1:ℝ)) ζ
    (by intro i;norm_num) (fun _=>((n:ℝ)+2)⁻¹) hp hs
  have he : k=⟨fun i=>-tieMean n*ζ i,by change (∑i,-tieMean n*ζ i)=0;rw [←Finset.mul_sum,hζ,mul_zero]⟩:=by
    apply Subtype.ext
    funext i
    have hh:=hflux i
    rw [standard_selectedOffsets_zero] at hh
    change massFlux (fun _=>1) (fun _=>0) ζ (k:Fin (n+2)→ℝ) i=0 at hh
    rw [standard_massFlux_centered n ζ k hζ k.property i] at hh
    have hpos : 0<((n:ℝ)+2)*tieMass n:=mul_pos (by positivity) (tieMass_pos n)
    have hz : (k:Fin (n+2)→ℝ) i+tieMean n*ζ i=0:=(mul_eq_zero.mp hh).resolve_left hpos.ne'
    linarith
  simpa only [he] using hk

def diagonalRowsCLM (m : ℕ) : (Fin m→ℝ)→L[ℝ](Fin m→FSC.Coord m) :=
  ContinuousLinearMap.pi (fun i=>(ContinuousLinearMap.proj i).smulRight (EuclideanSpace.single i (1:ℝ)))

theorem diagonalRowsCLM_apply (σ : Fin m→ℝ) : diagonalRowsCLM m σ=diagonalRows σ := by
  ext i k
  by_cases hik:i=k
  · subst k
    simp [diagonalRowsCLM,diagonalRows]
  · simp [diagonalRowsCLM,diagonalRows,Pi.single,Function.update,hik,Ne.symm hik]

theorem selected_diagonal_parameters_contDiffAt (σ : Fin (n+2)→ℝ) (hσ : ∀i,0<σ i)
    (p : Fin (n+2)→ℝ) (hp : ∀i,0<p i) (hs : ∑i,p i=1) :
    ContDiffAt ℝ 1 (fun a:Fin (n+2)→ℝ=>selectedOffsets (diagonalRows a) p) σ := by
  obtain ⟨b,hb,hB⟩:=exists_diagonal_singular_lower σ hσ
  have hC:=selectedOffsets_joint_C1 (diagonalRows σ) b hb hB p hp hs
  have hP : ContDiffAt ℝ 1 (fun a:Fin (n+2)→ℝ=>(diagonalRows a,(0:centeredGauge (Fin (n+2))))) σ:=by
    apply ContDiffAt.prodMk
    · have he : (diagonalRowsCLM (n+2) : (Fin (n+2)→ℝ)→(Fin (n+2)→FSC.Coord (n+2)))=diagonalRows:=funext diagonalRowsCLM_apply
      rw [←he]
      exact (diagonalRowsCLM (n+2)).contDiff.contDiffAt
    · exact contDiffAt_const
  simpa only [Function.comp_def,Submodule.coe_zero,add_zero] using hC.comp
    (f:=fun a:Fin (n+2)→ℝ=>(diagonalRows a,(0:centeredGauge (Fin (n+2))))) σ hP

theorem standard_selectedOffsets_hasDerivAt_of_path (n : ℕ) (σp : ℝ→Fin (n+2)→ℝ)
    (ζ : Fin (n+2)→ℝ) (hζ : ∑i,ζ i=0) (hbase : σp 0=fun _=>1)
    (hσp : HasDerivAt σp ζ 0) :
    HasDerivAt (fun t=>selectedOffsets (diagonalRows (σp t)) (fun _=>((n:ℝ)+2)⁻¹))
      ⟨fun i=>-tieMean n*ζ i,by change (∑i,-tieMean n*ζ i)=0;rw [←Finset.mul_sum,hζ,mul_zero]⟩ 0 := by
  have hp : ∀i:Fin (n+2),0<((n:ℝ)+2)⁻¹:=by intro i;positivity
  have hs : (∑i:Fin (n+2),((n:ℝ)+2)⁻¹)=1:=by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat]
    field_simp
  let f:=fun a:Fin (n+2)→ℝ=>selectedOffsets (diagonalRows a) (fun _=>((n:ℝ)+2)⁻¹)
  have hf : DifferentiableAt ℝ f (fun _=>1):=
    (selected_diagonal_parameters_contDiffAt (fun _=>1) (by intro i;norm_num) _ hp hs).differentiableAt (by norm_num)
  have hf0 : HasFDerivAt f (fderiv ℝ f (fun _=>1)) (parameterLine (fun _=>1) ζ 0):=by
    have he : parameterLine (fun _ : Fin (n+2)=>(1:ℝ)) ζ 0=(fun _=>1):=by funext i;simp [parameterLine]
    rw [he]
    exact hf.hasFDerivAt
  have ha:=hf0.comp_hasDerivAt (f:=parameterLine (fun _=>1) ζ) 0 (parameterLine_hasDerivAt (fun _=>1) ζ)
  have he := ha.unique (standard_selectedOffsets_hasDerivAt n ζ hζ)
  have hf' : HasFDerivAt f (fderiv ℝ f (fun _=>1)) (σp 0):=by rw [hbase];exact hf.hasFDerivAt
  have hd:=hf'.comp_hasDerivAt 0 hσp
  rw [he] at hd
  exact hd

/-- The source's variance parametrization v_i(t)=1+t ξ_i has the claimed
actual balancing derivative h_i′(0)=−M ξ_i/2. -/
theorem standard_variance_selectedOffsets_hasDerivAt (n : ℕ) (ξ : Fin (n+2)→ℝ) (hξ : ∑i,ξ i=0) :
    HasDerivAt (fun t=>selectedOffsets (diagonalRows (fun i=>Real.sqrt (1+t*ξ i)))
      (fun _=>((n:ℝ)+2)⁻¹))
      ⟨fun i=>-tieMean n*(ξ i/2),by change (∑i,-tieMean n*(ξ i/2))=0;rw [←Finset.mul_sum,←Finset.sum_div,hξ,zero_div,mul_zero]⟩ 0 := by
  apply standard_selectedOffsets_hasDerivAt_of_path n (fun t i=>Real.sqrt (1+t*ξ i))
    (fun i=>ξ i/2) (by rw [←Finset.sum_div,hξ,zero_div]) (by funext i;norm_num)
  apply hasDerivAt_pi.mpr
  intro i
  have hp : HasDerivAt (fun t:ℝ=>1+t*ξ i) (ξ i) 0:=by
    simpa only [id_eq,one_mul] using ((hasDerivAt_id (0:ℝ)).mul_const (ξ i)).const_add 1
  have hq : HasDerivAt Real.sqrt (1/(2*Real.sqrt (1+(0:ℝ)*ξ i))) (1+(0:ℝ)*ξ i):=
    Real.hasDerivAt_sqrt (by norm_num)
  convert hq.comp 0 hp using 1
  · rfl
  · norm_num
    ring

end NegativeVotingRegularDiagonalBalance
