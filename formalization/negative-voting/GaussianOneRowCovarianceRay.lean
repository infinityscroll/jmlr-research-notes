import GaussianOneRowCurvature
import GaussianCovarianceOptimizerDegree

/-! The literal fixed-label covariance ray. Its incident edge lengths and
normal strains are computed exactly, then the actual one-row covariance
curvature theorem supplies the second derivative. -/
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped BigOperators Classical RealInnerProductSpace Topology
namespace NegativeVotingOneRowCovarianceRay
open NegativeVoting NegativeVotingOneRowCurvature NegativeVotingPositiveCovariance
  NegativeVotingCovarianceConcavity NegativeVotingCovarianceOptimizerDegree
  NegativeVotingLocalCurvatureAlgebra
variable {m d:ℕ} [NeZero m]

def rowProjector (b:Fin m→FSC.Coord d) (i:Fin m) : FSC.Coord d→L[ℝ]FSC.Coord d :=
  ((m:ℝ)/((m:ℝ)-1))•rankOne (b i)

def transverseCoefficient (m:ℕ) (a:ℝ) : ℝ := ((m:ℝ)-1-a)/((m:ℝ)-2)

def oneRowCovariance (b:Fin m→FSC.Coord d) (i:Fin m) (a:ℝ) : FSC.Coord d→L[ℝ]FSC.Coord d :=
  a•rowProjector b i+transverseCoefficient m a•(ContinuousLinearMap.id ℝ (FSC.Coord d)-rowProjector b i)

def oneRowDirection (b:Fin m→FSC.Coord d) (i:Fin m) : FSC.Coord d→L[ℝ]FSC.Coord d :=
  rowProjector b i-((m:ℝ)-2)⁻¹•(ContinuousLinearMap.id ℝ (FSC.Coord d)-rowProjector b i)

theorem rowProjector_symmetric (b:Fin m→FSC.Coord d) (i:Fin m) :
    (rowProjector b i).toLinearMap.IsSymmetric :=
  (rankOne_psd (b i)).1.smul (by rfl)

theorem rowProjector_pairing (b:Fin m→FSC.Coord d) (i:Fin m) (x:FSC.Coord d) :
    inner ℝ x (rowProjector b i x)=((m:ℝ)/((m:ℝ)-1))*(inner ℝ (b i) x)^2 := by
  simp only [rowProjector,ContinuousLinearMap.smul_apply,real_inner_smul_right,rankOne_pairing]

theorem rowProjector_bounds (hm:2≤ m) (b:Fin m→FSC.Coord d)
    (hG:∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (i:Fin m) (x:FSC.Coord d) :
    0≤ inner ℝ x (rowProjector b i x) ∧ inner ℝ x (rowProjector b i x)≤‖x‖^2 := by
  have hm0 : (0:ℝ)< m := by exact_mod_cast (by omega : 0< m)
  have hm1 : (0:ℝ)<(m:ℝ)-1 := by
    have hh : (2:ℝ)≤ m := by exact_mod_cast hm
    linarith
  rw [rowProjector_pairing]
  constructor
  · positivity
  · have hh:=real_inner_mul_inner_self_le (b i) x
    rw [hG,if_pos rfl,real_inner_self_eq_norm_sq] at hh
    have hh':=mul_le_mul_of_nonneg_left hh (show 0≤(m:ℝ)/((m:ℝ)-1) by positivity)
    have hc : (m:ℝ)/((m:ℝ)-1)*(1-1/(m:ℝ))=1 := by field_simp <;> ring
    have hprod : (m:ℝ)/((m:ℝ)-1)*((1-1/(m:ℝ))*‖x‖^2)=‖x‖^2 := by
      rw [←mul_assoc,hc,one_mul]
    rw [hprod] at hh'
    nlinarith only [hh']

theorem oneRowCovariance_pairing (b:Fin m→FSC.Coord d) (i:Fin m) (a:ℝ) (x:FSC.Coord d) :
    inner ℝ x (oneRowCovariance b i a x)=
      a*inner ℝ x (rowProjector b i x)+transverseCoefficient m a*(‖x‖^2-inner ℝ x (rowProjector b i x)) := by
  simp only [oneRowCovariance,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,inner_add_right,real_inner_smul_right,
    inner_sub_right,real_inner_self_eq_norm_sq]

theorem oneRowCovariance_symmetric (b:Fin m→FSC.Coord d) (i:Fin m) (a:ℝ) :
    (oneRowCovariance b i a).toLinearMap.IsSymmetric := by
  have hP:=rowProjector_symmetric b i
  have hI : (ContinuousLinearMap.id ℝ (FSC.Coord d)).toLinearMap.IsSymmetric := by intro x y;rfl
  exact (hP.smul (by rfl)).add ((hI.sub hP).smul (by rfl))

theorem oneRowDirection_symmetric (b:Fin m→FSC.Coord d) (i:Fin m) :
    (oneRowDirection b i).toLinearMap.IsSymmetric := by
  have hP:=rowProjector_symmetric b i
  have hI : (ContinuousLinearMap.id ℝ (FSC.Coord d)).toLinearMap.IsSymmetric := by intro x y;rfl
  exact hP.sub ((hI.sub hP).smul (by rfl))

theorem oneRowCovariance_psd (hm:3≤ m) (b:Fin m→FSC.Coord d)
    (hG:∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (i:Fin m) (a:ℝ) (ha:0≤ a) (ha1:a≤(m:ℝ)-1) : oneRowCovariance b i a∈psdCone := by
  refine ⟨oneRowCovariance_symmetric b i a,?_⟩
  intro x
  rw [oneRowCovariance_pairing]
  have hb:0≤ transverseCoefficient m a := by
    unfold transverseCoefficient
    apply div_nonneg (by linarith)
    have hh:(3:ℝ)≤ m := by exact_mod_cast hm
    linarith
  obtain ⟨h0,h1⟩:=rowProjector_bounds (by omega) b hG i x
  exact add_nonneg (mul_nonneg ha h0) (mul_nonneg hb (sub_nonneg.mpr h1))

theorem oneRowCovariance_positive (hm:3≤ m) (b:Fin m→FSC.Coord d)
    (hG:∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (i:Fin m) (a:ℝ) (ha:0< a) (ha1:a<(m:ℝ)-1) : oneRowCovariance b i a∈pdCone := by
  refine ⟨oneRowCovariance_symmetric b i a,?_⟩
  intro x hx
  rw [oneRowCovariance_pairing]
  have hb:0< transverseCoefficient m a := by
    unfold transverseCoefficient
    apply div_pos (by linarith)
    have hh:(3:ℝ)≤ m := by exact_mod_cast hm
    linarith
  obtain ⟨h0,h1⟩:=rowProjector_bounds (by omega) b hG i x
  have hs:0<‖x‖^2:=sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hmin:0< min a (transverseCoefficient m a):=lt_min ha hb
  have hq:=mul_le_mul_of_nonneg_right (min_le_left a (transverseCoefficient m a)) h0
  have hr:=mul_le_mul_of_nonneg_right (min_le_right a (transverseCoefficient m a)) (sub_nonneg.mpr h1)
  have hh:=mul_pos hmin hs
  nlinarith only [hq,hr,hh]

theorem oneRowCovariance_affine (b:Fin m→FSC.Coord d) (i:Fin m) (a t:ℝ) :
    oneRowCovariance b i (a+t)=oneRowCovariance b i a+t•oneRowDirection b i := by
  simp only [oneRowCovariance,oneRowDirection,transverseCoefficient,div_eq_mul_inv]
  module

theorem rowProjector_incident (hm:2≤ m) (b:Fin m→FSC.Coord d)
    (hG:∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (i j:Fin m) (hji:j≠i) :
    inner ℝ (b i-b j) (rowProjector b i (b i-b j))=(m:ℝ)/((m:ℝ)-1) := by
  rw [rowProjector_pairing,inner_sub_right,hG,hG,if_pos rfl,if_neg (Ne.symm hji)]
  ring

theorem oneRowCovariance_incident (hm:3≤ m) (b:Fin m→FSC.Coord d)
    (hG:∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (i j:Fin m) (hji:j≠i) (a:ℝ) :
    inner ℝ (b i-b j) (oneRowCovariance b i a (b i-b j))=a+1 := by
  rw [oneRowCovariance_pairing,rowProjector_incident (by omega) b hG i j hji,
    regular_edge_norm_sq b hG i j (Ne.symm hji)]
  have hm1 : (m:ℝ)-1≠0 := by
    have hh:(3:ℝ)≤ m := by exact_mod_cast hm
    linarith
  have hm2 : (m:ℝ)-2≠0 := by
    have hh:(3:ℝ)≤ m := by exact_mod_cast hm
    linarith
  unfold transverseCoefficient
  field_simp
  <;> ring

theorem oneRowDirection_incident (hm:3≤ m) (b:Fin m→FSC.Coord d)
    (hG:∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (i j:Fin m) (hji:j≠i) :
    inner ℝ (b i-b j) (oneRowDirection b i (b i-b j))=1 := by
  change inner ℝ (b i-b j) (rowProjector b i (b i-b j)-((m:ℝ)-2)⁻¹•((b i-b j)-rowProjector b i (b i-b j)))=1
  rw [inner_sub_right,real_inner_smul_right,inner_sub_right,real_inner_self_eq_norm_sq]
  rw [rowProjector_incident (by omega) b hG i j hji,regular_edge_norm_sq b hG i j (Ne.symm hji)]
  have hm1 : (m:ℝ)-1≠0 := by
    have hh:(3:ℝ)≤ m := by exact_mod_cast hm
    linarith
  have hm2 : (m:ℝ)-2≠0 := by
    have hh:(3:ℝ)≤ m := by exact_mod_cast hm
    linarith
  field_simp
  <;> ring

/-- Actual derivatives along the fixed-label ray. The balanced offsets and
all facet weights are constructed; the only coefficient loss is the explicit
Cheeger constant already proved in GaussianOneRowCurvature. -/
theorem exists_oneRowValue_derivatives (hm:3≤ m)
    (b:AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hG:∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (p:Fin m→ℝ) (hp:∀ j,0< p j) (hs:∑ j,p j=1)
    (pmin:ℝ) (hpmin:0≤ pmin) (hmin:∀ j,pmin≤ p j)
    (i:Fin m) (a:ℝ) (ha:0< a) (ha1:a<(m:ℝ)-1) :
    ∃ v q:ℝ,HasDerivAt (fun t:ℝ=> operatorValue b p (oneRowCovariance b i t)) v a ∧
      HasDerivAt (deriv (fun t:ℝ=> operatorValue b p (oneRowCovariance b i t))) q a ∧
      q≤-pmin/(16*Real.pi*(Real.sqrt (a+1))^3) := by
  have hsqrt:0< Real.sqrt (a+1):=Real.sqrt_pos.mpr (by linarith)
  obtain ⟨v,q,hv,hq,hbound⟩:=exists_one_row_covariance_derivatives (by omega) b p hp hs pmin hpmin hmin
    (oneRowCovariance b i a) (oneRowDirection b i) (oneRowCovariance_positive hm b hG i a ha ha1)
    (oneRowDirection_symmetric b i) i (Real.sqrt (a+1)) hsqrt
    (fun j hj=>(oneRowCovariance_incident hm b hG i j hj a).trans (Real.sq_sqrt (by linarith)).symm)
    (fun j hj=> oneRowDirection_incident hm b hG i j hj)
  have heq : (fun t:ℝ=> operatorValue b p (oneRowCovariance b i a+t•oneRowDirection b i))=
      (fun t:ℝ=> operatorValue b p (oneRowCovariance b i (a+t))) := by
    funext t
    rw [oneRowCovariance_affine]
  rw [heq] at hv hq
  have hder : deriv (fun t:ℝ=> operatorValue b p (oneRowCovariance b i (a+t)))=
      (fun t:ℝ=> deriv (fun u:ℝ=> operatorValue b p (oneRowCovariance b i u)) (a+t)) := by
    funext t
    exact deriv_comp_const_add (fun u:ℝ=>operatorValue b p (oneRowCovariance b i u)) a t
  rw [hder] at hq
  exact ⟨v,q,hasDerivAt_of_const_add_zero a v hv,hasDerivAt_of_const_add_zero a q hq,hbound⟩

end NegativeVotingOneRowCovarianceRay
