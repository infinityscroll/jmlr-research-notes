import GaussianBoundaryHighChaosTrace
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.InnerProductSpace.Dual

/-! The actual bounded ordered boundary pairing and its Riesz representative.
Trace integrability, representative-independent linearity, the actual high-degree
Gaussian L² subspace, and a bounded Hilbert representative are constructed here.
Identification with a moving-cell derivative and path integration remain
separate obligations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin
open NegativeVotingHypercontractivity NegativeVotingSmoothingComposition
open NegativeVotingDisintegration NegativeVotingNormalTrace
open NegativeVotingPolynomialFacetGeometricTrace NegativeVotingActualFacetOUTrace
open NegativeVotingBoundaryTraceAggregation NegativeVotingBoundaryHighChaosTrace
open OAI.MinUncut.GaussianHermite
open scoped ENNReal BigOperators

namespace NegativeVotingBoundaryFunctionalRiesz

section Plane
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Actual whole-plane L² membership, needed independently of any inequality
between real-valued integrals. -/
theorem ambientAverage_plane_memLp_two {n : ℕ} (w : E) (hw : ‖w‖=1)
    (e : tangentSpace w ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (a : ℝ)
    (f : E → ℝ) (hfM : Measurable f) (hf : MemLp f 2 (stdGaussian E)) :
    MemLp (fun y : tangentSpace w => ambientAverage ρ f ((y:E)+a • w)) 2
      (stdGaussian (tangentSpace w)) := by
  let g := fun z : (Fin n → ℝ) × ℝ => f (coordinateReconstruct w e z)
  have hgm := (coordinateReconstruct_memLp_and_norm w hw e f 2 hf).1
  change MemLp g 2 ((γFin n).prod (gaussianReal 0 1)) at hgm
  have hs : ρ^2 < 1 := by nlinarith
  have hsection := (normalSection_memLp_and_integral_sq_le hs a g hgm).1
  have htrace : MemLp (normalTrace ρ a g) 2 (γFin n) :=
    gaussianAverage_memLp_two hρ hρ1 _ hsection
  have he := normalTrace_eq_product_ae hρ hρ1 a g hgm
  have hact : (fun y => ambientAverage ρ f ((tangentCoordinatesInverse w e y:E)+a • w)) =ᵐ[γFin n]
      normalTrace ρ a g := by
    filter_upwards [he] with y hy
    have hcoord : (tangentCoordinatesInverse w e y:E)+a • w =
        coordinateReconstruct w e (y,a) := rfl
    rw [hcoord,ambientAverage_coordinateReconstruct w hw e ρ f hfM]
    exact hy.symm
  have hmem := htrace.ae_eq hact.symm
  have hT : Measurable (tangentCoordinatesInverse w e) := by
    unfold tangentCoordinatesInverse
    fun_prop
  have hM : Measurable (fun y : tangentSpace w => ambientAverage ρ f ((y:E)+a • w)) :=
    (ambientAverage_measurable ρ f hfM).comp (by fun_prop)
  rw [←tangentCoordinatesInverse_map w e]
  exact (memLp_map_measure_iff hM.aestronglyMeasurable hT.aemeasurable).mpr hmem

end Plane

section PlaneLinearity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Linearity on a fixed affine plane, including ambient AE changes of input
representative. The normal-kernel argument is essential: an ambient AE identity
alone cannot be restricted to a plane. -/
theorem ambientAverage_plane_linear_ae {n : ℕ} (w : E) (hw : ‖w‖=1)
    (e : tangentSpace w ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (a c : ℝ)
    (f g h : E → ℝ) (hfM : Measurable f) (hgM : Measurable g) (hhM : Measurable h)
    (hf : MemLp f 2 (stdGaussian E)) (hg : MemLp g 2 (stdGaussian E))
    (hh : h =ᵐ[stdGaussian E] fun x => f x+c*g x) :
    ∀ᵐ y : tangentSpace w ∂stdGaussian (tangentSpace w),
      ambientAverage ρ h ((y:E)+a • w) =
        ambientAverage ρ f ((y:E)+a • w)+c*ambientAverage ρ g ((y:E)+a • w) := by
  let f' := fun z => f (coordinateReconstruct w e z)
  let g' := fun z => g (coordinateReconstruct w e z)
  let h' := fun z => h (coordinateReconstruct w e z)
  have hf' := (coordinateReconstruct_memLp_and_norm w hw e f 2 hf).1
  have hg' := (coordinateReconstruct_memLp_and_norm w hw e g 2 hg).1
  have hh' : h' =ᵐ[(γFin n).prod (gaussianReal 0 1)] fun z => f' z+c*g' z := by
    have hmp : MeasurePreserving (coordinateReconstruct w e)
        ((γFin n).prod (gaussianReal 0 1)) (stdGaussian E) :=
      ⟨by unfold coordinateReconstruct; fun_prop, coordinateReconstruct_map w hw e⟩
    exact hmp.quasiMeasurePreserving.ae hh
  have hhm : MemLp h' 2 ((γFin n).prod (gaussianReal 0 1)) :=
    (hf'.add (hg'.const_mul c)).ae_eq hh'.symm
  have hs : ρ^2 < 1 := by nlinarith
  have hfinite : ∀ᵐ y ∂γFin n,
      ambientAverage ρ h ((tangentCoordinatesInverse w e y:E)+a • w) =
        ambientAverage ρ f ((tangentCoordinatesInverse w e y:E)+a • w)+
          c*ambientAverage ρ g ((tangentCoordinatesInverse w e y:E)+a • w) := by
    filter_upwards [NegativeVotingNormalDerivatives.normalTrace_congr_ae_all_parameters hs hh',
      normalTrace_eq_product_ae hρ hρ1 a h' hhm,
      normalTrace_eq_product_ae hρ hρ1 a (fun z => f' z+c*g' z) (hf'.add (hg'.const_mul c)),
      actual_normal_kernel_integrable_ae hs a f' hf',
      actual_normal_kernel_integrable_ae hs a g' hg'] with y he hhx hsum hi hj
    have hcoord : (tangentCoordinatesInverse w e y:E)+a • w = coordinateReconstruct w e (y,a) := rfl
    rw [hcoord, ambientAverage_coordinateReconstruct w hw e ρ h hhM,
      ambientAverage_coordinateReconstruct w hw e ρ f hfM,
      ambientAverage_coordinateReconstruct w hw e ρ g hgM]
    change productGaussianAverage ρ h' (y,a) = productGaussianAverage ρ f' (y,a)+c*productGaussianAverage ρ g' (y,a)
    unfold productGaussianAverage
    rw [←hhx,he a,hsum]
    rw [integral_add hi (hj.const_mul c),integral_const_mul]
  rw [←tangentCoordinatesInverse_map w e]
  apply (ae_map_iff (show AEMeasurable (tangentCoordinatesInverse w e) (γFin n) from by
    apply Measurable.aemeasurable
    unfold tangentCoordinatesInverse
    fun_prop) ?_).mpr hfinite
  apply measurableSet_eq_fun
  · exact (ambientAverage_measurable ρ h hhM).comp (by fun_prop)
  · exact ((ambientAverage_measurable ρ f hfM).comp (by fun_prop)).add
      (((ambientAverage_measurable ρ g hgM).comp (by fun_prop)).const_mul c)

end PlaneLinearity

section FiniteCauchy
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (X : ι → ι → Type*) [∀ i j, MeasurableSpace (X i j)]
  (μ : ∀ i j, Measure (X i j))

/-- Weighted Cauchy--Schwarz on the literal boundary integrals, including
the physical edge length in the speed energy and its reciprocal in the trace. -/
theorem ordered_weighted_pairing_sq_le
    (v z : ∀ i j, X i j → ℝ) (c ell : ι → ι → ℝ)
    (hc : ∀ i j, 0 ≤ c i j) (hell : ∀ i j, i≠j → 0 < ell i j)
    (hv : ∀ i j, i≠j → MemLp (v i j) 2 (μ i j))
    (hz : ∀ i j, i≠j → MemLp (z i j) 2 (μ i j)) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, c i j * ∫ x,v i j x*z i j x ∂μ i j)^2 ≤
      (∑ i, ∑ j ∈ Finset.univ.erase i, c i j*ell i j * ∫ x,(v i j x)^2 ∂μ i j)*
        (∑ i, ∑ j ∈ Finset.univ.erase i, c i j/ell i j * ∫ x,(z i j x)^2 ∂μ i j) := by
  let R := fun i j => c i j * ∫ x,v i j x*z i j x ∂μ i j
  let A := fun i j => c i j*ell i j * ∫ x,(v i j x)^2 ∂μ i j
  let B := fun i j => c i j/ell i j * ∫ x,(z i j x)^2 ∂μ i j
  have hA i j (hij : i≠j) : 0 ≤ A i j :=
    mul_nonneg (mul_nonneg (hc i j) (hell i j hij).le) (integral_nonneg (fun _ => sq_nonneg _))
  have hB i j (hij : i≠j) : 0 ≤ B i j :=
    mul_nonneg (div_nonneg (hc i j) (hell i j hij).le) (integral_nonneg (fun _ => sq_nonneg _))
  have hR i j (hij : i≠j) : (R i j)^2 ≤ A i j*B i j := by
    have h := mul_le_mul_of_nonneg_left (integral_mul_sq_le (hv i j hij) (hz i j hij))
      (sq_nonneg (c i j))
    change (c i j*(∫ x,v i j x*z i j x ∂μ i j))^2 ≤
      (c i j*ell i j*(∫ x,(v i j x)^2 ∂μ i j))*
        (c i j/ell i j*(∫ x,(z i j x)^2 ∂μ i j))
    have he : (c i j*ell i j*(∫ x,(v i j x)^2 ∂μ i j))*
        (c i j/ell i j*(∫ x,(z i j x)^2 ∂μ i j)) =
        (c i j)^2*((∫ x,(v i j x)^2 ∂μ i j)*(∫ x,(z i j x)^2 ∂μ i j)) := by
      field_simp [ne_of_gt (hell i j hij)]
    rw [he,mul_pow]
    exact h
  have hrow i : (∑ j ∈ Finset.univ.erase i, R i j)^2 ≤
      (∑ j ∈ Finset.univ.erase i, A i j)*(∑ j ∈ Finset.univ.erase i, B i j) :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _
      (fun j hj => hA i j (Finset.mem_erase.mp hj).1.symm)
      (fun j hj => hB i j (Finset.mem_erase.mp hj).1.symm)
      (fun j hj => hR i j (Finset.mem_erase.mp hj).1.symm)
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun i _ => Finset.sum_nonneg (fun j hj => hA i j (Finset.mem_erase.mp hj).1.symm))
    (fun i _ => Finset.sum_nonneg (fun j hj => hB i j (Finset.mem_erase.mp hj).1.symm))
    (fun i _ => hrow i)

end FiniteCauchy

section ActualBoundary
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Literal ordered surface pairing. For an antisymmetric physical speed the
usual unoriented boundary functional is half of this ordered sum. -/
def orderedBoundaryPairing (w : ι → ι → FSC.Coord d) (a : ι → ι → ℝ)
    (F : ∀ i j, Set (tangentSpace (w i j)))
    (v : ∀ i j, tangentSpace (w i j) → ℝ) (ρ : ℝ) (f : ι → FSC.Coord d → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, gaussianPDFReal 0 1 (a i j) *
    ∫ y in F i j, v i j y * ambientAverage ρ (fun x => f i x-f j x)
      ((y:FSC.Coord d)+(a i j) • w i j) ∂stdGaussian (tangentSpace (w i j))

def orderedSpeedEnergy (w : ι → ι → FSC.Coord d) (a ell : ι → ι → ℝ)
    (F : ∀ i j, Set (tangentSpace (w i j)))
    (v : ∀ i j, tangentSpace (w i j) → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, gaussianPDFReal 0 1 (a i j)*ell i j *
    ∫ y in F i j,(v i j y)^2 ∂stdGaussian (tangentSpace (w i j))

/-- The actual bounded boundary functional estimate, derived from the trace
theorem and the actual boundary speed energy. No desired L² representing-vector
bound is assumed. This is the bound needed for a subsequent Riesz extension. -/
theorem orderedBoundaryPairing_sq_le {n : ι → ι → ℕ}
    (w : ι → ι → FSC.Coord d) (a ell : ι → ι → ℝ)
    (F : ∀ i j, Set (tangentSpace (w i j)))
    (e : ∀ i j, i≠j → tangentSpace (w i j) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n i j)))
    (v : ∀ i j, tangentSpace (w i j) → ℝ)
    (hv : ∀ i j, i≠j → MemLp (v i j) 2 ((stdGaussian (tangentSpace (w i j))).restrict (F i j)))
    (τ σ q ell0 G : ℝ) (hτ : 0 < τ) (hσ : 0 < σ) (hσ1 : σ < 1)
    (hq : 2 ≤ q) (ht : τ^2=1/(2*q-1)) (hell0 : 0 < ell0) (hG : 0 ≤ G)
    (hw : ∀ i j, i≠j → ‖w i j‖=1)
    (hF : ∀ i j, i≠j → MeasurableSet (F i j))
    (hell : ∀ i j, i≠j → ell0 ≤ ell i j)
    (hμsym : ∀ i j, planeSurfaceMass w a F i j=planeSurfaceMass w a F j i)
    (hellsym : ∀ i j, ell i j=ell j i)
    (hdegree : ∀ i, (∑ j ∈ Finset.univ.erase i, planeSurfaceMass w a F i j/ell i j) ≤ G)
    (f : ι → FSC.Coord d → ℝ) (hfM : ∀ i, Measurable (f i))
    (hf : ∀ i, MemLp (f i) 2 (stdGaussian (FSC.Coord d)))
    (k : ℕ) (hvanish : ∀ i b, degree b < k →
      coeff (fun x : Fin d → ℝ => f i (WithLp.toLp 2 x)) b=0) :
    (orderedBoundaryPairing w a F v (τ*σ) f)^2 ≤
      8*traceCoefficient (ι := ι) ell0 G q*(σ^2)^k * orderedSpeedEnergy w a ell F v *
        ∑ i, ∫ x,(f i x)^2 ∂stdGaussian (FSC.Coord d) := by
  have hτsq : τ^2 < 1 := by
    rw [ht]
    apply (div_lt_one (by linarith : 0<2*q-1)).mpr
    linarith
  have hτ1 : τ<1 := by nlinarith
  have hprod1 : τ*σ < 1 := (mul_lt_mul_of_pos_left hσ1 hτ).trans (by simpa using hτ1)
  let z := fun i j (y : tangentSpace (w i j)) =>
    ambientAverage (τ*σ) (fun x => f i x-f j x) ((y:FSC.Coord d)+(a i j) • w i j)
  have hz i j (hij : i≠j) : MemLp (z i j) 2
      ((stdGaussian (tangentSpace (w i j))).restrict (F i j)) :=
    (ambientAverage_plane_memLp_two (w i j) (hw i j hij) (e i j hij)
      (mul_pos hτ hσ) hprod1 (a i j) (fun x => f i x-f j x)
      ((hfM i).sub (hfM j)) ((hf i).sub (hf j))).restrict (F i j)
  have hC := ordered_weighted_pairing_sq_le (fun i j => tangentSpace (w i j))
    (fun i j => (stdGaussian (tangentSpace (w i j))).restrict (F i j)) v z
    (fun i j => gaussianPDFReal 0 1 (a i j)) ell
    (fun _ _ => gaussianPDFReal_nonneg _ _ _) (fun i j hij => hell0.trans_le (hell i j hij)) hv hz
  have hN : 0 ≤ orderedSpeedEnergy w a ell F v := by
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    have hij := (Finset.mem_erase.mp hj).1.symm
    exact mul_nonneg
      (mul_nonneg (gaussianPDFReal_nonneg _ _ _) (hell0.le.trans (hell i j hij)))
      (integral_nonneg (fun _ => sq_nonneg _))
  have htrace := ambient_ordered_highChaos_trace_energy_le w a ell F e τ σ q ell0 G
    hτ hσ hσ1 hq ht hell0 hG hw hF hell hμsym hellsym hdegree f hfM hf k hvanish
  have hh := mul_le_mul_of_nonneg_left htrace hN
  change (orderedBoundaryPairing w a F v (τ*σ) f)^2 ≤
    orderedSpeedEnergy w a ell F v * _ at hC
  exact hC.trans (by nlinarith only [hh])

end ActualBoundary

section L2Functional
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Finite label families with the Hilbert (sum-of-squares) norm. -/
abbrev BoundaryL2 (d : ℕ) (ι : Type*) [Fintype ι] :=
  PiLp 2 (fun _ : ι => Lp ℝ 2 (stdGaussian (FSC.Coord d)))

omit [DecidableEq ι] in
theorem boundaryL2_norm_sq (f : BoundaryL2 d ι) :
    ‖f‖^2 = ∑ i, ∫ x,(f i x)^2 ∂stdGaussian (FSC.Coord d) := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro i hi
  rw [←real_inner_self_eq_norm_sq,MeasureTheory.L2.inner_def]
  simp only [Real.inner_apply,pow_two]

/-- Original-coordinate Hermite coefficient as a linear functional on the
actual Gaussian L² label space. -/
def boundaryCoefficient (i : ι) (b : Fin d → ℕ) : BoundaryL2 d ι →ₗ[ℝ] ℝ where
  toFun f := coeff (fun x : Fin d → ℝ => f i (WithLp.toLp 2 x)) b
  map_add' f g := by
    have hT := NegativeVotingConditionalSecondMoment.gaussian_toLp_measurePreserving d
    have he := hT.quasiMeasurePreserving.ae (Lp.coeFn_add (f i) (g i))
    have hf := (Lp.memLp (f i)).comp_measurePreserving hT
    have hg := (Lp.memLp (g i)).comp_measurePreserving hT
    unfold coeff
    calc
      _ = ∫ x,psi b x*(f i (WithLp.toLp 2 x)+g i (WithLp.toLp 2 x)) ∂γpi (Fin d) := by
        apply integral_congr_ae
        filter_upwards [he] with x hx
        simp only [PiLp.add_apply]
        change (f i+g i) (WithLp.toLp 2 x) = f i (WithLp.toLp 2 x)+g i (WithLp.toLp 2 x) at hx
        rw [hx]
      _ = _ := by
        simp_rw [mul_add]
        exact integral_add ((memLp_psi b).integrable_mul hf) ((memLp_psi b).integrable_mul hg)
  map_smul' c f := by
    have hT := NegativeVotingConditionalSecondMoment.gaussian_toLp_measurePreserving d
    have he := hT.quasiMeasurePreserving.ae (Lp.coeFn_smul c (f i))
    unfold coeff
    calc
      _ = ∫ x,psi b x*(c*f i (WithLp.toLp 2 x)) ∂γpi (Fin d) := by
        apply integral_congr_ae
        filter_upwards [he] with x hx
        simp only [PiLp.smul_apply]
        change (c • f i) (WithLp.toLp 2 x) = c*f i (WithLp.toLp 2 x) at hx
        rw [hx]
      _ = _ := by
        simp_rw [mul_left_comm (psi b _) c]
        exact integral_const_mul c _

/-- The actual high-degree Gaussian L² test subspace, not an abstract decay
interface: every original-coordinate Hermite coefficient below k is zero. -/
def highChaosBoundaryTests (d : ℕ) (ι : Type*) [Fintype ι] (k : ℕ) :
    Submodule ℝ (BoundaryL2 d ι) where
  carrier := {f | ∀ i b, degree b<k → boundaryCoefficient i b f=0}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg i b hb; simp [hf i b hb,hg i b hb]
  smul_mem' := by intro c f hf i b hb; simp [hf i b hb]

omit [DecidableEq ι] in
theorem highChaosBoundaryTests_vanish (k : ℕ) (f : highChaosBoundaryTests d ι k)
    (i : ι) (b : Fin d → ℕ) (hb : degree b<k) :
    coeff (fun x : Fin d → ℝ => (f:BoundaryL2 d ι) i (WithLp.toLp 2 x)) b=0 :=
  f.property i b hb

theorem orderedBoundaryPairing_linear {n : ι → ι → ℕ}
    (w : ι → ι → FSC.Coord d) (a : ι → ι → ℝ)
    (F : ∀ i j, Set (tangentSpace (w i j)))
    (e : ∀ i j, i≠j → tangentSpace (w i j) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n i j)))
    (v : ∀ i j, tangentSpace (w i j) → ℝ)
    (hv : ∀ i j, i≠j → MemLp (v i j) 2 ((stdGaussian (tangentSpace (w i j))).restrict (F i j)))
    (hw : ∀ i j, i≠j → ‖w i j‖=1)
    {ρ : ℝ} (hρ : 0<ρ) (hρ1 : ρ<1) (c : ℝ)
    (f g h : ι → FSC.Coord d → ℝ)
    (hfM : ∀ i, Measurable (f i)) (hgM : ∀ i, Measurable (g i)) (hhM : ∀ i, Measurable (h i))
    (hf : ∀ i, MemLp (f i) 2 (stdGaussian (FSC.Coord d)))
    (hg : ∀ i, MemLp (g i) 2 (stdGaussian (FSC.Coord d)))
    (hh : ∀ i, h i =ᵐ[stdGaussian (FSC.Coord d)] fun x => f i x+c*g i x) :
    orderedBoundaryPairing w a F v ρ h = orderedBoundaryPairing w a F v ρ f+
      c*orderedBoundaryPairing w a F v ρ g := by
  unfold orderedBoundaryPairing
  rw [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hij : i≠j := (Finset.mem_erase.mp hj).1.symm
  have hlin := ambientAverage_plane_linear_ae (w i j) (hw i j hij) (e i j hij)
    hρ hρ1 (a i j) c (fun x => f i x-f j x) (fun x => g i x-g j x)
    (fun x => h i x-h j x) ((hfM i).sub (hfM j)) ((hgM i).sub (hgM j))
    ((hhM i).sub (hhM j)) ((hf i).sub (hf j)) ((hg i).sub (hg j))
    (by filter_upwards [hh i,hh j] with x hx hy; rw [hx,hy]; ring)
  have hfi := (hv i j hij).integrable_mul
    ((ambientAverage_plane_memLp_two (w i j) (hw i j hij) (e i j hij) hρ hρ1 (a i j)
      (fun x => f i x-f j x) ((hfM i).sub (hfM j)) ((hf i).sub (hf j))).restrict (F i j))
  have hgi := (hv i j hij).integrable_mul
    ((ambientAverage_plane_memLp_two (w i j) (hw i j hij) (e i j hij) hρ hρ1 (a i j)
      (fun x => g i x-g j x) ((hgM i).sub (hgM j)) ((hg i).sub (hg j))).restrict (F i j))
  change Integrable (fun y => v i j y*ambientAverage ρ (fun x => f i x-f j x)
    ((y:FSC.Coord d)+a i j • w i j)) _ at hfi
  change Integrable (fun y => v i j y*ambientAverage ρ (fun x => g i x-g j x)
    ((y:FSC.Coord d)+a i j • w i j)) _ at hgi
  have he := integral_congr_ae (μ := (stdGaussian (tangentSpace (w i j))).restrict (F i j))
    ((ae_restrict_of_ae hlin).mono (fun y hy => congrArg (fun t : ℝ => v i j y*t) hy))
  rw [he]
  simp_rw [mul_add,mul_left_comm (v i j _) c]
  rw [integral_add hfi (hgi.const_mul c),integral_const_mul]
  ring

/-- The actual surface pairing on Gaussian L² equivalence classes. -/
def boundaryL2LinearMap {n : ι → ι → ℕ}
    (w : ι → ι → FSC.Coord d) (a : ι → ι → ℝ)
    (F : ∀ i j, Set (tangentSpace (w i j)))
    (e : ∀ i j, i≠j → tangentSpace (w i j) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n i j)))
    (v : ∀ i j, tangentSpace (w i j) → ℝ)
    (hv : ∀ i j, i≠j → MemLp (v i j) 2 ((stdGaussian (tangentSpace (w i j))).restrict (F i j)))
    (hw : ∀ i j, i≠j → ‖w i j‖=1)
    {ρ : ℝ} (hρ : 0<ρ) (hρ1 : ρ<1) : BoundaryL2 d ι →ₗ[ℝ] ℝ where
  toFun f := orderedBoundaryPairing w a F v ρ (fun i => f i)
  map_add' f g := by
    have hh := orderedBoundaryPairing_linear w a F e v hv hw hρ hρ1 1
      (fun i => f i) (fun i => g i) (fun i => (f+g) i)
      (fun i => (Lp.stronglyMeasurable (f i)).measurable)
      (fun i => (Lp.stronglyMeasurable (g i)).measurable)
      (fun i => (Lp.stronglyMeasurable ((f+g) i)).measurable)
      (fun i => Lp.memLp (f i)) (fun i => Lp.memLp (g i))
      (fun i => by
        simp only [PiLp.add_apply]
        filter_upwards [Lp.coeFn_add (f i) (g i)] with x hx
        simpa only [Pi.add_apply,one_mul] using hx)
    simpa using hh
  map_smul' c f := by
    have hh := orderedBoundaryPairing_linear w a F e v hv hw hρ hρ1 c
      (fun _ _ => 0) (fun i => f i) (fun i => (c • f) i)
      (fun _ => measurable_const) (fun i => (Lp.stronglyMeasurable (f i)).measurable)
      (fun i => (Lp.stronglyMeasurable ((c • f) i)).measurable)
      (fun _ => MemLp.zero) (fun i => Lp.memLp (f i))
      (fun i => by
        simp only [PiLp.smul_apply]
        filter_upwards [Lp.coeFn_smul c (f i)] with x hx
        simpa only [Pi.smul_apply,smul_eq_mul,zero_add] using hx)
    simpa [orderedBoundaryPairing,ambientAverage,smul_eq_mul] using hh

end L2Functional

section HilbertExtension
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A bounded functional on any linear test subspace has an ambient Hilbert
representative with the same squared bound. No closed-subspace premise is needed. -/
theorem exists_representative_of_sq_bound (S : Submodule ℝ H) (l : S →ₗ[ℝ] ℝ)
    (B : ℝ) (hB : 0≤B) (hb : ∀ f:S,(l f)^2 ≤ B*‖f‖^2) :
    ∃ V:H, ‖V‖^2≤B ∧ ∀ f:S,inner ℝ V (f:H)=l f := by
  have hb' : ∀ f:S,‖l f‖ ≤ Real.sqrt B*‖f‖ := by
    intro f
    rw [Real.norm_eq_abs]
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [sq_abs,mul_pow,Real.sq_sqrt hB]
    exact hb f
  let lc := l.mkContinuous (Real.sqrt B) hb'
  obtain ⟨L,hL,hn⟩ := exists_extension_norm_eq S lc
  refine ⟨(InnerProductSpace.toDual ℝ H).symm L,?_,?_⟩
  · have hnorm : ‖L‖≤Real.sqrt B := hn.trans_le (l.mkContinuous_norm_le (Real.sqrt_nonneg B) hb')
    rw [(InnerProductSpace.toDual ℝ H).symm.norm_map]
    have hh := sq_le_sq₀ (norm_nonneg L) (Real.sqrt_nonneg B)
    exact (hh.mpr hnorm).trans_eq (Real.sq_sqrt hB)
  · intro f
    rw [InnerProductSpace.toDual_symm_apply,hL f]
    rfl

end HilbertExtension

section ActualRiesz
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The literal smoothed boundary pairing has an ambient Gaussian L²
representative on every high-degree linear test subspace. Its norm bound is
derived from the actual facet trace and speed energy, not assumed as a premise.
The representative is not asserted to be the derivative of moving cell masses;
that identification and path integration are separate obligations. -/
theorem exists_actual_boundary_representative {n : ι → ι → ℕ}
    (w : ι → ι → FSC.Coord d) (a ell : ι → ι → ℝ)
    (F : ∀ i j, Set (tangentSpace (w i j)))
    (e : ∀ i j, i≠j → tangentSpace (w i j) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n i j)))
    (v : ∀ i j, tangentSpace (w i j) → ℝ)
    (hv : ∀ i j, i≠j → MemLp (v i j) 2 ((stdGaussian (tangentSpace (w i j))).restrict (F i j)))
    (τ σ q ell0 G : ℝ) (hτ : 0 < τ) (hσ : 0 < σ) (hσ1 : σ < 1)
    (hq : 2 ≤ q) (ht : τ^2=1/(2*q-1)) (hell0 : 0 < ell0) (hG : 0 ≤ G)
    (hw : ∀ i j, i≠j → ‖w i j‖=1)
    (hF : ∀ i j, i≠j → MeasurableSet (F i j))
    (hell : ∀ i j, i≠j → ell0 ≤ ell i j)
    (hμsym : ∀ i j, planeSurfaceMass w a F i j=planeSurfaceMass w a F j i)
    (hellsym : ∀ i j, ell i j=ell j i)
    (hdegree : ∀ i, (∑ j ∈ Finset.univ.erase i, planeSurfaceMass w a F i j/ell i j) ≤ G)
    (k : ℕ) (S : Submodule ℝ (BoundaryL2 d ι))
    (hvanish : ∀ f:S, ∀ i b, degree b<k →
      coeff (fun x : Fin d → ℝ => (f:BoundaryL2 d ι) i (WithLp.toLp 2 x)) b=0) :
    ∃ V : BoundaryL2 d ι,
      ‖V‖^2 ≤ 8*traceCoefficient (ι := ι) ell0 G q*(σ^2)^k*orderedSpeedEnergy w a ell F v ∧
      ∀ f:S, (∑ i, ∫ x,V i x*(f:BoundaryL2 d ι) i x ∂stdGaussian (FSC.Coord d)) =
        orderedBoundaryPairing w a F v (τ*σ) (fun i => (f:BoundaryL2 d ι) i) := by
  have hτsq : τ^2<1 := by
    rw [ht]
    apply (div_lt_one (by linarith : 0<2*q-1)).mpr
    linarith
  have hτ1 : τ<1 := by nlinarith
  have hp : 0<τ*σ := mul_pos hτ hσ
  have hp1 : τ*σ<1 := (mul_lt_mul_of_pos_left hσ1 hτ).trans (by simpa using hτ1)
  let l := (boundaryL2LinearMap w a F e v hv hw hp hp1).comp S.subtype
  let B := 8*traceCoefficient (ι := ι) ell0 G q*(σ^2)^k*orderedSpeedEnergy w a ell F v
  have hN : 0≤orderedSpeedEnergy w a ell F v := by
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    have hij := (Finset.mem_erase.mp hj).1.symm
    exact mul_nonneg
      (mul_nonneg (gaussianPDFReal_nonneg _ _ _) (hell0.le.trans (hell i j hij)))
      (integral_nonneg (fun _ => sq_nonneg _))
  have hB : 0≤B := by
    unfold B traceCoefficient
    positivity
  have hb : ∀ f:S,(l f)^2 ≤ B*‖f‖^2 := by
    intro f
    have hh := orderedBoundaryPairing_sq_le w a ell F e v hv τ σ q ell0 G
      hτ hσ hσ1 hq ht hell0 hG hw hF hell hμsym hellsym hdegree
      (fun i => (f:BoundaryL2 d ι) i)
      (fun i => (Lp.stronglyMeasurable ((f:BoundaryL2 d ι) i)).measurable)
      (fun i => Lp.memLp ((f:BoundaryL2 d ι) i)) k (hvanish f)
    change _ ≤ B*‖(f:BoundaryL2 d ι)‖^2
    rw [boundaryL2_norm_sq]
    exact hh
  obtain ⟨V,hV,hrep⟩ := exists_representative_of_sq_bound S l B hB hb
  refine ⟨V,hV,?_⟩
  intro f
  have hh := hrep f
  rw [PiLp.inner_apply] at hh
  simpa only [MeasureTheory.L2.inner_def,Real.inner_apply,l,LinearMap.comp_apply,
    Submodule.subtype_apply,boundaryL2LinearMap,LinearMap.coe_mk,AddHom.coe_mk] using hh

/-- Specialization to the actual original-coordinate high-Hermite subspace;
callers supply neither an abstract test carrier nor a functional norm premise. -/
theorem exists_actual_highChaos_boundary_representative {n : ι → ι → ℕ}
    (w : ι → ι → FSC.Coord d) (a ell : ι → ι → ℝ)
    (F : ∀ i j, Set (tangentSpace (w i j)))
    (e : ∀ i j, i≠j → tangentSpace (w i j) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n i j)))
    (v : ∀ i j, tangentSpace (w i j) → ℝ)
    (hv : ∀ i j, i≠j → MemLp (v i j) 2 ((stdGaussian (tangentSpace (w i j))).restrict (F i j)))
    (τ σ q ell0 G : ℝ) (hτ : 0 < τ) (hσ : 0 < σ) (hσ1 : σ < 1)
    (hq : 2 ≤ q) (ht : τ^2=1/(2*q-1)) (hell0 : 0 < ell0) (hG : 0 ≤ G)
    (hw : ∀ i j, i≠j → ‖w i j‖=1)
    (hF : ∀ i j, i≠j → MeasurableSet (F i j))
    (hell : ∀ i j, i≠j → ell0 ≤ ell i j)
    (hμsym : ∀ i j, planeSurfaceMass w a F i j=planeSurfaceMass w a F j i)
    (hellsym : ∀ i j, ell i j=ell j i)
    (hdegree : ∀ i, (∑ j ∈ Finset.univ.erase i, planeSurfaceMass w a F i j/ell i j) ≤ G)
    (k : ℕ) :
    ∃ V : BoundaryL2 d ι,
      ‖V‖^2 ≤ 8*traceCoefficient (ι := ι) ell0 G q*(σ^2)^k*orderedSpeedEnergy w a ell F v ∧
      ∀ f:highChaosBoundaryTests d ι k,
        (∑ i, ∫ x,V i x*(f:BoundaryL2 d ι) i x ∂stdGaussian (FSC.Coord d)) =
          orderedBoundaryPairing w a F v (τ*σ) (fun i => (f:BoundaryL2 d ι) i) :=
  exists_actual_boundary_representative w a ell F e v hv τ σ q ell0 G hτ hσ hσ1 hq ht
    hell0 hG hw hF hell hμsym hellsym hdegree k (highChaosBoundaryTests d ι k)
      (highChaosBoundaryTests_vanish k)

end ActualRiesz
end NegativeVotingBoundaryFunctionalRiesz
