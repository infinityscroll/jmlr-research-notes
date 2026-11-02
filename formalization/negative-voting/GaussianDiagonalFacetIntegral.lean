import GaussianDiagonalWinnerIntegral
import GaussianRegularFacetMean
import GaussianMovingCap
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Exact physical facet-weight integrals for independent diagonal Gaussian
scores. The normalization is obtained by differentiating the actual winner
mass and comparing its geometric mass Jacobian. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin Set Filter WeakSimplex
open scoped BigOperators RealInnerProductSpace ENNReal Classical Topology
namespace NegativeVotingDiagonalFacetIntegral
open NegativeVotingDiagonalHazardDifferentiation NegativeVotingDiagonalWinnerIntegral
  NegativeVotingFan NegativeVotingCapTail NegativeVotingFanJacobian
variable {n m : ℕ}

/-- Positive independent variances give the required centered singular bound;
no affine-basis or noncoincidence premise is imported. -/
theorem diagonal_singular_lower (σ : Fin m→ℝ) (b : ℝ) (hb : 0≤b) (hσ : ∀i,b≤σ i) :
    CenteredSingularLowerBound (diagonalRows σ) b := by
  intro q hq
  have he : (∑i,q i • diagonalRows σ i)=WithLp.toLp 2 (fun i=>q i*σ i):=by
    ext j
    simp [diagonalRows,Pi.single_apply,Pi.single,Function.update,eq_comm]
  rw [he,EuclideanSpace.real_norm_sq_eq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hs : b^2≤(σ i)^2:=sq_le_sq₀ hb (hb.trans (hσ i)) |>.mpr (hσ i)
  simpa only [mul_pow,mul_comm] using mul_le_mul_of_nonneg_right hs (sq_nonneg (q i))

theorem exists_diagonal_singular_lower [Nonempty (Fin m)] (σ : Fin m→ℝ) (hσ : ∀i,0<σ i) :
    ∃b,0<b ∧ CenteredSingularLowerBound (diagonalRows σ) b := by
  obtain ⟨i,hi,hmin⟩:=Finset.exists_min_image Finset.univ σ Finset.univ_nonempty
  exact ⟨σ i,hσ i,diagonal_singular_lower σ (σ i) (hσ i).le (fun j=>hmin j (Finset.mem_univ j))⟩

@[fun_prop] theorem gaussianCDF_continuous (σ h : ℝ) : Continuous (gaussianCDF σ h) := by
  unfold gaussianCDF
  exact NegativeVotingMassCentroid.continuous_normalCDF.comp (by fun_prop)

@[fun_prop] theorem gaussianDensity_continuous (σ h : ℝ) : Continuous (gaussianDensity σ h) := by
  unfold gaussianDensity normalPDF gaussianPDFReal
  fun_prop

theorem gaussianCDF_bounds (σ h x : ℝ) : 0≤gaussianCDF σ h x ∧ gaussianCDF σ h x≤1 :=
  ⟨(gaussianCDF_pos _ _ _).le,(normalCDF_lt_one _).le⟩

theorem gaussianDensity_le_inv (σ h x : ℝ) (hσ : 0<σ) :
    gaussianDensity σ h x≤σ⁻¹ := by
  unfold gaussianDensity
  calc
    _≤1/σ:=div_le_div_of_nonneg_right
      ((NegativeVotingMovingCap.normalPDF_le_zero _).trans NegativeVotingRegularFacetMean.normalPDF_zero_le_one) hσ.le
    _=σ⁻¹:=one_div _

def otherProduct (σ h : Fin m→ℝ) (i j : Fin m) (x : ℝ) : ℝ :=
  ∏k∈(Finset.univ.erase i).erase j,gaussianCDF (σ k) (h k) x

theorem otherProduct_bounds (σ h : Fin m→ℝ) (i j : Fin m) (x : ℝ) :
    0≤otherProduct σ h i j x ∧ otherProduct σ h i j x≤1 := by
  exact ⟨Finset.prod_nonneg (fun k hk=>(gaussianCDF_bounds _ _ _).1),
    Finset.prod_le_one₀ (fun k hk=>(gaussianCDF_bounds _ _ _).1) (fun k hk=>(gaussianCDF_bounds _ _ _).2)⟩

@[fun_prop] theorem otherProduct_continuous (σ h : Fin m→ℝ) (i j : Fin m) :
    Continuous (otherProduct σ h i j) := by
  unfold otherProduct
  fun_prop

def offsetLine (h : Fin m→ℝ) (j : Fin m) (t : ℝ) : Fin m→ℝ :=
  h+t • Pi.single j 1

@[simp] theorem offsetLine_self (h : Fin m→ℝ) (j : Fin m) (t : ℝ) :
    offsetLine h j t j=h j+t := by simp [offsetLine]
@[simp] theorem offsetLine_other (h : Fin m→ℝ) (j k : Fin m) (t : ℝ) (hkj : k≠j) :
    offsetLine h j t k=h k := by simp [offsetLine,Pi.single_apply,hkj]
@[simp] theorem offsetLine_zero (h : Fin m→ℝ) (j : Fin m) : offsetLine h j 0=h := by
  simp [offsetLine]

def competitorKernel (σ h : Fin m→ℝ) (i j : Fin m) (t y : ℝ) : ℝ :=
  gaussianCDF (σ j) (h j+t) (σ i*y+h i)*otherProduct σ h i j (σ i*y+h i)
def competitorDerivative (σ h : Fin m→ℝ) (i j : Fin m) (t y : ℝ) : ℝ :=
  -gaussianDensity (σ j) (h j+t) (σ i*y+h i)*otherProduct σ h i j (σ i*y+h i)

@[fun_prop] theorem competitorKernel_continuous (σ h : Fin m→ℝ) (i j : Fin m) (t : ℝ) :
    Continuous (competitorKernel σ h i j t) := by unfold competitorKernel;fun_prop
@[fun_prop] theorem competitorDerivative_continuous (σ h : Fin m→ℝ) (i j : Fin m) (t : ℝ) :
    Continuous (competitorDerivative σ h i j t) := by unfold competitorDerivative;fun_prop

theorem competitorKernel_abs_le (σ h : Fin m→ℝ) (i j : Fin m) (t y : ℝ) :
    |competitorKernel σ h i j t y|≤1 := by
  have hh:=gaussianCDF_bounds (σ j) (h j+t) (σ i*y+h i)
  have ho:=otherProduct_bounds σ h i j (σ i*y+h i)
  rw [competitorKernel,abs_of_nonneg (mul_nonneg hh.1 ho.1)]
  exact mul_le_one₀ hh.2 ho.1 ho.2

theorem competitorDerivative_abs_le (σ h : Fin m→ℝ) (hσ : ∀k,0<σ k)
    (i j : Fin m) (t y : ℝ) : |competitorDerivative σ h i j t y|≤(σ j)⁻¹ := by
  have hd:0≤gaussianDensity (σ j) (h j+t) (σ i*y+h i):=(gaussianDensity_pos _ _ _ (hσ j)).le
  have ho:=otherProduct_bounds σ h i j (σ i*y+h i)
  rw [competitorDerivative,abs_mul,abs_neg,abs_of_nonneg hd,abs_of_nonneg ho.1]
  exact (mul_le_of_le_one_right hd ho.2).trans (gaussianDensity_le_inv _ _ _ (hσ j))

theorem competitorKernel_hasDerivAt (σ h : Fin m→ℝ) (hσ : ∀k,0<σ k)
    (i j : Fin m) (y t : ℝ) :
    HasDerivAt (fun s=>competitorKernel σ h i j s y) (competitorDerivative σ h i j t y) t := by
  have hh:=gaussianCDF_hasDerivAt (fun _ : ℝ=>σ j) (fun s=>h j+s) t 0 1 (σ i*y+h i)
    (hasDerivAt_const _ _) (by simpa using (hasDerivAt_id t).const_add (h j)) (hσ j)
  have hd:=hh.mul_const (otherProduct σ h i j (σ i*y+h i))
  simpa [competitorKernel,competitorDerivative,transportSpeed] using hd

theorem competitorIntegral_hasDerivAt (σ h : Fin m→ℝ) (hσ : ∀k,0<σ k)
    (i j : Fin m) :
    HasDerivAt (fun t=>∫y,competitorKernel σ h i j t y ∂gaussianReal 0 1)
      (∫y,competitorDerivative σ h i j 0 y ∂gaussianReal 0 1) 0 := by
  have hint : Integrable (competitorKernel σ h i j 0) (gaussianReal 0 1):=
    Integrable.mono' (integrable_const 1) (by fun_prop)
      (ae_of_all _ (fun y=>by simpa only [Real.norm_eq_abs] using competitorKernel_abs_le σ h i j 0 y))
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s:=Set.univ) (bound:=fun _ : ℝ=>(σ j)⁻¹)
    (F:=competitorKernel σ h i j) (F':=competitorDerivative σ h i j)
    (Filter.univ_mem) (by filter_upwards with t;fun_prop) hint (by fun_prop)
    (ae_of_all _ (fun y t ht=>by simpa only [Real.norm_eq_abs] using competitorDerivative_abs_le σ h hσ i j t y))
    (integrable_const _) (ae_of_all _ (fun y t ht=>competitorKernel_hasDerivAt σ h hσ i j y t))).2

theorem eraseProduct_offsetLine (σ h : Fin m→ℝ) (i j : Fin m) (hij : i≠j) (t x : ℝ) :
    (∏k∈Finset.univ.erase i,gaussianCDF (σ k) (offsetLine h j t k) x)=
      gaussianCDF (σ j) (h j+t) x*otherProduct σ h i j x := by
  rw [←Finset.mul_prod_erase (a:=j) (Finset.univ.erase i)
    (fun k=>gaussianCDF (σ k) (offsetLine h j t k) x) (by simp [hij,Ne.symm hij])]
  rw [offsetLine_self]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [offsetLine_other h j k t (Finset.mem_erase.mp hk).1]

theorem mass_offsetLine_eq_competitorIntegral (σ h : Fin (n+1)→ℝ) (hσ : ∀k,0<σ k)
    (i j : Fin (n+1)) (hij : i≠j) (t : ℝ) :
    mass (diagonalRows σ) (offsetLine h j t) i=
      ∫y,competitorKernel σ h i j t y ∂gaussianReal 0 1 := by
  rw [mass_diagonal_eq_winner_integral σ _ hσ i,winner_integral_conditioned σ _ hσ i]
  apply integral_congr_ae
  filter_upwards with y
  rw [offsetLine_other h j i t hij,
    remainingProduct_eq_erase _ (fun k=>(gaussianCDF_pos _ _ _).ne') i,
    eraseProduct_offsetLine σ h i j hij t]
  rfl

theorem geometric_competitor_hasDerivAt (σ h : Fin (n+1)→ℝ) (hσ : ∀k,0<σ k)
    (i j : Fin (n+1)) (hij : i≠j) :
    HasDerivAt (fun t=>mass (diagonalRows σ) (offsetLine h j t) i)
      (-facetWeight (diagonalRows σ) h i j) 0 := by
  obtain ⟨b,hb,hlower⟩:=exists_diagonal_singular_lower σ hσ
  have hline : HasDerivAt (offsetLine h j) (Pi.single j 1) 0:=by
    apply hasDerivAt_pi.mpr
    intro k
    simpa only [offsetLine,Pi.smul_apply,Pi.add_apply,smul_eq_mul,one_mul,id_eq] using
      ((hasDerivAt_id (0:ℝ)).mul_const ((Pi.single j (1:ℝ): Fin (n+1)→ℝ) k)).const_add (h k)
  have hD : HasFDerivAt (fun h'=>mass (diagonalRows σ) h' i) (massDerivative (diagonalRows σ) h i) (offsetLine h j 0):=by
    rw [offsetLine_zero]
    exact hasFDerivAt_mass (diagonalRows σ) b hb hlower h i
  have hd:=hD.comp_hasDerivAt 0 hline
  have hv : massDerivative (diagonalRows σ) h i (Pi.single j 1)= -facetWeight (diagonalRows σ) h i j:=by
    rw [massDerivative_apply (diagonalRows σ) b hb hlower]
    simp [Pi.single_apply,Pi.single,Function.update,hij,Ne.symm hij]
  simpa only [offsetLine_zero,hv,Function.comp_def] using hd

theorem hazardPairDensity_eq_product (σ h : Fin m→ℝ) (i j : Fin m) (hij : i≠j) (x : ℝ) :
    hazardPairDensity σ h x i j=
      gaussianDensity (σ i) (h i) x*gaussianDensity (σ j) (h j) x*otherProduct σ h i j x := by
  have he : productCDF σ h x=gaussianCDF (σ i) (h i) x*
      (gaussianCDF (σ j) (h j) x*otherProduct σ h i j x):=by
    unfold productCDF otherProduct
    rw [←Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
      ←Finset.mul_prod_erase (a:=j) (Finset.univ.erase i) _ (by simp [hij,Ne.symm hij])]
  unfold hazardPairDensity gaussianHazard
  rw [he]
  field_simp [(gaussianCDF_pos (σ i) (h i) x).ne',(gaussianCDF_pos (σ j) (h j) x).ne']

/-- Exact physical facet weight, with the normalization inherited from the
actual geometric mass derivative. This is not an assumed coarea formula. -/
theorem facetWeight_diagonal_integral (σ h : Fin (n+1)→ℝ) (hσ : ∀k,0<σ k)
    (i j : Fin (n+1)) (hij : i≠j) :
    facetWeight (diagonalRows σ) h i j=∫x,hazardPairDensity σ h x i j := by
  have hg:=geometric_competitor_hasDerivAt σ h hσ i j hij
  have ha:=competitorIntegral_hasDerivAt σ h hσ i j
  have he : (fun t=>mass (diagonalRows σ) (offsetLine h j t) i)=
      fun t=>∫y,competitorKernel σ h i j t y ∂gaussianReal 0 1:=by
    funext t
    exact mass_offsetLine_eq_competitorIntegral σ h hσ i j hij t
  rw [he] at hg
  have hd:=hg.unique ha
  have hi : (∫y,competitorDerivative σ h i j 0 y ∂gaussianReal 0 1)=
      -(∫x,hazardPairDensity σ h x i j):=by
    simp only [competitorDerivative,add_zero,neg_mul,integral_neg]
    congr 1
    rw [gaussian_affine_integral (σ i) (h i) (hσ i)
      (fun x=>gaussianDensity (σ j) (h j) x*otherProduct σ h i j x)]
    apply integral_congr_ae
    filter_upwards with x
    rw [hazardPairDensity_eq_product σ h i j hij x]
    ring
  rw [hi] at hd
  exact neg_injective hd

theorem singular_lower_common_row_sub {d : ℕ} {V : Type*} [Fintype V]
    (B : V→FSC.Coord d) (b : ℝ) (hlower : CenteredSingularLowerBound B b) (v : FSC.Coord d) :
    CenteredSingularLowerBound (fun i=>B i-v) b := by
  intro q hq
  have he : (∑i,q i • (B i-v))=∑i,q i • B i:=by
    simp only [smul_sub,Finset.sum_sub_distrib,←Finset.sum_smul,hq,zero_smul,sub_zero]
  rw [he]
  exact hlower q hq

/-- Equality of actual mass functions forces equality of physical off-diagonal
facet weights, because both are entries of the actual offset derivative. -/
theorem facetWeight_eq_of_mass_eq {d e : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : V→FSC.Coord d) (C : V→FSC.Coord e) (b c : ℝ) (hb : 0<b) (hc : 0<c)
    (hB : CenteredSingularLowerBound B b) (hC : CenteredSingularLowerBound C c)
    (hmass : ∀h,mass B h=mass C h) (h : V→ℝ) (i j : V) (hij : i≠j) :
    facetWeight B h i j=facetWeight C h i j := by
  have he : (fun h'=>mass B h' i)=fun h'=>mass C h' i:=by
    funext h'
    exact congrFun (hmass h') i
  have hdB:=hasFDerivAt_mass B b hb hB h i
  rw [he] at hdB
  have heD:=hdB.unique (hasFDerivAt_mass C c hc hC h i)
  have hev:=congrArg (fun L:(V→ℝ)→L[ℝ]ℝ=>L (Pi.single j 1)) heD
  rw [massDerivative_apply B b hb hB,massDerivative_apply C c hc hC] at hev
  simpa [Pi.single,Function.update,hij] using hev

theorem facetWeight_common_row_sub {d : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : V→FSC.Coord d) (b : ℝ) (hb : 0<b) (hB : CenteredSingularLowerBound B b)
    (h : V→ℝ) (v : FSC.Coord d) (i j : V) (hij : i≠j) :
    facetWeight (fun k=>B k-v) h i j=facetWeight B h i j := by
  have hinj : Function.Injective B:=fun i j he=>by
    by_contra hij
    exact NegativeVotingFacetDegree.centered_singular_rows_ne B b hb hB i j hij he
  exact facetWeight_eq_of_mass_eq (fun k=>B k-v) B b b hb hb
    (singular_lower_common_row_sub B b hB v) hB
    (fun h'=>funext (fun k=>mass_common_row_sub B hinj h' v k)) h i j hij

/-- The same exact one-dimensional physical-weight formula applies after
centering the diagonal scores by any common row vector. -/
theorem facetWeight_centered_diagonal_integral (σ h : Fin (n+1)→ℝ) (hσ : ∀k,0<σ k)
    (v : FSC.Coord (n+1)) (i j : Fin (n+1)) (hij : i≠j) :
    facetWeight (fun k=>diagonalRows σ k-v) h i j=∫x,hazardPairDensity σ h x i j := by
  obtain ⟨b,hb,hB⟩:=exists_diagonal_singular_lower σ hσ
  rw [facetWeight_common_row_sub (diagonalRows σ) b hb hB h v i j hij,
    facetWeight_diagonal_integral σ h hσ i j hij]

end NegativeVotingDiagonalFacetIntegral
