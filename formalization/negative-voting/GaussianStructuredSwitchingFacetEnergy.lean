import GaussianStructuredSwitchingFacet
import GaussianTensorFacetAggregation

/-! The literal weighted forcing is aggregated on actual affine facets using
row degree, never an unweighted count of all labels. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace ENNReal Classical
namespace NegativeVotingStructuredSwitchingFacetEnergy
open NegativeVotingStructuredSwitchingFacet NegativeVotingStructuredSwitchingMoments
  NegativeVotingFan NegativeVotingDisintegration NegativeVotingWeightedFacet NegativeVotingFanJacobian
  NegativeVotingNormalTrace NegativeVotingSmoothErrorMoment NegativeVotingPolynomialFacetGeometricTrace

variable {d n : ℕ}

theorem normalRowSquare_le_scaled (τ a b L : ℝ) (hb : 0 ≤ b)
    (hτ2 : τ^2 ≤ 1/2) (hrel : τ^2*L ≤ 1/8192) (ha : a^2 ≤ b*L) :
    normalRowSquare τ a ≤ 2*Real.exp b := by
  have hsm : (1/2:ℝ) ≤ Real.sqrt (1-τ^2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hsp : (1:ℝ) ≤ Real.sqrt (1+τ^2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg τ]
  have him : (Real.sqrt (1-τ^2))⁻¹ ≤ 2 := by
    simpa using inv_anti₀ (by norm_num : (0:ℝ)<1/2) hsm
  have hip : (Real.sqrt (1+τ^2))⁻¹ ≤ 1 := by
    simpa using inv_anti₀ zero_lt_one hsp
  have he : τ^2*a^2/(1+τ^2) ≤ b := by
    apply (div_le_iff₀ (show 0<1+τ^2 by positivity)).mpr
    have hh:=mul_le_mul_of_nonneg_left ha (sq_nonneg τ)
    have hg:=mul_le_mul_of_nonneg_left hrel hb
    nlinarith [mul_nonneg hb (sq_nonneg τ)]
  unfold normalRowSquare
  have hi : (Real.sqrt (1-τ^2))⁻¹*(Real.sqrt (1+τ^2))⁻¹ ≤ 2 := by
    simpa using mul_le_mul him hip (by positivity) (by norm_num)
  exact mul_le_mul hi (Real.exp_le_exp.mpr he) (Real.exp_pos _).le (by norm_num)

def forcingLabelMajorant (A b r τ : ℝ) (D : Fin (n+2)→FSC.Coord d)
    (h : Fin (n+2)→ℝ) (fD fu : Fin (n+2)→FSC.Coord d→ℝ) (i : Fin (n+2)) : ℝ :=
  planeDampingCoefficient b*(r*planeErrorCoefficient A b n*τ⁻¹*
    ((1+Real.sqrt (b*logScale n))*‖D i‖+|h i|)+Real.sqrt (2*Real.exp b)*
    (realLp (stdGaussian (FSC.Coord d)) 2 (fD i)+realLp (stdGaussian (FSC.Coord d)) 2 (fu i))/r)

/-- Full actual weighted-facet square bound. The assumptions concern concrete
geometry and source L2 functions; all common-factor and OU traces are derived. -/
theorem exists_dimension_uniform_weightedForcing_facet_energy_le
    (A K : ℝ) (hA : 8192 ≤ A) (hK : 0 ≤ K) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d : ℕ,
      ∀ (B R D : Fin (n+2)→FSC.Coord d) (h : Fin (n+2)→ℝ),
      Function.Injective B → (∀i,‖R i‖ ≤ 1) →
      ∀ r η τ b G : ℝ, 0<r → r ≤ 1/((n:ℝ)+1) → 0 ≤ η →
        η ≤ K*r^2*logScale n → 0 ≤ b → 0 ≤ G →
        0<τ → τ<1 → 4*(A*logScale n) ≤ 1+(τ^2)⁻¹ →
      (∀i j,i≠j→((n:ℝ)+2)^(-4096:ℝ) ≤
        (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal) →
      (∀i j,i≠j→(pairOffset B h i j)^2 ≤ b*logScale n) →
      (∀i,(∑j∈Finset.univ.erase i,facetWeight B h i j) ≤ G) →
      ∀ (fD fu : Fin (n+2)→FSC.Coord d→ℝ),
      (∀i,Measurable (fD i)) → (∀i,Measurable (fu i)) →
      (∀i,MemLp (fD i) 2 (stdGaussian (FSC.Coord d))) →
      (∀i,MemLp (fu i) 2 (stdGaussian (FSC.Coord d))) →
      affineWeightedFacetEnergy B h (fun i x=>weightedForcing R D h η r τ fD fu x i) ≤
        G*Real.exp 1*∑i,(forcingLabelMajorant A b r τ D h fD fu i)^2 := by
  obtain ⟨N,hN⟩:=exists_dimension_uniform_weightedForcing_plane_norm_le A K (by linarith) hK
  refine ⟨N,?_⟩
  intro n hn d B R D h hinj hR r η τ b G hr hrange hη hηupper hb hG hτ hτ1 hqτ hp ha hdegree
    fD fu hfDM hfuM hfD hfu
  let q:=A*logScale n
  let C:=fun i=>forcingLabelMajorant A b r τ D h fD fu i
  have hL : 1 ≤ logScale n:=logScale_one_le n
  have hq : 2 ≤ q:=by dsimp [q]; nlinarith
  have hq0 : 0<q:=by linarith
  have hτsq : 0<τ^2:=sq_pos_of_pos hτ
  have hscale : 8192*logScale n ≤ q:=by dsimp [q]; nlinarith
  have hrel : τ^2*logScale n ≤ 1/8192 := by
    have hm:=mul_le_mul_of_nonneg_right hqτ hτsq.le
    have he : (1+(τ^2)⁻¹)*τ^2=τ^2+1:=by field_simp
    rw [he] at hm
    have hα : 8192*logScale n ≤ 4*A*logScale n-1:=by nlinarith
    have hz:=mul_le_mul_of_nonneg_right hα hτsq.le
    nlinarith
  have hτ2 : τ^2 ≤ 1/2:=by
    have hh:=mul_le_mul_of_nonneg_left hL hτsq.le
    nlinarith
  have hκ0 : 0 ≤ planeDampingCoefficient b:=by unfold planeDampingCoefficient; positivity
  have hε0 : 0 ≤ planeErrorCoefficient A b n:=by
    have hc:=momentConstant_nonneg (4*A) (by linarith)
    have hl : 0 ≤ logScale n:=by linarith
    unfold planeErrorCoefficient
    positivity
  have hC0 i : 0 ≤ C i:=by
    dsimp [C,forcingLabelMajorant]
    exact mul_nonneg hκ0 (add_nonneg (mul_nonneg
      (mul_nonneg (mul_nonneg hr.le hε0) (inv_nonneg.mpr hτ.le)) (by positivity))
      (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (realLp_nonneg _ _) (realLp_nonneg _ _))) hr.le))
  have htrace i j (hij:i≠j) :
      (∫y in intrinsicFacet B h i j,
        (weightedForcing R D h η r τ fD fu (facetChart B h i j y) i)^2
          ∂stdGaussian (tangentSpace (pairNormal B i j))) ≤
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal*
        Real.exp 1*(C i)^2 := by
    let w:=pairNormal B i j
    let a:=pairOffset B h i j
    let e:=canonicalTangentCoordinates w
    have hw : ‖w‖=1:=pairNormal_norm B i j (fun he=>hij (hinj he))
    obtain ⟨hmem,hbound⟩:=hN n hn d _ R D h hR w e hw r η τ a b hr hrange hη hηupper hb
      (ha i j hij) hτ hτ1 hqτ fD fu hfDM hfuM hfD hfu i
    have habs : |a| ≤ Real.sqrt (b*logScale n):=by
      apply Real.le_sqrt_of_sq_le
      simpa only [sq_abs] using ha i j hij
    have hgap : ‖D i‖+|a*inner ℝ (D i) w+h i| ≤
        (1+Real.sqrt (b*logScale n))*‖D i‖+|h i|:=by
      have hi : |inner ℝ (D i) w| ≤ ‖D i‖:=by simpa only [hw,mul_one] using abs_real_inner_le_norm (D i) w
      have hh:=mul_le_mul habs hi (abs_nonneg _) (Real.sqrt_nonneg _)
      have had:=abs_add_le (a*inner ℝ (D i) w) (h i)
      rw [abs_mul] at had
      nlinarith only [hh,had]
    have hrow : Real.sqrt (normalRowSquare τ a) ≤ Real.sqrt (2*Real.exp b):=
      Real.sqrt_le_sqrt (normalRowSquare_le_scaled τ a b (logScale n) hb hτ2 hrel (ha i j hij))
    have hbnd : realLp (stdGaussian (tangentSpace w)) (ENNReal.ofReal q)
        (fun y:tangentSpace w=>weightedForcing R D h η r τ fD fu ((y:FSC.Coord d)+a • w) i) ≤ C i:=by
      refine hbound.trans ?_
      apply mul_le_mul_of_nonneg_left _ hκ0
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hgap (mul_nonneg (mul_nonneg hr.le hε0) (inv_nonneg.mpr hτ.le))
      · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hrow
          (add_nonneg (realLp_nonneg _ _) (realLp_nonneg _ _))) hr.le
    have hrestr:=restricted_square_le_of_realLp (stdGaussian (tangentSpace w)) (intrinsicFacet B h i j)
      q (C i) hq _ hmem hbnd
    have hm : 0<(n:ℝ)+2:=by positivity
    have hpp : 0<(stdGaussian (tangentSpace w) (intrinsicFacet B h i j)).toReal:=
      (Real.rpow_pos_of_pos hm _).trans_le (hp i j hij)
    have hlog : -Real.log ((stdGaussian (tangentSpace w) (intrinsicFacet B h i j)).toReal) ≤
        4096*logScale n:=by
      have hh:=Real.log_le_log (Real.rpow_pos_of_pos hm _) (hp i j hij)
      rw [Real.log_rpow hm] at hh
      dsimp [logScale]
      linarith
    have hgain:=probability_rpow_gain hpp hq0 hlog hscale
    refine hrestr.trans ((mul_le_mul_of_nonneg_left hgain (sq_nonneg (C i))).trans_eq ?_)
    ring
  change (∑i,∑j∈Finset.univ.erase i,
    gaussianPDFReal 0 1 (pairOffset B h i j)/‖B i-B j‖*
      ∫y in intrinsicFacet B h i j,(weightedForcing R D h η r τ fD fu (facetChart B h i j y) i)^2
        ∂stdGaussian (tangentSpace (pairNormal B i j))) ≤ _
  calc
    _ ≤ ∑i,∑j∈Finset.univ.erase i,facetWeight B h i j*Real.exp 1*(C i)^2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j hj
      have hij : i≠j:=(Finset.mem_erase.mp hj).1.symm
      have hh:=mul_le_mul_of_nonneg_left (htrace i j hij)
        (div_nonneg (gaussianPDFReal_nonneg 0 1 (pairOffset B h i j)) (norm_nonneg (B i-B j)))
      convert hh using 1 <;> dsimp [facetWeight] <;> ring
    _ = ∑i,(∑j∈Finset.univ.erase i,facetWeight B h i j)*Real.exp 1*(C i)^2:=by
      simp only [Finset.sum_mul]
    _ ≤ ∑i,G*Real.exp 1*(C i)^2:=by
      exact Finset.sum_le_sum fun i _=>mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hdegree i) (Real.exp_pos _).le) (sq_nonneg _)
    _ = _:=by simp only [C,Finset.mul_sum]


private theorem four_term_square (K a b x y z w : ℝ) :
    (K*(a*(x+y)+b*(z+w)))^2 ≤ 4*K^2*(a^2*(x^2+y^2)+b^2*(z^2+w^2)) := by
  have h1:=add_sq_le (a:=a*(x+y)) (b:=b*(z+w))
  have h2:=mul_le_mul_of_nonneg_left (add_sq_le (a:=x) (b:=y)) (sq_nonneg a)
  have h3:=mul_le_mul_of_nonneg_left (add_sq_le (a:=z) (b:=w)) (sq_nonneg b)
  have hs : (a*(x+y)+b*(z+w))^2 ≤ 4*(a^2*(x^2+y^2)+b^2*(z^2+w^2)) := by
    nlinarith only [h1,h2,h3]
  convert mul_le_mul_of_nonneg_left hs (sq_nonneg K) using 1 <;> ring

/-- The actual label majorants are square-summed before any triangle over
labels; only the row, offset and source L2 square sums remain. -/
theorem sum_forcingLabelMajorant_sq_le (A b r τ : ℝ) (D : Fin (n+2)→FSC.Coord d)
    (h : Fin (n+2)→ℝ) (fD fu : Fin (n+2)→FSC.Coord d→ℝ) :
    (∑i,(forcingLabelMajorant A b r τ D h fD fu i)^2) ≤
      4*(planeDampingCoefficient b)^2*(r*planeErrorCoefficient A b n*τ⁻¹)^2*
        ((1+Real.sqrt (b*logScale n))^2*(∑i,‖D i‖^2)+(∑i,(h i)^2))+
      4*(planeDampingCoefficient b)^2*(Real.sqrt (2*Real.exp b)/r)^2*
        ((∑i,(realLp (stdGaussian (FSC.Coord d)) 2 (fD i))^2)+
          (∑i,(realLp (stdGaussian (FSC.Coord d)) 2 (fu i))^2)) := by
  have hi i := four_term_square (planeDampingCoefficient b) (r*planeErrorCoefficient A b n*τ⁻¹)
    (Real.sqrt (2*Real.exp b)/r) ((1+Real.sqrt (b*logScale n))*‖D i‖) |h i|
    (realLp (stdGaussian (FSC.Coord d)) 2 (fD i))
    (realLp (stdGaussian (FSC.Coord d)) 2 (fu i))
  have he i : (forcingLabelMajorant A b r τ D h fD fu i)^2 ≤
      4*(planeDampingCoefficient b)^2*
        ((r*planeErrorCoefficient A b n*τ⁻¹)^2*
          (((1+Real.sqrt (b*logScale n))*‖D i‖)^2+(h i)^2)+
          (Real.sqrt (2*Real.exp b)/r)^2*
          ((realLp (stdGaussian (FSC.Coord d)) 2 (fD i))^2+
            (realLp (stdGaussian (FSC.Coord d)) 2 (fu i))^2)) := by
    convert hi i using 1 <;> simp only [forcingLabelMajorant,sq_abs] <;> ring
  have hs:=Finset.sum_le_sum (fun i (_:i∈Finset.univ)=>he i)
  refine hs.trans_eq ?_
  simp only [mul_pow,mul_add,Finset.sum_add_distrib,←Finset.mul_sum]
  ring

end NegativeVotingStructuredSwitchingFacetEnergy
