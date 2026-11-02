import GaussianBoundedRowGraph
import GaussianFanRetainedCuts
import GaussianFanCentroidBoundary
import GaussianMassCentroid
import GaussianAffineBasisLower

/-! The rank-uniform bounded-row gap for actual Gaussian affine fans.
An affine basis supplies the qualitative differential chart; its singular
value never enters the constants. Singular limiting fans are handled later. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Matrix
open scoped BigOperators RealInnerProductSpace
namespace NegativeVotingBoundedRowGap
open NegativeVotingBoundedRowGraph NegativeVotingFiniteGraph
open NegativeVotingFan NegativeVotingFanJacobian NegativeVotingFanScore
open NegativeVotingFanBoundary NegativeVotingFanRetained NegativeVotingFanCentroid
open NegativeVotingMassCentroid NegativeVotingAffineBasisLower
variable {V:Type*} [Fintype V] [DecidableEq V] [Nonempty V] {d:ℕ}

/-- Actual Gaussian cuts, with their physical edge lengths retained. -/
theorem physical_cut_expansion (B:V→FSC.Coord d) (h:V→ℝ)
    (hinj:Function.Injective B) (p0:ℝ) (hp0:0≤ p0)
    (hmass:∀i,p0≤ mass B h i) (S:Finset V):
    (p0/(2*Real.pi))*min (S.card:ℝ) (Sᶜ.card:ℝ)≤
      cutWeight (fun i j=>‖B i-B j‖*facetWeight B h i j) S:=by
  classical
  have hh:=gaussian_cut_jacobian_conductance B h hinj (S:Set V)
  simp only [sum_on_finset] at hh
  let w:V→V→ℝ:=fun i j=>‖B i-B j‖*facetWeight B h i j
  have hew (i j:V):‖B i-B j‖*facetWeight B h i j=w i j:=rfl
  simp_rw [hew] at hh
  simp only [double_sum_on_finset] at hh
  have ht:(∑i∈S,mass B h i)+(∑i∈Sᶜ,mass B h i)=1:=by
    rw [Finset.sum_add_sum_compl,mass_sum]
  have hm (T:Finset V):p0*(T.card:ℝ)≤∑i∈T,mass B h i:=by
    calc
      _=∑i∈T,p0:=by simp [Finset.sum_const,nsmul_eq_mul];ring
      _≤_:=Finset.sum_le_sum (fun i _=>hmass i)
  have hmin:p0*min (S.card:ℝ) (Sᶜ.card:ℝ)≤
      min (∑i∈S,mass B h i) (1-∑i∈S,mass B h i):=by
    apply le_min
    · exact (mul_le_mul_of_nonneg_left (min_le_left _ _) hp0).trans (hm S)
    · have hc:(1-∑i∈S,mass B h i)=∑i∈Sᶜ,mass B h i:=by linarith
      rw [hc]
      exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hp0).trans (hm Sᶜ)
  have hf:=hmin.trans hh
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (show 0<2*Real.pi by positivity)).mpr
  simpa only [w,mul_comm] using hf

def centroidCap (m C:ℝ):ℝ:=
  (C*Real.sqrt (2*Real.log m)+(Real.sqrt (2*Real.pi))⁻¹)/m

theorem centroid_norm_le_cap (B:V→FSC.Coord d) (h:V→ℝ)
    (m C:ℝ) (hm:1≤ m) (hmass:∀i,mass B h i≤ C/m) (i:V):
    ‖centroid B h i‖≤ centroidCap m C:=by
  have h01:∀ᵐx∂stdGaussian (FSC.Coord d),0≤ weights B h x i∧weights B h x i≤1:=by
    filter_upwards with x
    have hp:=weights_simplex B h x
    refine ⟨hp.1 i,?_⟩
    rw [←hp.2]
    exact Finset.single_le_sum (fun j _=>hp.1 j) (Finset.mem_univ i)
  exact gaussianCentroid_norm_le_logarithmic_mass_bound (fun x=>weights B h x i)
    m C hm (weights_measurable B h i).aemeasurable h01 (hmass i)

/-- All graph and centroid hypotheses are derived from literal fan data.
The constants contain no inverse singular value or minimum edge length. -/
theorem gaussian_bounded_row_rayleigh (b:AffineBasis V ℝ (FSC.Coord d))
    (h:V→ℝ) (m C p0 bmax mmax:ℝ) (hm:1≤ m)
    (hp0:0≤ p0) (hb:0< bmax) (hM:0< mmax)
    (hmass:∀i,p0≤ mass b h i∧mass b h i≤ C/m)
    (hB:∀i,‖b i‖≤ bmax) (hcap:centroidCap m C≤ mmax)
    (z:V→ℝ) (hz:∑i,z i=0):
    min ((p0/(2*Real.pi))^2/(64*bmax*mmax))
      ((p0/(2*Real.pi))/(16*bmax))*(∑i,(z i)^2)≤
      z ⬝ᵥ (offsetJacobian b h *ᵥ z):=by
  classical
  obtain ⟨σ,hσ,hlower⟩:=exists_centeredSingularLowerBound b
  have hrow (i:V):‖rowLaplacian (facetWeight b h) b i‖≤ mmax:=by
    change ‖∑j,facetWeight b h i j • (b i-b j)‖≤ mmax
    rw [←centroid_eq_boundary_laplacian b h σ hσ hlower i]
    exact (centroid_norm_le_cap b h m C hm (fun j=>(hmass j).2) i).trans hcap
  rw [offsetJacobian_energy]
  exact bounded_row_rayleigh (facetWeight b h) (facetWeight_nonneg b h)
    (facetWeight_symm b h) b bmax mmax (p0/(2*Real.pi)) hb hM (by positivity)
    hB hrow (physical_cut_expansion b h b.ind.injective p0 hp0 (fun i=>(hmass i).1)) z hz

/-- The actual Gaussian centroid cap on the half-to-three-halves mass box. -/
theorem centroidCap_three_halves (m:ℝ) (hm:1≤ m):
    centroidCap m (3/2)≤4*Real.sqrt (1+Real.log m)/m:=by
  have hl:0≤ Real.log m:=Real.log_nonneg hm
  have hL:0≤1+Real.log m:=by linarith
  have hs:1≤ Real.sqrt (1+Real.log m):=by
    simpa using Real.sqrt_le_sqrt (show (1:ℝ)≤1+Real.log m by linarith)
  have hroot:Real.sqrt (2*Real.log m)≤2*Real.sqrt (1+Real.log m):=by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt hL]
    nlinarith
  have hp:1≤ Real.sqrt (2*Real.pi):=by
    simpa using Real.sqrt_le_sqrt (show (1:ℝ)≤2*Real.pi by linarith [Real.pi_gt_three])
  have hinv:(Real.sqrt (2*Real.pi))⁻¹≤1:=by
    rw [inv_eq_one_div]
    exact (div_le_one (by positivity)).mpr hp
  unfold centroidCap
  apply div_le_div_of_nonneg_right _ (by linarith)
  linarith

/-- Explicit inverse-logarithmic gap throughout the balanced mass box,
independent of the affine basis condition number. -/
theorem uniform_box_rayleigh (b:AffineBasis V ℝ (FSC.Coord d)) (h:V→ℝ)
    (m:ℝ) (hm:1≤ m)
    (hmass:∀i,1/(2*m)≤ mass b h i∧mass b h i≤(3/2)/m)
    (hB:∀i,‖b i‖≤8*Real.sqrt (1+Real.log m)/m)
    (z:V→ℝ) (hz:∑i,z i=0):
    (1/(32768*Real.pi^2*(1+Real.log m)))*(∑i,(z i)^2)≤
      z ⬝ᵥ (offsetJacobian b h *ᵥ z):=by
  have hmp:0< m:=by linarith
  let L:ℝ:=1+Real.log m
  let s:ℝ:=Real.sqrt L
  have hL:1≤ L:=by dsimp [L];linarith [Real.log_nonneg hm]
  have hsp:0< s:=Real.sqrt_pos.mpr (by linarith)
  have hsq:s^2=L:=Real.sq_sqrt (by linarith)
  have hs:1≤ s:=by simpa [s] using Real.sqrt_le_sqrt hL
  have hh:=gaussian_bounded_row_rayleigh b h m (3/2) (1/(2*m)) (8*s/m) (4*s/m)
    hm (by positivity) (by positivity) (by positivity) hmass hB (centroidCap_three_halves m hm) z hz
  have hc1:((1/(2*m))/(2*Real.pi))^2/(64*(8*s/m)*(4*s/m))=
      1/(32768*Real.pi^2*L):=by
    field_simp
    rw [←hsq]
    ring
  have hc2:((1/(2*m))/(2*Real.pi))/(16*(8*s/m))=1/(512*Real.pi*s):=by
    field_simp
    norm_num
  have hcoeff:1/(32768*Real.pi^2*L)≤1/(512*Real.pi*s):=by
    apply one_div_le_one_div_of_le (by positivity)
    have hSL:s≤ L:=by nlinarith
    have hp:1≤64*Real.pi:=by linarith [Real.pi_gt_three]
    have ht:=mul_le_mul_of_nonneg_right hp (show 0≤ L by linarith)
    have hu:s≤64*Real.pi*L:=hSL.trans (by nlinarith)
    have hh:=mul_le_mul_of_nonneg_left hu (show 0≤512*Real.pi by positivity)
    nlinarith
  rw [hc1,hc2,min_eq_left hcoeff] at hh
  exact hh

end NegativeVotingBoundedRowGap
