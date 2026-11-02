import GaussianFiniteGraphRayleigh
import GaussianFiniteGraphCoarea
import Mathlib.Analysis.InnerProductSpace.Basic

/-! A physical weighted-graph gap with the unequal-row error retained.
No bound on graph degree or positive lower edge length is required. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingBoundedRowGraph
open NegativeVotingFiniteGraphRayleigh NegativeVotingFiniteGraph
variable {V E:Type*} [Fintype V] [Nonempty V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def rowLaplacian (w:V→V→ℝ) (B:V→E) (i:V):E:=∑j,w i j • (B i-B j)
def rowMetricDegree (w:V→V→ℝ) (B:V→E) (i:V):ℝ:=∑j,w i j*‖B i-B j‖^2
def labelEnergy (w:V→V→ℝ) (z:V→ℝ):ℝ:=(1/2:ℝ)*∑i,∑j,w i j*(z i-z j)^2
def metricPairEnergy (w:V→V→ℝ) (B:V→E) (z:V→ℝ):ℝ:=
  (1/2:ℝ)*∑i,∑j,w i j*‖B i-B j‖^2*(|z i|+|z j|)^2
def mixedMagnitude (w:V→V→ℝ) (B:V→E) (z:V→ℝ):ℝ:=
  (1/2:ℝ)*∑i,∑j,w i j*‖B i-B j‖*|z i-z j| *(|z i|+|z j|)

theorem row_metric_degree_identity (w:V→V→ℝ) (B:V→E) (i:V):
    rowMetricDegree w B i=2*inner ℝ (B i) (rowLaplacian w B i)-
      ∑j,w i j*(‖B i‖^2-‖B j‖^2):=by
  simp only [rowMetricDegree,rowLaplacian,inner_sum,real_inner_smul_right,
    Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [norm_sub_sq_real,inner_sub_right,real_inner_self_eq_norm_sq]
  ring

theorem scalar_edge_pairing (w:V→V→ℝ) (hsym:∀i j,w i j=w j i)
    (v t:V→ℝ):
    (∑i,t i*(∑j,w i j*(v i-v j)))=
      (1/2:ℝ)*∑i,∑j,w i j*(v i-v j)*(t i-t j):=by
  have hs:(∑i,∑j,w i j*(v i-v j)*t j)=-(∑i,∑j,w i j*(v i-v j)*t i):=by
    rw [Finset.sum_comm,←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym j i]
    ring
  have he (i j:V):w i j*(v i-v j)*(t i-t j)=
      w i j*(v i-v j)*t i-w i j*(v i-v j)*t j:=by ring
  simp_rw [he,Finset.sum_sub_distrib]
  rw [hs]
  have hl:(∑i,t i*(∑j,w i j*(v i-v j)))=∑i,∑j,w i j*(v i-v j)*t i:=by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hl]
  ring

theorem norm_squared_difference_le (B:V→E) (bmax:ℝ)
    (hB:∀i,‖B i‖≤ bmax) (i j:V):
    |‖B i‖^2-‖B j‖^2|≤2*bmax*‖B i-B j‖:=by
  have he:‖B i‖^2-‖B j‖^2=(‖B i‖-‖B j‖)*(‖B i‖+‖B j‖):=by ring
  rw [he,abs_mul,abs_of_nonneg (by positivity:0≤‖B i‖+‖B j‖)]
  calc
    _≤‖B i-B j‖*(2*bmax):=mul_le_mul (abs_norm_sub_norm_le _ _)
      (by linarith [hB i,hB j]) (by positivity) (norm_nonneg _)
    _=_:=by ring

theorem labelEnergy_nonneg (w:V→V→ℝ) (hw:∀i j,0≤ w i j) (z:V→ℝ):
    0≤ labelEnergy w z:=by
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _=>
    Finset.sum_nonneg fun j _=>mul_nonneg (hw i j) (sq_nonneg _))

theorem metricPairEnergy_nonneg (w:V→V→ℝ) (hw:∀i j,0≤ w i j) (B:V→E) (z:V→ℝ):
    0≤ metricPairEnergy w B z:=by
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _=>
    Finset.sum_nonneg fun j _=>mul_nonneg (mul_nonneg (hw i j) (sq_nonneg _)) (sq_nonneg _))

theorem mixedMagnitude_nonneg (w:V→V→ℝ) (hw:∀i j,0≤ w i j) (B:V→E) (z:V→ℝ):
    0≤ mixedMagnitude w B z:=by
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _=>
    Finset.sum_nonneg fun j _=>by positivity [hw i j])

/-- The actual physical edge lengths remain in the second Cauchy factor. -/
theorem mixedMagnitude_cauchy (w:V→V→ℝ) (hw:∀i j,0≤ w i j) (B:V→E) (z:V→ℝ):
    (mixedMagnitude w B z)^2≤ labelEnergy w z*metricPairEnergy w B z:=by
  let f:V×V→ℝ:=fun p=>Real.sqrt (w p.1 p.2)*|z p.1-z p.2|
  let g:V×V→ℝ:=fun p=>Real.sqrt (w p.1 p.2)*‖B p.1-B p.2‖*(|z p.1|+|z p.2|)
  have hp (p:V×V):f p*g p=w p.1 p.2*‖B p.1-B p.2‖*|z p.1-z p.2| *(|z p.1|+|z p.2|):=by
    dsimp [f,g]
    have hh:=Real.sq_sqrt (hw p.1 p.2)
    nlinarith [congrArg (fun x:ℝ=>x*‖B p.1-B p.2‖*|z p.1-z p.2| *(|z p.1|+|z p.2|)) hh]
  have hf (p:V×V):(f p)^2=w p.1 p.2*(z p.1-z p.2)^2:=by
    dsimp [f]
    rw [mul_pow,Real.sq_sqrt (hw p.1 p.2),sq_abs]
  have hg (p:V×V):(g p)^2=w p.1 p.2*‖B p.1-B p.2‖^2*(|z p.1|+|z p.2|)^2:=by
    dsimp [g]
    rw [mul_pow,mul_pow,Real.sq_sqrt (hw p.1 p.2)]
  have hh:=Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  simp_rw [hp,hf,hg,Fintype.sum_prod_type] at hh
  unfold mixedMagnitude labelEnergy metricPairEnergy
  nlinarith

/-- The finite scalar lower bound keeps the full mixed row-error term. -/
theorem gap_from_mixed_error (A B k E0 K S T:ℝ)
    (hA:0< A) (hB:0< B) (hk:0≤ k) (hE:0≤ E0) (hS:0≤ S) (hT:0≤ T)
    (hL:k*S≤2*T) (hC:T^2≤ E0*K) (hK:K≤ A*S+4*B*T):
    min (k^2/(16*A)) (k/(16*B))*S≤ E0:=by
  by_cases hSz:S=0
  · simp only [hSz,mul_zero]
    exact hE
  have hSp:0< S:=lt_of_le_of_ne hS (Ne.symm hSz)
  by_cases hlarge:k*S≤16*B*E0
  · calc
      _≤(k/(16*B))*S:=mul_le_mul_of_nonneg_right (min_le_right _ _) hS
      _≤ E0:=by
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ (show 0<16*B by positivity)).mpr
        nlinarith
  · have hBT:4*B*E0≤ T/2:=by linarith
    have hBTT:=mul_le_mul_of_nonneg_right hBT hT
    have hEK:=mul_le_mul_of_nonneg_left hK hE
    have ht2:T^2≤2*A*E0*S:=by nlinarith
    have hsq:=pow_le_pow_left₀ (mul_nonneg hk hS) hL 2
    have h8:k^2*S≤8*A*E0:=by
      apply (mul_le_mul_iff_right₀ hSp).mp
      nlinarith
    calc
      _≤(k^2/(16*A))*S:=mul_le_mul_of_nonneg_right (min_le_left _ _) hS
      _≤ E0:=by
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ (show 0<16*A by positivity)).mpr
        nlinarith [mul_nonneg hA.le hE]

theorem metricPairEnergy_le_degree (w:V→V→ℝ) (hw:∀i j,0≤ w i j)
    (hsym:∀i j,w i j=w j i) (B:V→E) (z:V→ℝ):
    metricPairEnergy w B z≤2*∑i,(z i)^2*rowMetricDegree w B i:=by
  let a:V→V→ℝ:=fun i j=>w i j*‖B i-B j‖^2
  have ha:∀i j,0≤ a i j:=fun i j=>mul_nonneg (hw i j) (sq_nonneg _)
  have has:∀i j,a i j=a j i:=by intro i j;dsimp [a];rw [hsym i j,norm_sub_rev (B i)]
  have hp (i j:V):(|z i|+|z j|)^2≤2*(z i)^2+2*(z j)^2:=by
    nlinarith [sq_nonneg (|z i|-|z j|),sq_abs (z i),sq_abs (z j)]
  have hu:=Finset.sum_le_sum (fun i (_:i∈Finset.univ)=>Finset.sum_le_sum
    (fun j (_:j∈Finset.univ)=>mul_le_mul_of_nonneg_left (hp i j) (ha i j)))
  have hc:(∑i,∑j,a i j*(z j)^2)=(∑i,∑j,a i j*(z i)^2):=by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [has j i]
  have he:(∑i,∑j,a i j*(2*(z i)^2+2*(z j)^2))=
      2*(∑i,∑j,a i j*(z i)^2)+2*(∑i,∑j,a i j*(z j)^2):=by
    have hh (i j:V):a i j*(2*(z i)^2+2*(z j)^2)=
        2*(a i j*(z i)^2)+2*(a i j*(z j)^2):=by ring
    simp_rw [hh,Finset.sum_add_distrib,←Finset.mul_sum]
  rw [he,hc] at hu
  have hr:(∑i,(z i)^2*rowMetricDegree w B i)=(∑i,∑j,a i j*(z i)^2):=by
    simp only [rowMetricDegree,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [a]
    ring
  rw [hr]
  change (1/2:ℝ)*(∑i,∑j,a i j*(|z i|+|z j|)^2)≤_
  linarith

theorem absolute_square_difference_upper (x y:ℝ):
    |x^2-y^2|≤|x-y| *(|x|+|y|):=by
  rw [show x^2-y^2=(x-y)*(x+y) by ring,abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_add_le x y) (abs_nonneg _)

/-- The unequal-row correction is retained with its full coefficient4. -/
theorem metricPairEnergy_row_error_bound (w:V→V→ℝ) (hw:∀i j,0≤ w i j)
    (hsym:∀i j,w i j=w j i) (B:V→E) (bmax mmax:ℝ)
    (hb:0≤ bmax) (hm:0≤ mmax) (hB:∀i,‖B i‖≤ bmax)
    (hM:∀i,‖rowLaplacian w B i‖≤ mmax) (z:V→ℝ):
    metricPairEnergy w B z≤4*bmax*mmax*(∑i,(z i)^2)+4*bmax*mixedMagnitude w B z:=by
  have hdegree:=metricPairEnergy_le_degree w hw hsym B z
  have hid:(∑i,(z i)^2*rowMetricDegree w B i)=
      2*(∑i,(z i)^2*inner ℝ (B i) (rowLaplacian w B i))-
      (1/2:ℝ)*∑i,∑j,w i j*(‖B i‖^2-‖B j‖^2)*((z i)^2-(z j)^2):=by
    have he (i:V):(z i)^2*rowMetricDegree w B i=
        2*((z i)^2*inner ℝ (B i) (rowLaplacian w B i))-
        (z i)^2*(∑j,w i j*(‖B i‖^2-‖B j‖^2)):=by
      rw [row_metric_degree_identity]
      ring
    simp_rw [he,Finset.sum_sub_distrib]
    rw [←Finset.mul_sum,scalar_edge_pairing w hsym (fun i=>‖B i‖^2) (fun i=>(z i)^2)]
  have hmoment:(∑i,(z i)^2*inner ℝ (B i) (rowLaplacian w B i))≤
      bmax*mmax*(∑i,(z i)^2):=by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hh:inner ℝ (B i) (rowLaplacian w B i)≤ bmax*mmax:=
      (real_inner_le_norm _ _).trans (mul_le_mul (hB i) (hM i) (norm_nonneg _) hb)
    nlinarith [mul_le_mul_of_nonneg_left hh (sq_nonneg (z i))]
  have herr:-(∑i,∑j,w i j*(‖B i‖^2-‖B j‖^2)*((z i)^2-(z j)^2))≤
      4*bmax*mixedMagnitude w B z:=by
    have hp (i j:V):-(w i j*(‖B i‖^2-‖B j‖^2)*((z i)^2-(z j)^2))≤
        2*bmax*(w i j*‖B i-B j‖*|z i-z j| *(|z i|+|z j|)):=by
      calc
        _≤|w i j*(‖B i‖^2-‖B j‖^2)*((z i)^2-(z j)^2)|:=neg_le_abs _
        _=w i j*|‖B i‖^2-‖B j‖^2| *|(z i)^2-(z j)^2|:=by
          rw [abs_mul,abs_mul,abs_of_nonneg (hw i j)]
        _≤ w i j*(2*bmax*‖B i-B j‖)*(|z i-z j| *(|z i|+|z j|)):=
          mul_le_mul (mul_le_mul_of_nonneg_left (norm_squared_difference_le B bmax hB i j) (hw i j))
            (absolute_square_difference_upper (z i) (z j)) (abs_nonneg _) (by positivity [hw i j])
        _=_:=by ring
    have hh:=Finset.sum_le_sum (fun i (_:i∈Finset.univ)=>Finset.sum_le_sum (fun j (_:j∈Finset.univ)=>hp i j))
    simp only [Finset.sum_neg_distrib,←Finset.mul_sum] at hh
    unfold mixedMagnitude
    nlinarith
  nlinarith

/-- Signed-square coarea removes any need to assume a median or bounded
graph degree. The actual physical edge metric stays visible. -/
theorem centered_l1_le_mixed (w:V→V→ℝ) (hw:∀i j,0≤ w i j) (B:V→E)
    (k:ℝ) (hk:0≤ k)
    (hL1:∀g:V→ℝ,(k/(Fintype.card V:ℝ))*(∑i,∑j,|g i-g j|)≤
      ∑i,∑j,‖B i-B j‖*w i j*|g i-g j|)
    (z:V→ℝ) (hz:∑i,z i=0):
    k*(∑i,(z i)^2)≤2*mixedMagnitude w B z:=by
  let g:V→ℝ:=fun i=>z i*|z i|
  have hm:0<(Fintype.card V:ℝ):=by exact_mod_cast Fintype.card_pos
  have hs:=Finset.sum_le_sum (fun i (_:i∈Finset.univ)=>Finset.sum_le_sum
    (fun j (_:j∈Finset.univ)=>signedSquare_difference_lower (z i) (z j)))
  rw [centered_pair_energy z hz] at hs
  simp only [←Finset.mul_sum] at hs
  have hlow:(Fintype.card V:ℝ)*(∑i,(z i)^2)≤∑i,∑j,|g i-g j|:=by dsimp [g];linarith
  have hmid:k*(∑i,(z i)^2)≤∑i,∑j,‖B i-B j‖*w i j*|g i-g j|:=by
    calc
      _=(k/(Fintype.card V:ℝ))*((Fintype.card V:ℝ)*(∑i,(z i)^2)):=by field_simp
      _≤(k/(Fintype.card V:ℝ))*(∑i,∑j,|g i-g j|):=mul_le_mul_of_nonneg_left hlow (by positivity)
      _≤_:=hL1 g
  have hhigh:(∑i,∑j,‖B i-B j‖*w i j*|g i-g j|)≤
      ∑i,∑j,w i j*‖B i-B j‖*|z i-z j| *(|z i|+|z j|):=by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    have hh:=mul_le_mul_of_nonneg_left (signedSquare_difference_upper (z i) (z j))
      (show 0≤‖B i-B j‖*w i j by positivity [hw i j])
    simpa only [g,mul_comm,mul_left_comm,mul_assoc] using hh
  have hh:=hmid.trans hhigh
  unfold mixedMagnitude
  nlinarith

/-- The physical cut bound and literal bounded row Laplacian imply a
separation-free spectral gap, with no degree bound or lower edge length. -/
theorem bounded_row_rayleigh (w:V→V→ℝ) (hw:∀i j,0≤ w i j)
    (hsym:∀i j,w i j=w j i) (B:V→E) (bmax mmax k:ℝ)
    (hb:0< bmax) (hm:0< mmax) (hk:0≤ k)
    (hB:∀i,‖B i‖≤ bmax) (hM:∀i,‖rowLaplacian w B i‖≤ mmax)
    (hcut:∀S:Finset V,k*min (S.card:ℝ) (Sᶜ.card:ℝ)≤
      cutWeight (fun i j=>‖B i-B j‖*w i j) S)
    (z:V→ℝ) (hz:∑i,z i=0):
    min (k^2/(64*bmax*mmax)) (k/(16*bmax))*(∑i,(z i)^2)≤ labelEnergy w z:=by
  have hws:∀i j,‖B i-B j‖*w i j=‖B j-B i‖*w j i:=by
    intro i j
    rw [norm_sub_rev (B i),hsym i j]
  have hL:=centered_l1_le_mixed w hw B k hk
    (weighted_l1_of_cut (fun i j=>‖B i-B j‖*w i j) k hk hws hcut) z hz
  have hh:=gap_from_mixed_error (4*bmax*mmax) bmax k (labelEnergy w z)
    (metricPairEnergy w B z) (∑i,(z i)^2) (mixedMagnitude w B z)
    (by positivity) hb hk (labelEnergy_nonneg w hw z)
    (Finset.sum_nonneg (fun i _=>sq_nonneg _)) (mixedMagnitude_nonneg w hw B z)
    hL (mixedMagnitude_cauchy w hw B z)
    (metricPairEnergy_row_error_bound w hw hsym B bmax mmax hb.le hm.le hB hM z)
  rwa [show 16*(4*bmax*mmax)=64*bmax*mmax by ring] at hh

end NegativeVotingBoundedRowGraph
