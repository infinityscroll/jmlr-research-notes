import GaussianDiagonalSecondForcingBound

/-! L1 inversion of the physical balancing Laplacian and summed derivative
coefficients. The displayed balance equation remains an explicit hypothesis
until the actual second-differentiability bridge is supplied. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Set
open scoped BigOperators Classical Topology
namespace NegativeVotingDiagonalSecondOffsetBound
open NegativeVotingDiagonalSecondForcingBound NegativeVotingDiagonalDerivativeEnvelopes
  NegativeVotingCompleteGraphComponentInverse NegativeVotingDiagonalBalanceEquation
  NegativeVotingDiagonalHazardDifferentiation NegativeVotingDiagonalFacetIntegral
  NegativeVotingDiagonalWinnerIntegral NegativeVotingFanInverse NegativeVotingFanJacobian
  NegativeVotingDiagonalUniformOffsetBound NegativeVotingDiagonalOffsetComponentBound
  NegativeVotingHazardQuantileAsymptotics NegativeVotingGaussianMaximum
  NegativeVotingDiagonalOffsetContinuation NegativeVotingHazardMomentEnvelope

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- A diagonal value is supplied only to invoke the complete-graph theorem;
it cancels identically from the physical equation. -/
theorem off_diagonal_l1_bound (w : V→V→ℝ) (hsym : ∀i j,w i j=w j i)
    (a : ℝ) (ha : 0 < a)
    (hlower : ∀i j,i≠j → a/(Fintype.card V:ℝ) ≤ w i j)
    (v b : V→ℝ) (hv : ∑i,v i=0) (heq : ∀i,(∑j,w i j*(v i-v j))=b i) :
    a*(∑i,|v i|) ≤ ∑i,|b i| := by
  let w' : V→V→ℝ := fun i j=>if i=j then a/(Fintype.card V:ℝ) else w i j
  have hs : ∀i j,w' i j=w' j i := by
    intro i j
    by_cases hij:i=j
    · subst j;rfl
    · simp only [w',hij,Ne.symm hij,ite_false,hsym i j]
  have hlo : ∀i j,a/(Fintype.card V:ℝ) ≤ w' i j := by
    intro i j
    by_cases hij:i=j
    · simp [w',hij]
    · simpa only [w',hij,ite_false] using hlower i j hij
  have he : ∀i,(∑j,w' i j*(v i-v j))=b i := by
    intro i
    rw [←heq i]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij:i=j <;> simp [w',hij]
  exact centered_laplacian_l1_bound w' hs a ha hlo v b hv he

/-- Exact exponent bookkeeping for the physical second-offset equation.
Only the summed source is needed; no coordinate acceleration bound occurs. -/
theorem diagonal_secondOffset_l1_bound {n : ℕ}
    (η : ℝ) (hη : 0 < η) (σ h source ξ : Fin (n+2)→ℝ)
    (hσ : ∀i,0 < σ i) (v : centeredGauge (Fin (n+2)))
    (hlower : ∀i j,i≠j → ((n:ℝ)+2)^(-2-η/2) ≤ ∫x,hazardPairDensity σ h x i j)
    (heq : ∀i,offsetLaplacian σ h v i= -source i)
    (hsource : (∑i,|source i|) ≤ ((n:ℝ)+2)^(-1+8*η)*(∑i,(ξ i)^2)) :
    (∑i,|(v : Fin (n+2)→ℝ) i|) ≤ ((n:ℝ)+2)^(9*η)*(∑i,(ξ i)^2) := by
  let m : ℝ := (n:ℝ)+2
  let a := m^(-1-η/2)
  have hm : 0 < m := by dsimp [m];positivity
  have hm1 : 1 ≤ m := by dsimp [m];linarith [Nat.cast_nonneg (α:=ℝ) n]
  have ha : 0 < a := Real.rpow_pos_of_pos hm _
  have hlo (i j:Fin (n+2)) (hij:i≠j) : a/(Fintype.card (Fin (n+2)):ℝ) ≤
      facetWeight (diagonalRows σ) h i j := by
    rw [facetWeight_diagonal_integral σ h hσ i j hij]
    have he : a/(Fintype.card (Fin (n+2)):ℝ)=m^(-2-η/2) := by
      simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat]
      change a/m=_
      dsimp [a]
      rw [rpow_div_size _ _ hm]
      congr 1;ring
    rw [he]
    exact hlower i j hij
  have hi := off_diagonal_l1_bound (facetWeight (diagonalRows σ) h)
    (facetWeight_symm _ _) a ha hlo v (fun i=>-source i) v.property heq
  simp only [abs_neg] at hi
  have hraw : (∑i,|(v : Fin (n+2)→ℝ) i|) ≤ (m^(-1+8*η)/a)*(∑i,(ξ i)^2) := by
    apply (mul_le_mul_iff_right₀ ha).mp
    have ht := hi.trans hsource
    convert ht using 1 <;> field_simp <;> ring
  have hexp : m^(-1+8*η)/a=m^(17*η/2) := by
    dsimp [a]
    rw [←Real.rpow_sub hm]
    congr 1;ring
  rw [hexp] at hraw
  refine hraw.trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _=>sq_nonneg _))
  exact Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)

lemma secondEnvelope_split (H σ₁ h₁ σ₂ h₂ : ℝ) :
    secondEnvelope H σ₁ h₁ σ₂ h₂ =
      secondEnvelope H σ₁ h₁ σ₂ 0+128*(1+H)^2*|h₂| := by
  unfold secondEnvelope;simp only [abs_zero];ring

/-- Full acceleration enters the summed envelope only via its L1 norm. -/
theorem sum_full_variance_coefficients (H T : ℝ) (hH : 0 ≤ H) (hT : 1 ≤ T)
    (σ h₁ h₂ ξ : V→ℝ) (hσ : ∀i,1/2 ≤ σ i)
    (hk : ∀i,|h₁ i| ≤ T*(|ξ i|+meanAbs ξ)) :
    4*(∑i,(firstEnvelope H (ξ i/(2*σ i)) (h₁ i))^2)+
      (∑i,secondEnvelope H (ξ i/(2*σ i)) (h₁ i) (-(ξ i)^2/(4*(σ i)^3)) (h₂ i)) ≤
      32768*(1+H)^4*T^2*(∑i,(ξ i)^2)+128*(1+H)^2*(∑i,|h₂ i|) := by
  have hsplit : (∑i,secondEnvelope H (ξ i/(2*σ i)) (h₁ i) (-(ξ i)^2/(4*(σ i)^3)) (h₂ i)) =
      (∑i,secondEnvelope H (ξ i/(2*σ i)) (h₁ i) (-(ξ i)^2/(4*(σ i)^3)) 0)+
        128*(1+H)^2*(∑i,|h₂ i|) := by
    calc
      _ = ∑i,(secondEnvelope H (ξ i/(2*σ i)) (h₁ i) (-(ξ i)^2/(4*(σ i)^3)) 0+
          128*(1+H)^2*|h₂ i|) := Finset.sum_congr rfl (fun i _=>secondEnvelope_split ..)
      _ = _ := by rw [Finset.sum_add_distrib,Finset.mul_sum]
  rw [hsplit]
  have hh := sum_variance_coefficients H T hH hT (fun i=>ξ i/(2*σ i)) h₁
    (fun i=>-(ξ i)^2/(4*(σ i)^3)) ξ
    (fun i=>variance_speed_abs_le _ _ (hσ i))
    (fun i=>variance_acceleration_abs_le _ _ (hσ i)) hk
  linarith

/-- Pure scalar absorption of the complete q/u coefficient. The h'' input
here is exactly the L1 output of the preceding physical Laplacian theorem. -/
theorem eventually_full_variance_coefficients (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ (σ h₁ h₂ ξ : Fin (n+2)→ℝ) (H : ℝ),
      (∀i,1/2 ≤ σ i) → 0 ≤ H → H ≤ upperQuantile n →
      (∀i,|h₁ i| ≤ ((n:ℝ)+2)^(3*η)*(|ξ i|+meanAbs ξ)) →
      (∑i,|h₂ i|) ≤ ((n:ℝ)+2)^(9*η)*(∑i,(ξ i)^2) →
      4*(∑i,(firstEnvelope H (ξ i/(2*σ i)) (h₁ i))^2)+
        (∑i,secondEnvelope H (ξ i/(2*σ i)) (h₁ i) (-(ξ i)^2/(4*(σ i)^3)) (h₂ i)) ≤
        ((n:ℝ)+2)^(10*η)*(∑i,(ξ i)^2) := by
  have hpoly₁ := eventually_rpow_quantile_polynomial_le 65536 (by norm_num) 4
    (6*η) (10*η) (by linarith)
  have hpoly₂ := eventually_rpow_quantile_polynomial_le 256 (by norm_num) 2
    (9*η) (10*η) (by linarith)
  filter_upwards [hpoly₁,hpoly₂] with n hn₁ hn₂
  intro σ h₁ h₂ ξ H hσ hH hHb hk hacc
  let m : ℝ := (n:ℝ)+2
  let E : ℝ := ∑i,(ξ i)^2
  have hm : 0 < m := by dsimp [m];positivity
  have hm1 : 1 ≤ m := by dsimp [m];linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _=>sq_nonneg _
  have ht : 1 ≤ m^(3*η) := Real.one_le_rpow hm1 (by positivity)
  have hb₁ : (1+H)^4 ≤ (1+upperQuantile n)^4 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 4
  have hb₂ : (1+H)^2 ≤ (1+upperQuantile n)^2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hp : (m^(3*η))^2=m^(6*η) := by
    rw [←Real.rpow_mul_natCast hm.le]
    congr 1;ring
  have hbase := sum_full_variance_coefficients H (m^(3*η)) hH ht σ h₁ h₂ ξ hσ hk
  rw [hp] at hbase
  have hterm₁ : 32768*(1+H)^4*m^(6*η)*E ≤ (m^(10*η)/2)*E := by
    have hh := mul_le_mul_of_nonneg_left hb₁ (by positivity : (0:ℝ) ≤ 65536*m^(6*η))
    have hc : 32768*(1+H)^4*m^(6*η) ≤ m^(10*η)/2 := by
      dsimp [m] at hh ⊢
      nlinarith
    exact (by convert mul_le_mul_of_nonneg_right hc hE using 1 <;> ring)
  have hterm₂ : 128*(1+H)^2*(∑i,|h₂ i|) ≤ (m^(10*η)/2)*E := by
    have ha := mul_le_mul_of_nonneg_left hacc (by positivity : (0:ℝ) ≤ 128*(1+H)^2)
    have hh := mul_le_mul_of_nonneg_left hb₂ (by positivity : (0:ℝ) ≤ 256*m^(9*η))
    have hc : 128*(1+H)^2*m^(9*η) ≤ m^(10*η)/2 := by
      dsimp [m] at hh ⊢
      nlinarith
    exact ha.trans (by convert mul_le_mul_of_nonneg_right hc hE using 1 <;> ring)
  nlinarith

/-- The actual continuation box, source estimate and L1 inversion use the
same width. The final implication is deliberately conditional only on the
literal differentiated balancing equation, not on any acceleration estimate. -/
theorem exists_uniform_variance_second_control (η A : ℝ) (hη : 0 < η) (hA : 0 ≤ A) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1/16 ∧
      ∀ᶠ n : ℕ in atTop, MomentBoxControl n a η 2 8 ∧
        ∀ (ξ : Fin (n+2)→ℝ), (∀i,|ξ i| ≤ A) →
        ∀ t∈Icc 0 (((n:ℝ)+2)^(-30*η)),
          ∃ k : centeredGauge (Fin (n+2)),
            HasDerivAt (varianceOffsets n ξ) k t ∧
            (∀i,|(k : Fin (n+2)→ℝ) i| ≤ ((n:ℝ)+2)^(3*η)*(|ξ i|+meanAbs ξ)) ∧
            (∀i,1-a ≤ varianceSigma ξ t i ∧ varianceSigma ξ t i ≤ 1+a) ∧
            (∀i,|varianceOffsetVector n ξ t i| ≤ a*upperQuantile n) ∧
            (∑i,|secondForcing (varianceSigma ξ t) (varianceOffsetVector n ξ t)
              (fun i=>ξ i/(2*varianceSigma ξ t i)) k
              (fun i=>-(ξ i)^2/(4*(varianceSigma ξ t i)^3)) i|) ≤
              ((n:ℝ)+2)^(-1+8*η)*(∑i,(ξ i)^2) ∧
            ∀ v : centeredGauge (Fin (n+2)),
              (∀i,offsetLaplacian (varianceSigma ξ t) (varianceOffsetVector n ξ t) v i=
                -secondForcing (varianceSigma ξ t) (varianceOffsetVector n ξ t)
                  (fun i=>ξ i/(2*varianceSigma ξ t i)) k
                  (fun i=>-(ξ i)^2/(4*(varianceSigma ξ t i)^3)) i) →
              (∑i,|(v : Fin (n+2)→ℝ) i|) ≤ ((n:ℝ)+2)^(9*η)*(∑i,(ξ i)^2) ∧
              4*(∑i,(firstEnvelope (a*upperQuantile n)
                (ξ i/(2*varianceSigma ξ t i)) ((k : Fin (n+2)→ℝ) i))^2)+
                (∑i,secondEnvelope (a*upperQuantile n) (ξ i/(2*varianceSigma ξ t i))
                  ((k : Fin (n+2)→ℝ) i) (-(ξ i)^2/(4*(varianceSigma ξ t i)^3))
                  ((v : Fin (n+2)→ℝ) i)) ≤ ((n:ℝ)+2)^(10*η)*(∑i,(ξ i)^2) := by
  obtain ⟨a,ha,ha1,hcont⟩ := exists_uniform_variance_offset_continuation η A hη hA
  have habs := eventually_rpow_quantile_polynomial_le 393216 (by norm_num) 4
    (-1+13*η/2) (-1+8*η) (by linarith)
  refine ⟨a,ha,ha1,?_⟩
  filter_upwards [hcont,habs,eventually_full_variance_coefficients η hη,
    upperQuantile_tendsto.eventually_ge_atTop 1] with n hn habs_n hcoeff hb
  refine ⟨hn.1,?_⟩
  intro ξ hξ t ht
  obtain ⟨hσ,hh,hsmall,k,hk,hkbound⟩ := hn.2 ξ hξ t ht
  let m : ℝ := (n:ℝ)+2
  let b : ℝ := upperQuantile n
  have hm : 0 < m := by dsimp [m];positivity
  have hb0 : 0 ≤ b := by dsimp [b];linarith
  have hm1 : 1 ≤ m := by dsimp [m];linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hhalf (i:Fin (n+2)) : 1/2 ≤ varianceSigma ξ t i := by linarith [(hσ i).1]
  have hpos (i:Fin (n+2)) : 0 < varianceSigma ξ t i := by linarith [hhalf i]
  have hoff (i:Fin (n+2)) : |varianceOffsetVector n ξ t i| ≤ a*b := (hh i).le
  have haone : a ≤ 1 := by linarith
  have hab : a*b ≤ b := by nlinarith
  have hm₀ (i j:Fin (n+2)) := (hn.1 0 4 (by norm_num) (by norm_num)
    (varianceSigma ξ t) (varianceOffsetVector n ξ t)
    (fun i=>(hσ i).1) (fun i=>(hσ i).2) hoff i j).2.1
  have hm₂ (i j:Fin (n+2)) := (hn.1 2 4 (by norm_num) (by norm_num)
    (varianceSigma ξ t) (varianceOffsetVector n ξ t)
    (fun i=>(hσ i).1) (fun i=>(hσ i).2) hoff i j).2.1
  have hlo (i j:Fin (n+2)) (_:i≠j) := (hn.1 0 4 (by norm_num) (by norm_num)
    (varianceSigma ξ t) (varianceOffsetVector n ξ t)
    (fun i=>(hσ i).1) (fun i=>(hσ i).2) hoff i j).1
  have hsource : (∑i,|secondForcing (varianceSigma ξ t) (varianceOffsetVector n ξ t)
      (fun i=>ξ i/(2*varianceSigma ξ t i)) k
      (fun i=>-(ξ i)^2/(4*(varianceSigma ξ t i)^3)) i|) ≤ m^(-1+8*η)*(∑i,(ξ i)^2) := by
    have hbase := variance_secondForcing_bound (varianceSigma ξ t) (varianceOffsetVector n ξ t)
      k ξ (a*b) (m^(3*η)) (m^(-2+η/2)) hhalf (mul_nonneg ha.le hb0) hoff
      (Real.one_le_rpow hm1 (by positivity)) (Real.rpow_nonneg hm.le _) hkbound hm₀ hm₂
    have hscale : 393216*(Fintype.card (Fin (n+2)):ℝ)*m^(-2+η/2)*(1+a*b)^4*(m^(3*η))^2 =
        393216*m^(-1+13*η/2)*(1+a*b)^4 := by
      simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat]
      change 393216*m*m^(-2+η/2)*(1+a*b)^4*(m^(3*η))^2 = _
      rw [←Real.rpow_mul_natCast hm.le]
      calc
        _ = 393216*(m^(1:ℝ)*m^(-2+η/2)*m^(3*η*2))*(1+a*b)^4 := by rw [Real.rpow_one];ring
        _ = _ := by rw [←Real.rpow_add hm,←Real.rpow_add hm];congr 2 <;> ring
    rw [hscale] at hbase
    have hpoly : (1+a*b)^4 ≤ (1+b)^4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
    have hcoef : 393216*m^(-1+13*η/2)*(1+a*b)^4 ≤ m^(-1+8*η) :=
      (mul_le_mul_of_nonneg_left hpoly (by positivity)).trans habs_n
    exact hbase.trans (mul_le_mul_of_nonneg_right hcoef (Finset.sum_nonneg fun _ _=>sq_nonneg _))
  refine ⟨k,hk,hkbound,hσ,hoff,hsource,?_⟩
  intro v heq
  have hv := diagonal_secondOffset_l1_bound η hη (varianceSigma ξ t) (varianceOffsetVector n ξ t)
    (secondForcing (varianceSigma ξ t) (varianceOffsetVector n ξ t)
      (fun i=>ξ i/(2*varianceSigma ξ t i)) k
      (fun i=>-(ξ i)^2/(4*(varianceSigma ξ t i)^3))) ξ hpos v hlo heq hsource
  exact ⟨hv,hcoeff (varianceSigma ξ t) k v ξ (a*b) hhalf (mul_nonneg ha.le hb0) hab hkbound hv⟩

end NegativeVotingDiagonalSecondOffsetBound
