import GaussianCapPolynomialStein

/-! Actual quadratic and cubic Gaussian Stein boundary identities obtained
by finite algebraic polarization of the proved power identities. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace BigOperators ENNReal Topology Classical
namespace NegativeVotingCapPolarizedStein
open NegativeVotingPolyhedral NegativeVotingPolynomialTilt NegativeVotingCapPolynomialStein
variable {d : ℕ} {ι : Type*} [Fintype ι]

 theorem cap_inner_pow_memLp_two (w : ι→FSC.Coord d) (b : ι→ℝ)
    (v : FSC.Coord d) (k : ℕ) :
    MemLp (fun x=> (inner ℝ v x)^k) 2 ((stdGaussian (FSC.Coord d)).restrict (FSC.cap w b)) := by
  simpa only [zero_mul,Real.exp_zero,mul_one] using pow_exp_memLp_two
    ((stdGaussian (FSC.Coord d)).restrict (FSC.cap w b)) (fun x=>inner ℝ v x)
    (by fun_prop) (cap_integrableExpSet w b v) k 0

 theorem face_inner_pow_memLp_two (w : ι→FSC.Coord d) (b : ι→ℝ) (j : ι)
    (v : FSC.Coord d) (k : ℕ) :
    MemLp (fun x=> (inner ℝ v x)^k) 2 ((FSC.sliceLaw (w j) (b j)).restrict (faceEvent w b j)) := by
  letI : IsGaussian (FSC.sliceLaw (w j) (b j)) := sliceLaw_isGaussian (w j) (b j)
  simpa only [zero_mul,Real.exp_zero,mul_one] using pow_exp_memLp_two
    ((FSC.sliceLaw (w j) (b j)).restrict (faceEvent w b j)) (fun x=>inner ℝ v x)
    (by fun_prop) (face_integrableExpSet w b j v) k 0

 theorem gaussian_cap_power_combination_stein {κ : Type*} [Fintype κ]
    (w : ι→FSC.Coord d) (hw : ∀ j,‖w j‖=1) (b : ι→ℝ)
    (hb : FSC.NoCoincident w b) (u : FSC.Coord d) (V : κ→FSC.Coord d)
    (c : κ→ℝ) (k : ℕ) :
    (∫ x in FSC.cap w b,inner ℝ u x*(∑ l,c l*(inner ℝ (V l) x)^(k+1))
      ∂stdGaussian (FSC.Coord d))=
    (∫ x in FSC.cap w b,∑ l,(((k+1:ℕ):ℝ)*c l*inner ℝ u (V l))*(inner ℝ (V l) x)^k
      ∂stdGaussian (FSC.Coord d))-
    ∑ j,(WeakSimplex.normalPDF (b j)*inner ℝ (w j) u)*
      (∫ x in faceEvent w b j,∑ l,c l*(inner ℝ (V l) x)^(k+1) ∂FSC.sliceLaw (w j) (b j)) := by
  letI (j:ι) : IsGaussian (FSC.sliceLaw (w j) (b j)) := sliceLaw_isGaussian (w j) (b j)
  have hp (v:FSC.Coord d) (r:ℕ) :=
    (cap_inner_pow_memLp_two w b v r).integrable (by norm_num : (1:ℝ≥0∞)≤2)
  have hfp (j:ι) (v:FSC.Coord d) (r:ℕ) :=
    (face_inner_pow_memLp_two w b j v r).integrable (by norm_num : (1:ℝ≥0∞)≤2)
  have hu : MemLp (fun x:FSC.Coord d=>inner ℝ u x) 2
      ((stdGaussian (FSC.Coord d)).restrict (FSC.cap w b)) :=
    (IsGaussian.memLp_two_id.const_inner (𝕜:=ℝ) u).restrict _
  have hmix (l:κ) : Integrable (fun x:FSC.Coord d=>inner ℝ u x*(c l*(inner ℝ (V l) x)^(k+1)))
      ((stdGaussian (FSC.Coord d)).restrict (FSC.cap w b)) := by
    simpa only [Pi.mul_def] using hu.integrable_mul ((cap_inner_pow_memLp_two w b (V l) (k+1)).const_mul (c l))
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun l _=>hmix l),
    integral_finsetSum Finset.univ (fun l _=>(hp (V l) k).const_mul _)]
  simp_rw [integral_finsetSum Finset.univ (fun l _=>(hfp _ (V l) (k+1)).const_mul (c l))]
  have hi (l:κ) : (∫ x in FSC.cap w b,inner ℝ u x*(c l*(inner ℝ (V l) x)^(k+1))
      ∂stdGaussian (FSC.Coord d))=
      c l*(∫ x in FSC.cap w b,inner ℝ u x*(inner ℝ (V l) x)^(k+1) ∂stdGaussian (FSC.Coord d)) := by
    rw [←integral_const_mul]
    congr 1
    funext x
    ring
  simp_rw [hi,gaussian_cap_power_stein w hw b hb,integral_const_mul,
    mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro l _
    ring
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    ring

/-- The actual polarized quadratic identity. -/
 theorem gaussian_cap_bilinear_stein (w : ι→FSC.Coord d) (hw : ∀ j,‖w j‖=1)
    (b : ι→ℝ) (hb : FSC.NoCoincident w b) (u v z : FSC.Coord d) :
    (∫ x in FSC.cap w b,inner ℝ u x*(inner ℝ v x*inner ℝ z x) ∂stdGaussian (FSC.Coord d))=
      (∫ x in FSC.cap w b,inner ℝ u v*inner ℝ z x+inner ℝ u z*inner ℝ v x
        ∂stdGaussian (FSC.Coord d))-
      ∑ j,(WeakSimplex.normalPDF (b j)*inner ℝ (w j) u)*
        (∫ x in faceEvent w b j,inner ℝ v x*inner ℝ z x ∂FSC.sliceLaw (w j) (b j)) := by
  let V : Fin 3→FSC.Coord d := ![v+z,v,z]
  let c : Fin 3→ℝ := ![1/2,-1/2,-1/2]
  have hF (x:FSC.Coord d) : (∑ l,c l*(inner ℝ (V l) x)^(1+1))=inner ℝ v x*inner ℝ z x := by
    simp only [V,c,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Fin.sum_univ_zero,add_zero,inner_add_left]
    ring
  have hG (x:FSC.Coord d) : (∑ l,(((1+1:ℕ):ℝ)*c l*inner ℝ u (V l))*(inner ℝ (V l) x)^1)=
      inner ℝ u v*inner ℝ z x+inner ℝ u z*inner ℝ v x := by
    simp only [V,c,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Fin.sum_univ_zero,add_zero,inner_add_left,inner_add_right]
    norm_num
    ring
  have hh := gaussian_cap_power_combination_stein w hw b hb u V c 1
  simp_rw [hF,hG] at hh
  exact hh

/-- The actual polarized cubic identity, including its literal polyhedral
face measure. This is the degree needed by quadratic affine transport. -/
 theorem gaussian_cap_trilinear_stein (w : ι→FSC.Coord d) (hw : ∀ j,‖w j‖=1)
    (b : ι→ℝ) (hb : FSC.NoCoincident w b) (u v z y : FSC.Coord d) :
    (∫ x in FSC.cap w b,inner ℝ u x*(inner ℝ v x*inner ℝ z x*inner ℝ y x)
      ∂stdGaussian (FSC.Coord d))=
      (∫ x in FSC.cap w b,inner ℝ u v*(inner ℝ z x*inner ℝ y x)+
        inner ℝ u z*(inner ℝ v x*inner ℝ y x)+inner ℝ u y*(inner ℝ v x*inner ℝ z x)
        ∂stdGaussian (FSC.Coord d))-
      ∑ j,(WeakSimplex.normalPDF (b j)*inner ℝ (w j) u)*
        (∫ x in faceEvent w b j,inner ℝ v x*inner ℝ z x*inner ℝ y x ∂FSC.sliceLaw (w j) (b j)) := by
  let V : Fin 7→FSC.Coord d := ![v+z+y,v+z,v+y,z+y,v,z,y]
  let c : Fin 7→ℝ := ![1/6,-1/6,-1/6,-1/6,1/6,1/6,1/6]
  have hF (x:FSC.Coord d) : (∑ l,c l*(inner ℝ (V l) x)^(2+1))=
      inner ℝ v x*inner ℝ z x*inner ℝ y x := by
    simp only [V,c,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Fin.sum_univ_zero,add_zero,inner_add_left]
    ring
  have hG (x:FSC.Coord d) : (∑ l,(((2+1:ℕ):ℝ)*c l*inner ℝ u (V l))*(inner ℝ (V l) x)^2)=
      inner ℝ u v*(inner ℝ z x*inner ℝ y x)+inner ℝ u z*(inner ℝ v x*inner ℝ y x)+
        inner ℝ u y*(inner ℝ v x*inner ℝ z x) := by
    simp only [V,c,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Fin.sum_univ_zero,add_zero,inner_add_left,inner_add_right]
    norm_num
    ring
  have hh := gaussian_cap_power_combination_stein w hw b hb u V c 2
  simp_rw [hF,hG] at hh
  exact hh

end NegativeVotingCapPolarizedStein
