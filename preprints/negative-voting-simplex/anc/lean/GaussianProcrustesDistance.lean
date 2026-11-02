import GaussianRayDeficit

/-! Rectangular regular-orbit approximation, with singular row maps included.
The construction extends an isometry on a range rather than dividing by a
possibly zero singular value. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology RealInnerProductSpace Classical
namespace NegativeVotingProcrustes
open NegativeVotingRayDeficit NegativeVotingAffineNormControl
  NegativeVotingAffineLogMassBound NegativeVotingPositiveCovariance
  NegativeVotingCovarianceRealization NegativeVotingCenteredParseval
  NegativeVotingBalancedReference NegativeVotingRegularCovarianceDeficit
variable {d e m n:ℕ}

section IsometricExtension
variable {E V:Type*} [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Equal norms of two linear realizations produce an actual ambient isometry
between them, including when the realizations have a nontrivial kernel. -/
theorem exists_isometry_of_equal_norms (S A:E→ₗ[ℝ]V)
    (hnorm:∀x,‖S x‖=‖A x‖):
    ∃U:V→ₗᵢ[ℝ]V,∀x,U (S x)=A x:=by
  obtain ⟨R,hR⟩:=S.rangeRestrict.exists_rightInverse_of_surjective S.range_rangeRestrict
  have hSR (y:LinearMap.range S):S (R y)=(y:V):=by
    exact congrArg Subtype.val (LinearMap.congr_fun hR y)
  let L:LinearMap.range S→ₗᵢ[ℝ]V:=
    { toLinearMap:=A.comp R
      norm_map':=by
        intro y
        change ‖A (R y)‖=‖(y:V)‖
        rw [←hnorm,hSR] }
  refine ⟨L.extend,?_⟩
  intro x
  let sx:LinearMap.range S:=⟨S x,LinearMap.mem_range_self S x⟩
  have hzS:S (R sx-x)=0:=by rw [map_sub,hSR];exact sub_self _
  have hzA:A (R sx-x)=0:=by
    apply norm_eq_zero.mp
    rw [←hnorm,hzS,norm_zero]
  calc
    L.extend (S x)=L sx:=L.extend_apply sx
    _ = A x:=by
      change A (R sx)=A x
      exact sub_eq_zero.mp (by simpa only [map_sub] using hzA)
end IsometricExtension

/-- Actual zero-padding linear isometry between finite Gaussian coordinate
spaces; its only dimensional assumption is the required d≤ e. -/
def coordinateEmbedding (hde:d≤ e):FSC.Coord d→ₗᵢ[ℝ]FSC.Coord e where
  toFun x:=WithLp.toLp 2 (fun k:Fin e=>if hk:k.val<d then x ⟨k.val,hk⟩ else 0)
  map_add' x y:=by
    apply PiLp.ext
    intro k
    simp only [PiLp.add_apply]
    split_ifs <;>simp
  map_smul' c x:=by
    apply PiLp.ext
    intro k
    simp only [PiLp.smul_apply,smul_eq_mul,RingHom.id_apply]
    split_ifs <;>simp
  norm_map' x:=by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
    symm
    exact Fintype.sum_of_injective (Fin.castLE hde) (Fin.castLE_injective hde)
      (fun k:Fin d=>(x k)^2)
      (fun k:Fin e=>(if hk:k.val<d then x ⟨k.val,hk⟩ else 0)^2)
      (by
        intro k hk
        have hkd:¬k.val<d:=by
          intro h
          exact hk ⟨⟨k.val,h⟩,by ext;rfl⟩
        simp [hkd])
      (by intro k;simp [k.isLt])

/-- A PSD square root cannot move a vector farther from the identity than
its square does. No inverse or lower eigenvalue bound is used. -/
theorem psd_sqrt_pointwise_distance (S:FSC.Coord d→L[ℝ]FSC.Coord d)
    (hS:S∈psdCone) (x:FSC.Coord d):
    ‖S x-x‖≤‖S (S x)-x‖:=by
  let y:=S x-x
  have he:S (S x)-x=y+S y:=by dsimp [y];rw [map_sub];abel
  rw [he]
  change ‖y‖≤‖y+S y‖
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_add_sq_real]
  nlinarith [hS.2 y,sq_nonneg ‖S y‖]

theorem psd_sqrt_HilbertSchmidt_distance (S:FSC.Coord d→L[ℝ]FSC.Coord d)
    (hS:S∈psdCone):
    operatorHilbertSchmidt (S-ContinuousLinearMap.id ℝ (FSC.Coord d))≤
      operatorHilbertSchmidt (S.comp S-ContinuousLinearMap.id ℝ (FSC.Coord d)):=by
  apply (sq_le_sq₀ (operatorHilbertSchmidt_nonneg _) (operatorHilbertSchmidt_nonneg _)).mp
  rw [operatorHilbertSchmidt_sq,operatorHilbertSchmidt_sq]
  apply Finset.sum_le_sum
  intro j _
  exact pow_le_pow_left₀ (norm_nonneg _) (psd_sqrt_pointwise_distance S hS _) 2

/-- Actual rectangular polar factor, obtained by extending an isometry on the
image of a genuine PSD square root. Singular A is expressly allowed. -/
theorem exists_rectangular_polar_factor (A:FSC.Coord d→L[ℝ]FSC.Coord e) (hde:d≤ e):
    ∃S:FSC.Coord d→L[ℝ]FSC.Coord d,∃Q:FSC.Coord d→ₗᵢ[ℝ]FSC.Coord e,
      S∈psdCone ∧ S.comp S=A.adjoint.comp A ∧ ∀x,A x=Q (S x):=by
  have hC:A.adjoint.comp A∈psdCone:=by
    refine ⟨A.isSymmetric_adjoint_comp_self,?_⟩
    intro x
    change 0≤ inner ℝ x (A.adjoint (A x))
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact real_inner_self_nonneg
  obtain ⟨S,hS,hSq⟩:=exists_psd_factor (A.adjoint.comp A) hC
  let J:=coordinateEmbedding hde
  have hnorm:∀x,‖(J.toLinearMap.comp S.toLinearMap) x‖=‖A.toLinearMap x‖:=by
    intro x
    change ‖J (S x)‖=‖A x‖
    rw [J.norm_map]
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [←real_inner_self_eq_norm_sq,←real_inner_self_eq_norm_sq]
    calc
      inner ℝ (S x) (S x)=inner ℝ x (S (S x)):=hS.1 x (S x)
      _ = inner ℝ x (A.adjoint (A x)):=by
        exact congrArg (inner ℝ x) (congrArg (fun T:FSC.Coord d→L[ℝ]FSC.Coord d=>T x) hSq)
      _ = inner ℝ (A x) (A x):=ContinuousLinearMap.adjoint_inner_right A x (A x)
  obtain ⟨U,hU⟩:=exists_isometry_of_equal_norms (J.toLinearMap.comp S.toLinearMap) A.toLinearMap hnorm
  refine ⟨S,U.comp J,hS,hSq,?_⟩
  intro x
  exact (hU x).symm

theorem parseval_inner_square_sum (b:Fin m→FSC.Coord d)
    (hP:∀x,(∑i,inner ℝ (b i) x • b i)=x) (x:FSC.Coord d):
    (∑i,(inner ℝ (b i) x)^2)=‖x‖^2:=by
  calc
    _ = inner ℝ (∑i,inner ℝ (b i) x • b i) x:=by
      simp only [sum_inner,real_inner_smul_left,pow_two]
    _ = inner ℝ x x:=by rw [hP]
    _ = ‖x‖^2:=real_inner_self_eq_norm_sq x

theorem parseval_operator_HilbertSchmidt_sq [NeZero m] (b:Fin m→FSC.Coord d)
    (hP:∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (H:FSC.Coord d→L[ℝ]FSC.Coord d):
    (operatorHilbertSchmidt H)^2=∑i,‖H (b i)‖^2:=by
  by_cases hd:d=0
  · subst d
    have hz:∀x:FSC.Coord 0,H x=0:=fun x=>Subsingleton.elim _ _
    simp [operatorHilbertSchmidt_sq,hz]
  · letI:NeZero d:=⟨hd⟩
    calc
      _ = LinearMap.trace ℝ (FSC.Coord d) (H.adjoint.comp H).toLinearMap:=by
        rw [operatorHilbertSchmidt_sq]
        exact (parseval_square_trace (EuclideanSpace.basisFun (Fin d) ℝ)
          (fun x=>(EuclideanSpace.basisFun (Fin d) ℝ).sum_repr' x) H).symm
      _ = _:=parseval_square_trace b hP H

/-- The operator Hilbert--Schmidt defect is exactly the full score-Gram
Frobenius defect for a Parseval frame, with no dimension-dependent factor. -/
theorem scoreGram_HilbertSchmidt_sq [NeZero m] (b:Fin m→FSC.Coord d)
    (hP:∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (H:FSC.Coord d→L[ℝ]FSC.Coord d):
    (operatorHilbertSchmidt H)^2=∑i,∑j,(inner ℝ (b i) (H (b j)))^2:=by
  rw [Finset.sum_comm]
  simp_rw [parseval_inner_square_sum b hP]
  exact parseval_operator_HilbertSchmidt_sq b hP H

/-- Scaled regular rows are the actual physical regular-simplex orbit. -/
def ScaledRegularGram (n:ℕ) (R:Fin (n+2)→FSC.Coord e):Prop:=
  ∀i j,inner ℝ (R i) (R j)=(referenceScale n)^2*((if i=j then 1 else 0)-1/((n:ℝ)+2))

/-- A concrete regular reference within α times the normalized Gram defect.
The ambient dimension may exceed the minimal simplex dimension, and the input
row system may be singular. -/
theorem exists_regular_rows_with_distance_bound
    (b:AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG:∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP:∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hde:d≤ e) (B:Fin (n+2)→FSC.Coord e) (hB:(∑i,B i)=0):
    ∃R:Fin (n+2)→FSC.Coord e,ScaledRegularGram n R ∧
      (∑i,‖B i-R i‖^2)≤(referenceScale n)^2*
        (operatorHilbertSchmidt (normalizedRowCovariance n b B-
          ContinuousLinearMap.id ℝ (FSC.Coord d)))^2:=by
  let a:=referenceScale n
  let A:FSC.Coord d→L[ℝ]FSC.Coord e:=a⁻¹ • reconstruction b B
  have ha:a≠0:=ne_of_gt (referenceScale_pos n)
  have hG':∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ):=by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hG
  have hArow (i:Fin (n+2)):A (b i)=a⁻¹ • B i:=by
    change a⁻¹ • reconstruction b B (b i)=_
    rw [reconstruction_row b B hG' hB]
  have hAcov:A.adjoint.comp A=normalizedRowCovariance n b B:=by
    apply ContinuousLinearMap.ext
    intro x
    simp [A,normalizedRowCovariance,rowCovariance,a,map_smul,smul_smul,pow_two]
  obtain ⟨S,Q,hS,hSq,hAQ⟩:=exists_rectangular_polar_factor A hde
  let R:Fin (n+2)→FSC.Coord e:=fun i=>a • Q (b i)
  have hR:ScaledRegularGram n R:=by
    intro i j
    dsimp [R]
    rw [real_inner_smul_left,real_inner_smul_right,Q.inner_map_map,hG]
    dsimp [a]
    ring
  have hdist (i:Fin (n+2)):‖B i-R i‖^2=a^2*‖(S-ContinuousLinearMap.id ℝ (FSC.Coord d)) (b i)‖^2:=by
    have hb:B i=a • A (b i):=by rw [hArow,smul_smul,mul_inv_cancel₀ ha,one_smul]
    have he:B i-R i=a • Q (S (b i)-b i):=by
      rw [hb,hAQ]
      dsimp [R]
      rw [map_sub,smul_sub]
    rw [he,norm_smul,Q.norm_map,Real.norm_eq_abs,mul_pow,sq_abs]
    rfl
  refine ⟨R,hR,?_⟩
  simp_rw [hdist]
  rw [←Finset.mul_sum,←parseval_operator_HilbertSchmidt_sq b hP]
  have hh:=psd_sqrt_HilbertSchmidt_distance S hS
  rw [hSq,hAcov] at hh
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (operatorHilbertSchmidt_nonneg _) hh 2) (sq_nonneg a)

/-- Literal Euclidean distance to the full scaled regular orbit. -/
def regularOrbitDistance (n:ℕ) (B:Fin (n+2)→FSC.Coord e):ℝ:=
  sInf {r:ℝ|∃R:Fin (n+2)→FSC.Coord e,ScaledRegularGram n R ∧
    r=Real.sqrt (∑i,‖B i-R i‖^2)}

theorem regularOrbitDistance_nonneg_and_le
    (b:AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG:∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP:∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hde:d≤ e) (B:Fin (n+2)→FSC.Coord e) (hB:(∑i,B i)=0):
    0≤ regularOrbitDistance n B ∧ regularOrbitDistance n B≤ referenceScale n*
      operatorHilbertSchmidt (normalizedRowCovariance n b B-
        ContinuousLinearMap.id ℝ (FSC.Coord d)):=by
  obtain ⟨R,hR,henergy⟩:=exists_regular_rows_with_distance_bound b hG hP hde B hB
  let s:Set ℝ:={r|∃T:Fin (n+2)→FSC.Coord e,ScaledRegularGram n T ∧
    r=Real.sqrt (∑i,‖B i-T i‖^2)}
  have hs:s.Nonempty:=⟨_,R,hR,rfl⟩
  have hlow:∀x∈s,0≤ x:=by rintro x ⟨T,_,rfl⟩;exact Real.sqrt_nonneg _
  have hbdd:BddBelow s:=⟨0,hlow⟩
  constructor
  · exact le_csInf hs hlow
  · calc
      regularOrbitDistance n B≤ Real.sqrt (∑i,‖B i-R i‖^2):=
        csInf_le hbdd ⟨R,hR,rfl⟩
      _ ≤ Real.sqrt ((referenceScale n)^2*(operatorHilbertSchmidt
          (normalizedRowCovariance n b B-ContinuousLinearMap.id ℝ (FSC.Coord d)))^2):=
        Real.sqrt_le_sqrt henergy
      _ = _:=by
        rw [←mul_pow,Real.sqrt_sq (mul_nonneg (referenceScale_pos n).le
          (operatorHilbertSchmidt_nonneg _))]

theorem normalized_Gram_defect_identity
    (b:AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG:∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP:∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (B:Fin (n+2)→FSC.Coord e) (hB:(∑i,B i)=0):
    (operatorHilbertSchmidt (normalizedRowCovariance n b B-
      ContinuousLinearMap.id ℝ (FSC.Coord d)))^2=
    ∑i,∑j,(inner ℝ (B i) (B j)/(referenceScale n)^2-
      ((if i=j then 1 else 0)-1/((n:ℝ)+2)))^2:=by
  rw [scoreGram_HilbertSchmidt_sq b hP]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have hg:=congrFun (congrFun (rowCovariance_gram b hG B hB) i) j
  change inner ℝ (b i) (rowCovariance b B (b j))=inner ℝ (B i) (B j) at hg
  simp only [normalizedRowCovariance,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,inner_sub_right,
    real_inner_smul_right,hg,hG,div_eq_mul_inv]
  ring

def rayProfile (radius x:ℝ):ℝ:=x^2*min 1 (radius/x)

theorem rayProfile_eq_min (radius x:ℝ):rayProfile radius x=min (x^2) (radius*x):=by
  by_cases hx:x=0
  · simp [rayProfile,hx]
  · unfold rayProfile
    rw [mul_min_of_nonneg _ _ (sq_nonneg x),mul_one]
    congr 1
    field_simp

theorem rayProfile_mono {radius x y:ℝ} (hr:0≤ radius) (hx:0≤ x) (hxy:x≤ y):
    rayProfile radius x≤ rayProfile radius y:=by
  rw [rayProfile_eq_min,rayProfile_eq_min]
  exact min_le_min (pow_le_pow_left₀ hx hxy 2) (mul_le_mul_of_nonneg_left hxy hr)

/-- The global actual Gaussian deficit controls the literal distance to the
full rectangular regular orbit. Only the quantitative local curvature input
remains, exactly as in the preceding ray theorem. -/
theorem regularCovarianceDeficit_orbit_bound (hn:0<n)
    (b:AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG:∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP:∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (radius:ℝ) (hradius:0<radius)
    (hcurv:LocalGaussianCurvature b (uniformMass n) radius
      (referenceScale n/(12*((n:ℝ)+2))))
    (hde:d≤ e) (B:Fin (n+2)→FSC.Coord e) (hB:(∑i,B i)=0):
    let q:=regularOrbitDistance n B/referenceScale n
    (referenceScale n)^2*q^2/(48*((n:ℝ)+2))*min 1 (radius/q)≤
      regularCovarianceDeficit n B:=by
  let defect:=operatorHilbertSchmidt
    (normalizedRowCovariance n b B-ContinuousLinearMap.id ℝ (FSC.Coord d))
  let q:=regularOrbitDistance n B/referenceScale n
  have horbit:=regularOrbitDistance_nonneg_and_le b hG hP hde B hB
  have hq0:0≤ q:=div_nonneg horbit.1 (referenceScale_pos n).le
  have hqe:q≤ defect:=by
    apply (div_le_iff₀ (referenceScale_pos n)).mpr
    simpa only [mul_comm] using horbit.2
  have hprof:=rayProfile_mono hradius.le hq0 hqe
  have hmul:=mul_le_mul_of_nonneg_left hprof
    (show 0≤(referenceScale n)^2/(48*((n:ℝ)+2)) by positivity)
  have hr:=regularCovarianceDeficit_ray_bound_normalized hn b hG hP radius hradius hcurv B hB
  change (referenceScale n)^2*q^2/(48*((n:ℝ)+2))*min 1 (radius/q)≤_
  calc
    _ = (referenceScale n)^2/(48*((n:ℝ)+2))*rayProfile radius q:=by unfold rayProfile;ring
    _ ≤ (referenceScale n)^2/(48*((n:ℝ)+2))*rayProfile radius defect:=hmul
    _ = (referenceScale n)^2*defect^2/(48*((n:ℝ)+2))*min 1 (radius/defect):=by
      unfold rayProfile;ring
    _ ≤ regularCovarianceDeficit n B:=hr

end NegativeVotingProcrustes
