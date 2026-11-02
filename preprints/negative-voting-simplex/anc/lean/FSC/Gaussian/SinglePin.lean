import FSC.Gaussian.AffineLaw
import FSC.Gaussian.PinDefinitions

/-! Canonical one-coordinate Gaussian regression on the full original index set. The residual is an explicit linear image; all fixed real pin values use the frozen `singleLaw`, including singular and deterministic residuals. -/

noncomputable section

open MeasureTheory ProbabilityTheory Matrix
open scoped InnerProductSpace BigOperators ENNReal

namespace FSC

/-- Subtract the source covariance column times the selected coordinate. -/
def singleResidual {n : ℕ} (G : Mat n) (i : Fin n) : Mat n :=
  1 - Matrix.vecMulVec (fun k ↦ G k i) (Pi.single i 1)

@[simp] theorem lin_singleResidual_apply {n : ℕ} (G : Mat n) (i : Fin n)
    (x : Coord n) (k : Fin n) :
    lin (singleResidual G i) x k = x k - G k i * x i := by
  simp [lin_apply, singleResidual, Matrix.sub_mulVec, Matrix.vecMulVec_mulVec, mul_comm]

theorem singleResidual_mul_apply {n : ℕ} (G : Mat n) (i k l : Fin n) :
    (singleResidual G i * G) k l = G k l - G k i * G i l := by
  simp [singleResidual, Matrix.sub_mul, Matrix.vecMulVec_mul,
    Matrix.vecMulVec_apply, Matrix.row]

theorem singleResidual_covariance {n : ℕ} (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (i : Fin n) :
    singleResidual G i * G * (singleResidual G i).transpose = singleCov G i := by
  have hsym (k l : Fin n) : G k l = G l k := by
    simpa only [star_trivial] using hG.1.isHermitian.apply l k
  have htrans : (singleResidual G i).transpose =
      1 - Matrix.vecMulVec (Pi.single i 1) (fun k ↦ G k i) := by
    simp [singleResidual, Matrix.transpose_vecMulVec]
  rw [htrans, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_vecMulVec,
    Matrix.mulVec_single_one]
  ext k l
  change (singleResidual G i * G) k l - (singleResidual G i * G) k i * G l i = _
  rw [singleResidual_mul_apply, singleResidual_mul_apply, hG.2 i]
  simp [singleCov, hsym i l]

theorem singleCov_posSemidef {n : ℕ} (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (i : Fin n) : (singleCov G i).PosSemidef := by
  rw [← singleResidual_covariance G hG i]
  exact posSemidef_congruence G hG.1 (singleResidual G i)

/-- The selected residual coordinate is identically zero. -/
@[simp] theorem singleResidual_pinned {n : ℕ} (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (i : Fin n) (x : Coord n) :
    lin (singleResidual G i) x i = 0 := by
  rw [lin_singleResidual_apply, hG.2 i, one_mul, sub_self]

/-- The original vector is reconstructed at its actual selected coordinate. -/
theorem single_reconstruction {n : ℕ} (G : Mat n) (i : Fin n) (x : Coord n) :
    singleMean G i (x i) + lin (singleResidual G i) x = x := by
  ext k
  change singleMean G i (x i) k + lin (singleResidual G i) x k = x k
  rw [lin_singleResidual_apply]
  simp only [singleMean, WeakSimplex.Coord.ofFun_apply]
  ring

/-- The actual residual image has the frozen full-index covariance. -/
theorem map_singleResidual {n : ℕ} (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (i : Fin n) :
    Measure.map (lin (singleResidual G i)) (multivariateGaussian (0 : Coord n) G) =
      multivariateGaussian (0 : Coord n) (singleCov G i) := by
  simpa only [map_zero, singleResidual_covariance G hG i] using
    map_lin_multivariateGaussian (0 : Coord n) G hG.1 (singleResidual G i)

/-- Every real pin shifts that same residual law to the canonical one-pin law. -/
theorem map_singleMean_add {n : ℕ} (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (i : Fin n) (t : ℝ) :
    Measure.map (fun x ↦ singleMean G i t + x)
      (multivariateGaussian (0 : Coord n) (singleCov G i)) = singleLaw G i t := by
  have hone : (lin (1 : Mat n) : Coord n → Coord n) = id := by
    funext x
    ext k
    simp
  simpa only [hone, id_eq, add_zero, Matrix.one_mul, Matrix.transpose_one,
    Matrix.mul_one, singleLaw] using
    map_affine_multivariateGaussian (0 : Coord n) (singleCov G i)
      (singleCov_posSemidef G hG i) 1 (singleMean G i t)

/-- Every residual coordinate has zero covariance with the selected original coordinate. -/
theorem covariance_singleResidual_eval {n : ℕ} (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (i k : Fin n) :
    cov[fun x : Coord n ↦ lin (singleResidual G i) x k, fun x ↦ x i;
      multivariateGaussian (0 : Coord n) G] = 0 := by
  have hmem (j : Fin n) : MemLp (fun x : Coord n ↦ x j) 2
      (multivariateGaussian (0 : Coord n) G) := by
    exact IsGaussian.memLp_dual (multivariateGaussian (0 : Coord n) G)
      (EuclideanSpace.proj j) 2 (by simp)
  simp_rw [lin_singleResidual_apply]
  rw [covariance_fun_sub_left (hmem k) ((hmem i).const_mul (G k i)) (hmem i),
    covariance_const_mul_left, covariance_eval_multivariateGaussian hG.1,
    covariance_eval_multivariateGaussian hG.1, hG.2 i, mul_one, sub_self]

/-- Joint Gaussianity precedes the zero-covariance independence conclusion. -/
theorem singleResidual_indep_pin {n : ℕ} (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (i : Fin n) :
    IndepFun (lin (singleResidual G i)) (fun x : Coord n ↦ x i)
      (multivariateGaussian (0 : Coord n) G) := by
  have hjoint : HasGaussianLaw
      (fun x : Coord n ↦ (lin (singleResidual G i) x, x i))
      (multivariateGaussian (0 : Coord n) G) :=
    IsGaussian.hasGaussianLaw_id.map ((lin (singleResidual G i)).prod (EuclideanSpace.proj i))
  apply hjoint.indepFun_of_covariance_inner
  intro u v
  have hmemR (k : Fin n) : MemLp (fun x : Coord n ↦ lin (singleResidual G i) x k) 2
      (multivariateGaussian (0 : Coord n) G) :=
    IsGaussian.memLp_two_id.continuousLinearMap_comp
      ((EuclideanSpace.proj k).comp (lin (singleResidual G i)))
  have hmempin : MemLp (fun x : Coord n ↦ x i) 2
      (multivariateGaussian (0 : Coord n) G) := by
    exact IsGaussian.memLp_dual (multivariateGaussian (0 : Coord n) G)
      (EuclideanSpace.proj i) 2 (by simp)
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [covariance_mul_const_right,
    covariance_fun_sum_left (fun k ↦ (hmemR k).mul_const (u k)) hmempin]
  simp only [covariance_mul_const_left, covariance_singleResidual_eval G hG,
    zero_mul, Finset.sum_const_zero]

/-- Unit diagonal identifies the actual selected marginal as a standard real Gaussian. -/
theorem map_pin {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G) (i : Fin n) :
    Measure.map (fun x : Coord n ↦ x i) (multivariateGaussian (0 : Coord n) G) =
      gaussianReal 0 1 := by
  simpa [hG.2 i] using
    (measurePreserving_eval_multivariateGaussian (μ := (0 : Coord n)) hG.1 (i := i)).map_eq

/-- Exact residual/pin factorization on the full original residual index set. -/
theorem map_singleResidual_pin {n : ℕ} (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (i : Fin n) :
    Measure.map (fun x : Coord n ↦ (lin (singleResidual G i) x, x i))
      (multivariateGaussian (0 : Coord n) G) =
      (multivariateGaussian (0 : Coord n) (singleCov G i)).prod (gaussianReal 0 1) := by
  rw [(singleResidual_indep_pin G hG i).map_prod_eq_prod_map_map (by fun_prop) (by fun_prop),
    map_singleResidual G hG i, map_pin G hG i]

/-- The canonical law fixes the selected coordinate at every prescribed real pin. -/
theorem singleLaw_pin_ae {n : ℕ} (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (i : Fin n) (t : ℝ) :
    ∀ᵐ x ∂singleLaw G i t, x i = t := by
  rw [← map_singleMean_add G hG i t, ← map_singleResidual G hG i,
    Measure.map_map (measurable_const_add (singleMean G i t)) (lin (singleResidual G i)).measurable]
  apply (ae_map_iff (by fun_prop) (measurableSet_eq_fun (by fun_prop) measurable_const)).2
  apply Filter.Eventually.of_forall
  intro x
  change singleMean G i t i + lin (singleResidual G i) x i = t
  rw [singleResidual_pinned G hG i x]
  simp [singleMean, hG.2 i]

/-- Fubini for the canonical pin, with an arbitrary measurable test of both vector and pin. -/
theorem lintegral_singlePin {n : ℕ} (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (i : Fin n)
    (f : Coord n × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x : Coord n, f (x, x i) ∂multivariateGaussian (0 : Coord n) G) =
      ∫⁻ t : ℝ, ∫⁻ y : Coord n, f (y, t) ∂singleLaw G i t ∂gaussianReal 0 1 := by
  let H : Coord n × ℝ → ℝ≥0∞ := fun p ↦ f (singleMean G i p.2 + p.1, p.2)
  have hH : Measurable H := by
    apply hf.comp
    dsimp [singleMean, WeakSimplex.Coord.ofFun]
    fun_prop
  calc
    (∫⁻ x : Coord n, f (x, x i) ∂multivariateGaussian (0 : Coord n) G) =
        ∫⁻ x : Coord n, H (lin (singleResidual G i) x, x i)
          ∂multivariateGaussian (0 : Coord n) G := by
      apply lintegral_congr
      intro x
      simp only [H, single_reconstruction]
    _ = ∫⁻ p, H p ∂Measure.map
        (fun x : Coord n ↦ (lin (singleResidual G i) x, x i))
        (multivariateGaussian (0 : Coord n) G) := (lintegral_map hH (by fun_prop)).symm
    _ = ∫⁻ p, H p ∂(multivariateGaussian (0 : Coord n) (singleCov G i)).prod
        (gaussianReal 0 1) := by rw [map_singleResidual_pin G hG i]
    _ = ∫⁻ t : ℝ, ∫⁻ r : Coord n, f (singleMean G i t + r, t)
        ∂multivariateGaussian (0 : Coord n) (singleCov G i) ∂gaussianReal 0 1 :=
      lintegral_prod_symm' H hH
    _ = ∫⁻ t : ℝ, ∫⁻ y : Coord n, f (y, t) ∂singleLaw G i t ∂gaussianReal 0 1 := by
      apply lintegral_congr
      intro t
      rw [← map_singleMean_add G hG i t]
      have hft : Measurable (fun y : Coord n ↦ f (y, t)) :=
        hf.comp (measurable_id.prodMk measurable_const)
      exact (lintegral_map hft (measurable_const_add (singleMean G i t))).symm

/-- Every measurable event is integrated against the explicit fixed-pin Gaussian laws. -/
theorem measure_singlePin {n : ℕ} (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (i : Fin n)
    (s : Set (Coord n)) (hs : MeasurableSet s) :
    multivariateGaussian (0 : Coord n) G s =
      ∫⁻ t : ℝ, singleLaw G i t s ∂gaussianReal 0 1 := by
  have h := lintegral_singlePin G hG i
    (fun p ↦ s.indicator (1 : Coord n → ℝ≥0∞) p.1)
    ((measurable_const.indicator hs).comp measurable_fst)
  simpa only [lintegral_indicator_one hs] using h

end FSC
