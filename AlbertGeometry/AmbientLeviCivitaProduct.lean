/-
The ambient affine connection is raised from the
literal derivative of the actual varying metric -D²logN/3. Its Koszul,
torsion, metric and uniqueness laws are proved before comparison with the
independently derivative-defined intrinsic product. No Jordan, invariance,
recognition, trace-of-multiplication or prescribed connection field is input.
This is the AMBIENT affine coefficient; the level-chart coefficient is -K.
-/
module

public import AlbertGeometry.BasedNormAdjointTransport
public import AlbertGeometry.LogHessianPositiveNeighborhood
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section
namespace AlbertGeometry.AmbientLeviCivitaProduct
noncomputable section
open AlbertGeometry.Cubic
open AlbertGeometry.BasedNormDerivativeTransport
open AlbertGeometry.BasedNormDerivativeTransport.BasedNormIso
open AlbertGeometry.BasedNormAdjointTransport
open scoped ContDiff Topology
open Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Exactly the canonical operator norms; no new norm on native Albert or V.
local instance ambientDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := E) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
local instance ambientDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := E) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
local instance ambientBilinearNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := E) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance ambientBilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := E) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance ambientTrilinearNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := E) (F := E →L[ℝ] E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance ambientTrilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := E) (F := E →L[ℝ] E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance ambientEndNorm : NormedAddCommGroup (E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := E) (F := E) (σ₁₂ := RingHom.id ℝ)
local instance ambientEndSpace : NormedSpace ℝ (E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := E) (F := E) (σ₁₂ := RingHom.id ℝ)
local instance ambientVectorBilinearNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := E) (F := E →L[ℝ] E) (σ₁₂ := RingHom.id ℝ)
local instance ambientVectorBilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := E) (F := E →L[ℝ] E) (σ₁₂ := RingHom.id ℝ)
local instance ambientInverseNorm : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := E →L[ℝ] ℝ) (F := E) (σ₁₂ := RingHom.id ℝ)
local instance ambientInverseSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := E →L[ℝ] ℝ) (F := E) (σ₁₂ := RingHom.id ℝ)

private theorem eval_const_hasFDerivAt
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : X → Y →L[ℝ] Z} {f' : X →L[ℝ] Y →L[ℝ] Z} {x : X}
    (hf : HasFDerivAt f f' x) (u : Y) :
    HasFDerivAt (fun y => f y u) (f'.flip u) x := by
  have h := hf.clm_apply (hasFDerivAt_const u x)
  apply h.congr_fderiv
  ext w
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply, map_zero, zero_add]

/-- Smoothness is proved for the literal log and then its literal derivatives. -/
theorem contDiffAt_actual_log (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) : ContDiffAt ℝ ⊤ (logCubic P) x :=
  (contDiff_diagonalCubic P.form ⊤).contDiffAt.log (ne_of_gt hx)

theorem contDiffAt_actual_logHessian (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) : ContDiffAt ℝ ⊤ (logHessian P) x := by
  have hd : ContDiffAt ℝ ⊤ (fderiv ℝ (logCubic P)) x :=
    (contDiffAt_actual_log P hx).fderiv_right (by simp)
  exact hd.fderiv_right (by simp)

theorem contDiffAt_actual_metric (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) : ContDiffAt ℝ ⊤ (logHessianForm P) x :=
  (contDiffAt_actual_logHessian P hx).const_smul (-1 / 3 : ℝ)

/-- The derivative of the actual varying ambient metric, never a stored jet. -/
def ambientMetricD1 (P : SymmetricTrilinearForm E) (x : E) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ := fderiv ℝ (logHessianForm P) x

theorem hasFDerivAt_actual_metric (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) :
    HasFDerivAt (logHessianForm P) (ambientMetricD1 P x) x :=
  ((contDiffAt_actual_metric P hx).differentiableAt (by simp)).hasFDerivAt

/-- Third-derivative Schwarz symmetry swaps the first two metric-jet slots. -/
theorem ambientMetricD1_swap12 (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) (u v w : E) :
    ambientMetricD1 P x u v w = ambientMetricD1 P x v u w := by
  have hd : ContDiffAt ℝ ⊤ (fderiv ℝ (logCubic P)) x :=
    (contDiffAt_actual_log P hx).fderiv_right (by simp)
  have hh := ((contDiffAt_actual_logHessian P hx).differentiableAt
    (by simp)).hasFDerivAt.const_smul (-1 / 3 : ℝ)
  have hs := congrArg (fun L : E →L[ℝ] ℝ => L w)
    ((hd.isSymmSndFDerivAt le_top).eq u v)
  change fderiv ℝ (logHessianForm P) x u v w =
    fderiv ℝ (logHessianForm P) x v u w
  have hmetric : fderiv ℝ (logHessianForm P) x =
      (-1 / 3 : ℝ) • fderiv ℝ (logHessian P) x := hh.fderiv
  rw [hmetric]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  exact congrArg (fun r : ℝ => (-1 / 3 : ℝ) * r) hs

/-- Symmetry is differentiated on an actual positive neighborhood. -/
theorem ambientMetricD1_swap23 (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) (u v w : E) :
    ambientMetricD1 P x u v w = ambientMetricD1 P x u w v := by
  have hG := hasFDerivAt_actual_metric P hx
  have h1 := eval_const_hasFDerivAt (eval_const_hasFDerivAt hG v) w
  have h2 := eval_const_hasFDerivAt (eval_const_hasFDerivAt hG w) v
  have hc : (fun y => logHessianForm P y v w) =ᶠ[𝓝 x]
      (fun y => logHessianForm P y w v) :=
    (eventually_positive P hx).mono (fun y hy => logHessianForm_symm P hy v w)
  have h := congrArg (fun L : E →L[ℝ] ℝ => L u)
    (h1.unique (h2.congr_of_eventuallyEq hc))
  simpa only [ContinuousLinearMap.flip_apply] using h

/-- Actual affine-coordinate Koszul tensor, built from the literal metric jet. -/
def ambientKoszulTensor (P : SymmetricTrilinearForm E) (x : E) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (ambientMetricD1 P x + (ambientMetricD1 P x).flip -
    ((((ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv).toContinuousLinearMap :
      (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ).comp
      (ambientMetricD1 P x).flip))

theorem ambientKoszulTensor_apply (P : SymmetricTrilinearForm E) (x u v w : E) :
    ambientKoszulTensor P x u v w =
      (ambientMetricD1 P x u v w + ambientMetricD1 P x v u w -
        ambientMetricD1 P x w u v) / 2 := by
  have hflip :
      ((((ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv).toContinuousLinearMap :
        (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ).comp
        (ambientMetricD1 P x).flip) u v w = ambientMetricD1 P x w u v := rfl
  simp only [ambientKoszulTensor, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
  rw [hflip]
  simp only [ContinuousLinearMap.flip_apply, smul_eq_mul]
  ring

theorem ambientKoszulTensor_eq_half (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) :
    ambientKoszulTensor P x = (1 / 2 : ℝ) • ambientMetricD1 P x := by
  ext u v w
  rw [ambientKoszulTensor_apply, ambientMetricD1_swap12 P hx v u w,
    ambientMetricD1_swap12 P hx w u v, ambientMetricD1_swap23 P hx u w v]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- Raise the actual Koszul covector by the actual metric inverse. The total
inverse may be zero off the invertible locus; all laws below prove invertibility. -/
def ambientGamma (P : SymmetricTrilinearForm E) (x : E) : E →L[ℝ] E →L[ℝ] E :=
  ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E)
    (logHessianForm P x).inverse).comp (ambientKoszulTensor P x)

theorem ambientGamma_apply (P : SymmetricTrilinearForm E) (x u v : E) :
    ambientGamma P x u v = (logHessianForm P x).inverse
      (ambientKoszulTensor P x u v) := by
  simp only [ambientGamma, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply]

section FiniteDimension
variable [FiniteDimensional ℝ E]

theorem actual_metric_dual_injective (P : SymmetricTrilinearForm E) (x : E)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) :
    Function.Injective (logHessianForm P x) := by
  intro u v huv
  have hzero : logHessianForm P x (u - v) = 0 := by rw [map_sub, huv, sub_self]
  have hzero' : logHessianForm P x (u - v) (u - v) = 0 := by rw [hzero]; rfl
  have hz : u - v = 0 := by
    by_contra hne
    have h := hp (u - v) hne
    rw [hzero'] at h
    exact (lt_irrefl 0) h
  exact sub_eq_zero.mp hz

theorem actual_metric_dual_isInvertible (P : SymmetricTrilinearForm E) (x : E)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) :
    (logHessianForm P x).IsInvertible := by
  let d : Module.Dual ℝ E ≃ₗ[ℝ] (E →L[ℝ] ℝ) := LinearMap.toContinuousLinearMap
  letI : FiniteDimensional ℝ (E →L[ℝ] ℝ) := d.finiteDimensional
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) :=
    (Subspace.dual_finrank_eq (K := ℝ) (V := E)).symm.trans d.finrank_eq
  let A : E ≃L[ℝ] (E →L[ℝ] ℝ) :=
    (LinearEquiv.ofInjectiveOfFinrankEq (logHessianForm P x).toLinearMap
      (actual_metric_dual_injective P x hp) hdim).toContinuousLinearEquiv
  exact ⟨A, rfl⟩

/-- Actual affine Koszul identity at every positive metric point. -/
theorem ambientGamma_koszul (P : SymmetricTrilinearForm E) (x : E)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) (u v w : E) :
    logHessianForm P x (ambientGamma P x u v) w = ambientKoszulTensor P x u v w := by
  rw [ambientGamma_apply]
  exact congrArg (fun L : E →L[ℝ] ℝ => L w)
    ((actual_metric_dual_isInvertible P x hp).self_apply_inverse
      (ambientKoszulTensor P x u v))

theorem ambientGamma_symm (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) (u v : E) :
    ambientGamma P x u v = ambientGamma P x v u := by
  apply actual_metric_dual_injective P x hp
  ext w
  rw [ambientGamma_koszul P x hp, ambientGamma_koszul P x hp]
  simp only [ambientKoszulTensor_eq_half P hx,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [ambientMetricD1_swap12 P hx]

theorem ambientGamma_metricCompatibility (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) (u v w : E) :
    ambientMetricD1 P x u v w =
      logHessianForm P x (ambientGamma P x u v) w +
        logHessianForm P x v (ambientGamma P x u w) := by
  rw [logHessianForm_symm P hx v (ambientGamma P x u w),
    ambientGamma_koszul P x hp, ambientGamma_koszul P x hp]
  simp only [ambientKoszulTensor_eq_half P hx,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [ambientMetricD1_swap23 P hx u w v]
  ring

/-- These are competitor laws used to PROVE uniqueness; no such fields enter
the definition of our actual connection. -/
theorem ambientGamma_unique (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) (H : E → E → E)
    (hTor : ∀ u v, H u v = H v u)
    (hMet : ∀ u v w, ambientMetricD1 P x u v w =
      logHessianForm P x (H u v) w + logHessianForm P x v (H u w)) :
    ∀ u v, H u v = ambientGamma P x u v := by
  intro u v
  apply actual_metric_dual_injective P x hp
  ext w
  rw [ambientGamma_koszul P x hp, ambientKoszulTensor_apply]
  have h1 := hMet u v w
  have h2 := hMet v u w
  have h3 := hMet w u v
  rw [logHessianForm_symm P hx v (H u w)] at h1
  rw [hTor v u, logHessianForm_symm P hx u (H v w)] at h2
  rw [hTor w u, hTor w v, logHessianForm_symm P hx u (H v w)] at h3
  linarith

/-- Actual adjoint polarization gives the cross pairing before Jordan laws. -/
theorem intrinsicCross_pairing (P : SymmetricTrilinearForm E) (e : E)
    (hB : (rawBilinearForm P e).Nondegenerate) (u v w : E) :
    rawTraceForm P e (intrinsicCross P e hB u v) w = 6 * P.form ![u,v,w] := by
  simp only [intrinsicCross, map_sub, ContinuousLinearMap.sub_apply,
    intrinsicAdjoint_pairing, fderiv_diagonalCubic_apply_symmetric]
  have hadd : P.form ![u + v,u + v,w] = P.form ![u,u,w] +
      P.form ![u,v,w] + P.form ![v,u,w] + P.form ![v,v,w] := by
    simp only [← fullyCurried_apply, map_add, ContinuousLinearMap.add_apply]
    ring
  rw [hadd, P.swap12 v u w]
  ring

theorem rawTraceForm_unit_left (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) (w : E) :
    rawTraceForm P e e w = normTrace P e w := by
  rw [rawTraceForm_eq_three_logMetric P e he, logHessianForm_radial_at_one P e w he]
  unfold normTrace
  ring

/-- Exact full-slot product pairing, with rawB=3g and unhalved cross. -/
theorem intrinsicProduct_pairing (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) (hB : (rawBilinearForm P e).Nondegenerate)
    (u v w : E) :
    rawTraceForm P e (intrinsicProduct P e hB u v) w =
      3 * P.form ![u,v,w] + (normTrace P e u * rawTraceForm P e v w +
        normTrace P e v * rawTraceForm P e u w - intrinsicS P e u v * normTrace P e w) / 2 := by
  simp only [intrinsicProduct, map_smul, map_add, map_sub,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, smul_eq_mul, intrinsicCross_pairing,
    rawTraceForm_unit_left P e he]
  ring

/-- Differentiate the proved rational metric identity on its positive
neighborhood. The scalar derivatives and whole CLM derivative agree by uniqueness. -/
theorem ambientMetricD1_at_one (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) (u v w : E) :
    ambientMetricD1 P e u v w = (-1 / 3 : ℝ) *
      (6 * P.form ![u,v,w] - normTrace P e u * cubicHessian P e v w -
        cubicHessian P e u v * normTrace P e w -
        normTrace P e v * cubicHessian P e u w +
        2 * normTrace P e u * normTrace P e v * normTrace P e w) := by
  have hN : 0 < diagonalCubic P.form e := by rw [he]; norm_num
  have hG := eval_const_hasFDerivAt
    (eval_const_hasFDerivAt (hasFDerivAt_actual_metric P hN) v) w
  have hH := eval_const_hasFDerivAt
    (eval_const_hasFDerivAt (hasFDerivAt_cubicHessian P e) v) w
  have hV := eval_const_hasFDerivAt (hasFDerivAt_fderiv_diagonalCubic_actual P e) v
  have hW := eval_const_hasFDerivAt (hasFDerivAt_fderiv_diagonalCubic_actual P e) w
  have hR := hasFDerivAt_inverseCubic P hN
  have hs := ((hH.mul hR).const_smul (-1 / 3 : ℝ)).add
    ((((hV.mul hW).mul hR).mul hR).const_smul (1 / 3 : ℝ))
  have hc : (fun y => logHessianForm P y v w) =ᶠ[𝓝 e]
      (fun y => (-1 / 3 : ℝ) * (cubicHessian P y v w *
        (diagonalCubic P.form y)⁻¹) + (1 / 3 : ℝ) *
          (fderiv ℝ (diagonalCubic P.form) y v *
            fderiv ℝ (diagonalCubic P.form) y w *
              (diagonalCubic P.form y)⁻¹ * (diagonalCubic P.form y)⁻¹)) :=
    (eventually_positive P hN).mono (fun y hy => by
      change logHessianForm P y v w = _
      rw [logHessianForm_apply P hy]
      simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
      ring)
  have hd := congrArg (fun L : E →L[ℝ] ℝ => L u)
    (hG.unique (hs.congr_of_eventuallyEq hc))
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, inverseCubicDerivative, fullyCurried_apply,
    smul_eq_mul, Pi.mul_apply, he, one_pow, inv_one, normTrace] at hd ⊢
  rw [hd]
  ring

/-- The metric cubic jet is DERIVED from actual DN/D2N/D3N, then compared
with the independently reconstructed product. All radial slots are retained. -/
theorem ambientMetricD1_eq_neg_two_product (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) (hB : (rawBilinearForm P e).Nondegenerate)
    (u v w : E) :
    ambientMetricD1 P e u v w =
      -2 * logHessianForm P e (intrinsicProduct P e hB u v) w := by
  have hg := rawTraceForm_eq_three_logMetric P e he (intrinsicProduct P e hB u v) w
  rw [intrinsicProduct_pairing P e he hB] at hg
  simp only [intrinsicS, rawTraceForm_apply] at hg
  rw [ambientMetricD1_at_one P e he]
  nlinarith only [hg]

/-- Actual AMBIENT affine Levi-Civita coefficient at the normalized base.
The product has its real positive-derived nondegeneracy certificate. -/
theorem ambientGamma_at_one_eq_neg_product (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u) (u v : E) :
    ambientGamma P e u v =
      -intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) u v := by
  have hN : 0 < diagonalCubic P.form e := by rw [he]; norm_num
  apply actual_metric_dual_injective P e hp
  ext w
  rw [ambientGamma_koszul P e hp, ambientKoszulTensor_eq_half P hN]
  simp only [ContinuousLinearMap.smul_apply, map_neg,
    ContinuousLinearMap.neg_apply, smul_eq_mul]
  rw [ambientMetricD1_eq_neg_two_product P e he
    (rawBilinearForm_nondegenerate P e he hp)]
  ring

end FiniteDimension

section SmoothConnection
variable [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Genuine smooth connection field on the actual positive-definite locus;
point invertibility and the literal metric derivatives supply its smoothness. -/
theorem contDiffAt_ambientGamma (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) :
    ContDiffAt ℝ ⊤ (ambientGamma P) x := by
  have hG := contDiffAt_actual_metric P hx
  have hi : ContDiffAt ℝ ⊤ (fun y => (logHessianForm P y).inverse) x :=
    (ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse
      (𝕜 := ℝ) (E := E) (F := E →L[ℝ] ℝ) (n := ⊤)
      (actual_metric_dual_isInvertible P x hp)).fun_comp x hG
  have hDG : ContDiffAt ℝ ⊤ (ambientMetricD1 P) x := hG.fderiv_right (by simp)
  have hK : ContDiffAt ℝ ⊤ (ambientKoszulTensor P) x :=
    (hDG.const_smul (1 / 2 : ℝ)).congr_of_eventuallyEq
      ((eventually_positive P hx).mono (fun y hy => ambientKoszulTensor_eq_half P hy))
  have hleft : ContDiffAt ℝ ⊤
      (fun y => ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E
        (logHessianForm P y).inverse) x :=
    (ContinuousLinearMap.contDiff (𝕜 := ℝ)
      (E := (E →L[ℝ] ℝ) →L[ℝ] E)
      (F := (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E) (n := ⊤)
      (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E)).contDiffAt.fun_comp x hi
  exact hleft.clm_comp hK

/-- Base positivity constructs an OPEN neighborhood where the above smooth,
torsion-free, metric-compatible connection and its uniqueness laws all apply. -/
theorem exists_actual_ambient_connection_domain (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u) :
    ∃ U : Set E, IsOpen U ∧ e ∈ U ∧ ∀ x ∈ U,
      0 < diagonalCubic P.form x ∧
      (∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) ∧
      ContDiffAt ℝ ⊤ (ambientGamma P) x ∧
      (∀ u v, ambientGamma P x u v = ambientGamma P x v u) ∧
      (∀ u v w, ambientMetricD1 P x u v w =
        logHessianForm P x (ambientGamma P x u v) w +
          logHessianForm P x v (ambientGamma P x u w)) := by
  have hN : 0 < diagonalCubic P.form e := by rw [he]; norm_num
  obtain ⟨U, hU, heU, hgood⟩ :=
    exists_positive_definite_logHessian_neighborhood P e hN hp
  refine ⟨U, hU, heU, fun x hx => ?_⟩
  have hn := (hgood x hx).1
  have hpx := (hgood x hx).2.2
  exact ⟨hn, hpx, contDiffAt_ambientGamma P hn hpx,
    ambientGamma_symm P hn hpx, ambientGamma_metricCompatibility P hn hpx⟩

end SmoothConnection

section BasedTransport
variable [FiniteDimensional ℝ E]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
variable {P : SymmetricTrilinearForm E} {e : E}
  {Q : SymmetricTrilinearForm G} {f : G}

/-- Full actual metric-jet transport is derived by differentiating varying
metric naturality on a positive neighborhood, with actual derivative certificates. -/
theorem ambientMetricD1_pull (I : BasedNormIso P e Q f) (x : E)
    (hx : 0 < diagonalCubic P.form x) (s u v : E) :
    ambientMetricD1 P x s u v =
      ambientMetricD1 Q (I.equiv x) (I.equiv s) (I.equiv u) (I.equiv v) := by
  have hy : 0 < diagonalCubic Q.form (I.equiv x) := by rw [I.map_norm]; exact hx
  have hP := eval_const_hasFDerivAt
    (eval_const_hasFDerivAt (hasFDerivAt_actual_metric P hx) u) v
  have hQ := (eval_const_hasFDerivAt
    (eval_const_hasFDerivAt (hasFDerivAt_actual_metric Q hy) (I.equiv u))
      (I.equiv v)).comp x I.equiv.toContinuousLinearMap.hasFDerivAt
  have hc : (fun y => logHessianForm P y u v) =ᶠ[𝓝 x]
      (fun y => logHessianForm Q (I.equiv y) (I.equiv u) (I.equiv v)) :=
    (eventually_positive P hx).mono (fun y hny => I.logHessianForm_pull y hny u v)
  have h := congrArg (fun L : E →L[ℝ] ℝ => L s)
    (hP.unique (hQ.congr_of_eventuallyEq hc))
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearEquiv.coe_coe] using h

/-- Target positivity is an OUTPUT of the actual inverse map at each point. -/
theorem actual_metric_positive_target (I : BasedNormIso P e Q f) (x : E)
    (hx : 0 < diagonalCubic P.form x)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) :
    ∀ v : G, v ≠ 0 → 0 < logHessianForm Q (I.equiv x) v v := by
  intro v hv
  have hu : I.equiv.symm v ≠ 0 := by
    intro hz
    apply hv
    simpa only [ContinuousLinearEquiv.apply_symm_apply, map_zero] using
      congrArg I.equiv hz
  have hg : logHessianForm P x (I.equiv.symm v) (I.equiv.symm v) =
      logHessianForm Q (I.equiv x) v v := by
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using
      I.logHessianForm_pull x hx (I.equiv.symm v) (I.equiv.symm v)
  rw [← hg]
  exact hp (I.equiv.symm v) hu

/-- Actual affine connection-field naturality at EVERY positive metric point,
not merely equality of stored base coefficients. No target positivity field
or metric/connection-preservation premise is supplied. -/
theorem ambientGamma_pull (I : BasedNormIso P e Q f) (x : E)
    (hx : 0 < diagonalCubic P.form x)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) (u v : E) :
    I.equiv (ambientGamma P x u v) =
      ambientGamma Q (I.equiv x) (I.equiv u) (I.equiv v) := by
  let hq := actual_metric_positive_target I x hx hp
  apply actual_metric_dual_injective Q (I.equiv x) hq
  ext z
  obtain ⟨w, rfl⟩ := I.equiv.surjective z
  rw [← I.logHessianForm_pull x hx (ambientGamma P x u v) w,
    ambientGamma_koszul P x hp, ambientGamma_koszul Q (I.equiv x) hq,
    ambientKoszulTensor_apply, ambientKoszulTensor_apply,
    ← ambientMetricD1_pull I x hx u v w,
    ← ambientMetricD1_pull I x hx v u w,
    ← ambientMetricD1_pull I x hx w u v]

/-- For two positive normalized based cubics, the ambient base connection
transports under norm/unit alone. Product covariance is the generic
derivative theorem; no connection/product preservation field is supplied. -/
theorem ambientGamma_at_one_pull (I : BasedNormIso P e Q f)
    (he : diagonalCubic P.form e = 1) (hf : diagonalCubic Q.form f = 1)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u)
    (hq : ∀ v : G, v ≠ 0 → 0 < logHessianForm Q f v v) (u v : E) :
    I.equiv (ambientGamma P e u v) = ambientGamma Q f (I.equiv u) (I.equiv v) := by
  rw [ambientGamma_at_one_eq_neg_product P e he hp,
    ambientGamma_at_one_eq_neg_product Q f hf hq, map_neg,
    intrinsicProduct_pull I (rawBilinearForm_nondegenerate P e he hp)
      (rawBilinearForm_nondegenerate Q f hf hq)]

end BasedTransport
end
end AlbertGeometry.AmbientLeviCivitaProduct
