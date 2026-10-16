/-
The jets below are literal nested Frechet
 derivatives of the original inverse-theorem level chart. All differentiated
 identities hold on the same fixed open smooth domain before differentiation.
No jet, metric positivity, curvature or arbitrary-polynomial representation
 conclusion is assumed. The metric used in the second jet is ambient -D²logN/3.
-/
module

public import AlbertGeometry.RegularLevelChartSmooth
public import AlbertGeometry.CubicThirdDerivative
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

@[expose] public section
open scoped ContDiff Topology
open Filter

namespace AlbertGeometry.Cubic
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- First actual Frechet derivative of the original level chart. -/
def levelChartD1 (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) (x : tangentSpace P e) :
    tangentSpace P e →L[ℝ] E := fderiv ℝ (levelChartPoint P e he) x

/-- Second actual derivative: differentiate the actual first-derivative field. -/
def levelChartD2 (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) (x : tangentSpace P e) :
    tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ] E :=
  fderiv ℝ (levelChartD1 P e he) x

/-- Third actual derivative: differentiate the actual second-derivative field. -/
def levelChartD3 (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) (x : tangentSpace P e) :
    tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ] E :=
  fderiv ℝ (levelChartD2 P e he) x

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

private theorem derivative_zero_of_eventually_constant
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} {f' : X →L[ℝ] Y} {x : X} {c : Y}
    (hf : HasFDerivAt f f' x) (hc : ∀ᶠ y in 𝓝 x, f y = c) (u : X) :
    f' u = 0 := by
  have h := hf.unique ((hasFDerivAt_const c x).congr_of_eventuallyEq hc)
  simpa only [ContinuousLinearMap.zero_apply] using congrArg (fun L => L u) h

variable (P : SymmetricTrilinearForm E) (e : E) (he : diagonalCubic P.form e = 1)
local notation "W" => tangentSpace P e
local notation "χ" => levelChartPoint P e he
local notation "Dχ" => levelChartD1 P e he
local notation "DDχ" => levelChartD2 P e he
local notation "DDDχ" => levelChartD3 P e he
local notation "π" => tangentProjection P e he
local notation "U" => smoothLevelChartDomain P e he
local notation "DN" => fderiv ℝ (diagonalCubic P.form)

/-- The certificates are obtained from actual smoothness at every x in U. -/
theorem hasFDerivAt_levelChartD0 (x : W) (hx : x ∈ U) :
    HasFDerivAt χ (Dχ x) x :=
  ((contDiffAt_levelChartPoint_smoothDomain P e he ⊤ x hx).differentiableAt
    (by simp)).hasFDerivAt

theorem contDiffAt_levelChartD1 (x : W) (hx : x ∈ U) : ContDiffAt ℝ ⊤ Dχ x := by
  change ContDiffAt ℝ ⊤ (fderiv ℝ (levelChartPoint P e he)) x
  exact ContDiffAt.fderiv_right (𝕜 := ℝ) (E := W) (F := E)
    (f := levelChartPoint P e he) (x₀ := x) (m := ⊤) (n := ⊤)
    (contDiffAt_levelChartPoint_smoothDomain P e he ⊤ x hx) (by simp)

theorem hasFDerivAt_levelChartD1 (x : W) (hx : x ∈ U) :
    HasFDerivAt Dχ (DDχ x) x :=
  ((contDiffAt_levelChartD1 P e he x hx).differentiableAt (by simp)).hasFDerivAt

section CanonicalLevelChartNorms

local instance levelChartLinearNormedAddCommGroup : NormedAddCommGroup (W →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := W) (F := E) (σ₁₂ := RingHom.id ℝ)

local instance levelChartLinearNormedSpace : NormedSpace ℝ (W →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := W) (F := E) (σ₁₂ := RingHom.id ℝ)

local instance levelChartBilinearNormedAddCommGroup :
    NormedAddCommGroup (W →L[ℝ] W →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := W) (F := W →L[ℝ] E) (σ₁₂ := RingHom.id ℝ)

local instance levelChartBilinearNormedSpace : NormedSpace ℝ (W →L[ℝ] W →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := W) (F := W →L[ℝ] E) (σ₁₂ := RingHom.id ℝ)

theorem contDiffAt_levelChartD2 (x : W) (hx : x ∈ U) : ContDiffAt ℝ ⊤ DDχ x := by
  change ContDiffAt ℝ ⊤ (fderiv ℝ (levelChartD1 P e he)) x
  exact ContDiffAt.fderiv_right (𝕜 := ℝ) (E := W) (F := W →L[ℝ] E)
    (f := levelChartD1 P e he) (x₀ := x) (m := ⊤) (n := ⊤)
    (contDiffAt_levelChartD1 P e he x hx) (by simp)

theorem hasFDerivAt_levelChartD2 (x : W) (hx : x ∈ U) :
    HasFDerivAt DDχ (DDDχ x) x :=
  ((contDiffAt_levelChartD2 P e he x hx).differentiableAt (by simp)).hasFDerivAt

/-- Actual neighborhood projection identity, obtained before differentiating. -/
theorem eventually_levelChart_projection (x : W) (hx : x ∈ U) :
    ∀ᶠ y in 𝓝 x, π (χ y) = y :=
  Filter.mem_of_superset ((isOpen_smoothLevelChartDomain P e he).mem_nhds hx)
    (fun y hy => levelChartPoint_projection P e he y
      (smoothLevelChartDomain_subset P e he hy))

/-- Actual neighborhood level identity, obtained before differentiating. -/
theorem eventually_levelChart_norm (x : W) (hx : x ∈ U) :
    ∀ᶠ y in 𝓝 x, diagonalCubic P.form (χ y) = 1 :=
  Filter.mem_of_superset ((isOpen_smoothLevelChartDomain P e he).mem_nhds hx)
    (fun y hy => levelChartPoint_on_level P e he y
      (smoothLevelChartDomain_subset P e he hy))

/-- The first projection identity holds throughout U, not only at zero. -/
theorem levelChartD1_projection (x : W) (hx : x ∈ U) (u : W) :
    π (Dχ x u) = u := by
  have hd := HasFDerivAt.comp (𝕜 := ℝ) (E := W) (F := E) (G := W) x
    (ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := E) (F := W)
      (tangentProjection P e he) (x := χ x))
    (hasFDerivAt_levelChartD0 P e he x hx)
  have hi := (hasFDerivAt_id (𝕜 := ℝ) (E := W) x).congr_of_eventuallyEq
    (eventually_levelChart_projection P e he x hx)
  have h := congrArg (fun L : W →L[ℝ] W => L u) (hd.unique hi)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using h

/-- The first level derivative vanishes throughout the same U. -/
theorem levelChartD1_norm (x : W) (hx : x ∈ U) (u : W) :
    DN (χ x) (Dχ x u) = 0 := by
  have hd := ((differentiable_diagonalCubic P.form (χ x)).hasFDerivAt).comp x
    (hasFDerivAt_levelChartD0 P e he x hx)
  simpa only [ContinuousLinearMap.comp_apply] using
    derivative_zero_of_eventually_constant hd
      (eventually_levelChart_norm P e he x hx) u

/-- Differentiate the proved neighborhood first-projection identity. -/
theorem levelChartD2_projection (x : W) (hx : x ∈ U) (w u : W) :
    π (DDχ x w u) = 0 := by
  have hd := HasFDerivAt.comp (𝕜 := ℝ) (E := W) (F := E) (G := W) x
    (ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := E) (F := W)
      (tangentProjection P e he) (x := Dχ x u))
    (eval_const_hasFDerivAt (hasFDerivAt_levelChartD1 P e he x hx) u)
  have hc : ∀ᶠ y in 𝓝 x, π (Dχ y u) = u :=
    Filter.mem_of_superset ((isOpen_smoothLevelChartDomain P e he).mem_nhds hx)
      (fun y hy => levelChartD1_projection P e he y hy u)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply] using
    derivative_zero_of_eventually_constant hd hc w

/-- Differentiate the proved neighborhood second-projection identity. -/
theorem levelChartD3_projection (x : W) (hx : x ∈ U) (t w u : W) :
    π (DDDχ x t w u) = 0 := by
  have hd := HasFDerivAt.comp (𝕜 := ℝ) (E := W) (F := E) (G := W) x
    (ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := E) (F := W)
      (tangentProjection P e he) (x := DDχ x w u))
    (eval_const_hasFDerivAt
      (eval_const_hasFDerivAt (hasFDerivAt_levelChartD2 P e he x hx) w) u)
  have hc : ∀ᶠ y in 𝓝 x, π (DDχ y w u) = 0 :=
    Filter.mem_of_superset ((isOpen_smoothLevelChartDomain P e he).mem_nhds hx)
      (fun y hy => levelChartD2_projection P e he y hy w u)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply] using
    derivative_zero_of_eventually_constant hd hc t

/-- Differentiate DN(χ)Dχ=0 on U using the actual Hessian and CLM product rule. -/
theorem levelChartD2_norm (x : W) (hx : x ∈ U) (w u : W) :
    DN (χ x) (DDχ x w u) +
      cubicHessian P (χ x) (Dχ x w) (Dχ x u) = 0 := by
  have hDN : HasFDerivAt (DN ∘ χ)
      ((cubicHessian P (χ x)).comp (Dχ x)) x :=
    HasFDerivAt.comp (𝕜 := ℝ) (E := W) (F := E) (G := E →L[ℝ] ℝ) x
      (hasFDerivAt_fderiv_diagonalCubic_actual P (χ x))
      (hasFDerivAt_levelChartD0 P e he x hx)
  have hDu := eval_const_hasFDerivAt (hasFDerivAt_levelChartD1 P e he x hx) u
  have hd := hDN.clm_apply hDu
  have hc : ∀ᶠ y in 𝓝 x, DN (χ y) (Dχ y u) = 0 :=
    Filter.mem_of_superset ((isOpen_smoothLevelChartDomain P e he).mem_nhds hx)
      (fun y hy => levelChartD1_norm P e he y hy u)
  simpa only [Function.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply] using
    derivative_zero_of_eventually_constant hd hc w

/-- Differentiate the SECOND constraint on U before specializing to zero.
The four terms come from the actual CLM chain and product rules. -/
theorem levelChartD3_norm (x : W) (hx : x ∈ U) (t w u : W) :
    cubicHessian P (χ x) (Dχ x w) (DDχ x t u) +
      (cubicHessian P (χ x) (DDχ x t w) (Dχ x u) +
        6 * P.form ![Dχ x t, Dχ x w, Dχ x u]) +
      (DN (χ x) (DDDχ x t w u) +
        cubicHessian P (χ x) (Dχ x t) (DDχ x w u)) = 0 := by
  have hχ := hasFDerivAt_levelChartD0 P e he x hx
  have hD := hasFDerivAt_levelChartD1 P e he x hx
  have hDD := hasFDerivAt_levelChartD2 P e he x hx
  have hH : HasFDerivAt (cubicHessian P ∘ χ)
      (((6 : ℝ) • fullyCurried P).comp (Dχ x)) x :=
    HasFDerivAt.comp (𝕜 := ℝ) (E := W) (F := E)
      (G := E →L[ℝ] E →L[ℝ] ℝ) x
      (hasFDerivAt_cubicHessian P (χ x)) hχ
  have hHw := hH.clm_apply (eval_const_hasFDerivAt hD w)
  have hHwu := hHw.clm_apply (eval_const_hasFDerivAt hD u)
  have hDN : HasFDerivAt (DN ∘ χ)
      ((cubicHessian P (χ x)).comp (Dχ x)) x :=
    HasFDerivAt.comp (𝕜 := ℝ) (E := W) (F := E) (G := E →L[ℝ] ℝ) x
      (hasFDerivAt_fderiv_diagonalCubic_actual P (χ x)) hχ
  have hDDw : HasFDerivAt (fun y : W => DDχ y w)
      ((DDDχ x).flip w) x :=
    eval_const_hasFDerivAt (X := W) (Y := W) (Z := W →L[ℝ] E)
      (f := levelChartD2 P e he) (f' := levelChartD3 P e he x) (x := x) hDD w
  have hDDwu : HasFDerivAt (fun y : W => DDχ y w u)
      (((DDDχ x).flip w).flip u) x :=
    eval_const_hasFDerivAt (X := W) (Y := W) (Z := E)
      (f := fun y : W => DDχ y w) (f' := (DDDχ x).flip w) (x := x) hDDw u
  have hd := hHwu.add (hDN.clm_apply hDDwu)
  have hc : ∀ᶠ y in 𝓝 x,
      cubicHessian P (χ y) (Dχ y w) (Dχ y u) + DN (χ y) (DDχ y w u) = 0 :=
    Filter.mem_of_superset ((isOpen_smoothLevelChartDomain P e he).mem_nhds hx)
      (fun y hy => by simpa only [Set.mem_ofPred_eq, add_comm] using
        levelChartD2_norm P e he y hy w u)
  simpa only [Function.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.smul_apply,
    smul_eq_mul, fullyCurried_apply] using
    derivative_zero_of_eventually_constant hd hc t

/-- Projection-zero forces an actual normal vector, by the fixed projection formula. -/
theorem normal_of_tangentProjection_zero (z : E) (hz : π z = 0) :
    z = (DN e z / 3) • e := by
  have h := congrArg (fun v : W => (v : E)) hz
  rw [tangentProjection_coe] at h
  exact sub_eq_zero.mp h

/-- First jet: both neighborhood first identities determine the actual derivative. -/
theorem levelChartD1_zero (u : W) : Dχ 0 u = (u : E) := by
  have hx := zero_mem_smoothLevelChartDomain P e he
  have hn := levelChartD1_norm P e he 0 hx u
  rw [levelChartPoint_zero] at hn
  have hp := congrArg (fun v : W => (v : E))
    (levelChartD1_projection P e he 0 hx u)
  simpa only [tangentProjection_coe, hn, zero_div, zero_smul, sub_zero] using hp

include he in
/-- Ambient normalized log-Hessian on true tangent vectors gives -H/3. -/
theorem cubicHessian_tangent_at_one (u v : W) :
    cubicHessian P e (u : E) (v : E) =
      -3 * logHessianForm P e (u : E) (v : E) := by
  have hu : DN e (u : E) = 0 := u.property
  have hv : DN e (v : E) = 0 := v.property
  have hpos : 0 < diagonalCubic P.form e := by rw [he]; norm_num
  have h := logHessianForm_apply P hpos (u : E) (v : E)
  rw [he, hu, hv] at h
  norm_num at h
  linarith

/-- Second jet: actual D²χ is normal, with coefficient given by the ambient metric. -/
theorem levelChartD2_zero (u v : W) :
    DDχ 0 u v = (logHessianForm P e (u : E) (v : E)) • e := by
  have hx := zero_mem_smoothLevelChartDomain P e he
  have hn := levelChartD2_norm P e he 0 hx u v
  rw [levelChartPoint_zero, levelChartD1_zero, levelChartD1_zero,
    cubicHessian_tangent_at_one P e he u v] at hn
  have hn' : DN e (DDχ 0 u v) =
      3 * logHessianForm P e (u : E) (v : E) := by linarith
  have hp := normal_of_tangentProjection_zero P e he (DDχ 0 u v)
    (levelChartD2_projection P e he 0 hx u v)
  rw [hn'] at hp
  have hc : (3 * logHessianForm P e (u : E) (v : E)) / 3 =
      logHessianForm P e (u : E) (v : E) := by ring
  simpa only [hc] using hp

private theorem cubicHessian_normal_tangent (r : ℝ) (u : W) :
    cubicHessian P e (r • e) (u : E) = 0 := by
  have hu : DN e (u : E) = 0 := u.property
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
    cubicHessian_radial, hu, mul_zero]

private theorem cubicHessian_tangent_normal (r : ℝ) (u : W) :
    cubicHessian P e (u : E) (r • e) = 0 := by
  rw [cubicHessian_symm]
  exact cubicHessian_normal_tangent P e r u

/-- Third jet: differentiating a neighborhood constraint kills all mixed normal
Hessian terms by Euler. Every jet is the actual nested fderiv of χ. -/
theorem levelChartD3_zero (u v w : W) :
    DDDχ 0 u v w = (-2 * P.form ![(u : E), (v : E), (w : E)]) • e := by
  have hx := zero_mem_smoothLevelChartDomain P e he
  have hn := levelChartD3_norm P e he 0 hx u v w
  rw [levelChartPoint_zero] at hn
  simp only [levelChartD1_zero, levelChartD2_zero,
    cubicHessian_normal_tangent, cubicHessian_tangent_normal,
    zero_add, add_zero] at hn
  have hn' : DN e (DDDχ 0 u v w) =
      -6 * P.form ![(u : E), (v : E), (w : E)] := by linarith
  have hp := normal_of_tangentProjection_zero P e he (DDDχ 0 u v w)
    (levelChartD3_projection P e he 0 hx u v w)
  rw [hn'] at hp
  have hc : (-6 * P.form ![(u : E), (v : E), (w : E)]) / 3 =
      -2 * P.form ![(u : E), (v : E), (w : E)] := by ring
  simpa only [hc] using hp

end CanonicalLevelChartNorms

end
end AlbertGeometry.Cubic
