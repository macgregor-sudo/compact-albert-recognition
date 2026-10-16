/-
The actual ambient normalized log-Hessian pulled
back along the original actual level chart. Derivatives below are literal
Frechet derivatives of the actual bilinear metric field. Whole-neighborhood
identities precede every differentiation. No connection/curvature jet is input.
-/
module

public import AlbertGeometry.LevelChartJets

@[expose] public section
open scoped ContDiff Topology
open Filter

namespace AlbertGeometry.Cubic
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

section CanonicalPullbackMetricNorms

local instance pullbackMetricDualNormedAddCommGroup (P : SymmetricTrilinearForm E) (e : E) :
    NormedAddCommGroup (tangentSpace P e →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := tangentSpace P e) (F := ℝ) (σ₁₂ := RingHom.id ℝ)

local instance pullbackMetricDualNormedSpace (P : SymmetricTrilinearForm E) (e : E) :
    NormedSpace ℝ (tangentSpace P e →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := tangentSpace P e) (F := ℝ) (σ₁₂ := RingHom.id ℝ)

local instance pullbackMetricBilinearNormedAddCommGroup (P : SymmetricTrilinearForm E) (e : E) :
    NormedAddCommGroup (tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := tangentSpace P e) (F := tangentSpace P e →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)

local instance pullbackMetricBilinearNormedSpace (P : SymmetricTrilinearForm E) (e : E) :
    NormedSpace ℝ (tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := tangentSpace P e) (F := tangentSpace P e →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)

local instance pullbackMetricTrilinearNormedAddCommGroup (P : SymmetricTrilinearForm E) (e : E) :
    NormedAddCommGroup (tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := tangentSpace P e) (F := tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)

local instance pullbackMetricTrilinearNormedSpace (P : SymmetricTrilinearForm E) (e : E) :
    NormedSpace ℝ (tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := tangentSpace P e) (F := tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)

/-- Genuine pullback of the ambient -D²logN/3, not Hessian of log(N∘χ). -/
def pullbackMetric (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) (x : tangentSpace P e) :
    tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ] ℝ :=
  (logHessianForm P (levelChartPoint P e he x)).bilinearComp
    (levelChartD1 P e he x) (levelChartD1 P e he x)

/-- Literal derivative of the actual bilinear metric field. -/
def pullbackMetricD1 (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) (x : tangentSpace P e) :
    tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ] ℝ :=
  fderiv ℝ (pullbackMetric P e he) x

/-- Literal derivative of that actual derivative field. -/
def pullbackMetricD2 (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) (x : tangentSpace P e) :
    tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ]
      tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ] ℝ :=
  fderiv ℝ (pullbackMetricD1 P e he) x

/-- Smooth cubic expression later identified with the ACTUAL metric on U. -/
def pullbackMetricFormula (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) (x : tangentSpace P e) :
    tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ] ℝ :=
  ((-2 : ℝ) • fullyCurried P (levelChartPoint P e he x)).bilinearComp
    (levelChartD1 P e he x) (levelChartD1 P e he x)

private theorem metric_eval_const_hasFDerivAt
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

private theorem contDiffAt_metric_flip
    {X Y Z F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : X → Y →L[ℝ] Z →L[ℝ] F} {x : X} (hf : ContDiffAt ℝ ⊤ f x) :
    ContDiffAt ℝ ⊤ (fun y => (f y).flip) x := by
  have hflip : ContDiff ℝ ⊤
      (ContinuousLinearMap.flipₗᵢ ℝ Y Z F :
        (Y →L[ℝ] Z →L[ℝ] F) → (Z →L[ℝ] Y →L[ℝ] F)) :=
    LinearIsometryEquiv.contDiff (𝕜 := ℝ)
      (E := Y →L[ℝ] Z →L[ℝ] F) (F := Z →L[ℝ] Y →L[ℝ] F) (n := ⊤)
      (ContinuousLinearMap.flipₗᵢ ℝ Y Z F)
  have hcomp : ContDiffAt ℝ ⊤
      (fun y => ContinuousLinearMap.flipₗᵢ ℝ Y Z F (f y)) x :=
    hflip.contDiffAt.fun_comp x hf
  have hsame : (fun y => ContinuousLinearMap.flipₗᵢ ℝ Y Z F (f y)) =
      (fun y => (f y).flip) := by
    funext y
    rfl
  rw [hsame] at hcomp
  exact hcomp


/-- A typed composition certificate on abstract carriers.  This isolates the
two compositions and flips before specialization to the actual chart. -/
private theorem contDiffAt_metric_bilinearComp
    {X Y Z A B F : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : X → A →L[ℝ] B →L[ℝ] F}
    {g : X → Y →L[ℝ] A} {h : X → Z →L[ℝ] B} {x : X}
    (hf : ContDiffAt ℝ ⊤ f x)
    (hg : ContDiffAt ℝ ⊤ g x) (hh : ContDiffAt ℝ ⊤ h x) :
    ContDiffAt ℝ ⊤ (fun y : X => (f y).bilinearComp (g y) (h y)) x := by
  have hfg : ContDiffAt ℝ ⊤ (fun y : X => (f y).comp (g y)) x :=
    ContDiffAt.clm_comp (𝕜 := ℝ) (X := X) (E := Y) (F := A)
      (G := B →L[ℝ] F) (n := ⊤) (g := f) (f := g) (x := x) hf hg
  have hfgFlip : ContDiffAt ℝ ⊤
      (fun y : X => ((f y).comp (g y)).flip) x :=
    contDiffAt_metric_flip (X := X) (Y := Y) (Z := B) (F := F)
      (f := fun y : X => (f y).comp (g y)) (x := x) hfg
  have hsecond : ContDiffAt ℝ ⊤
      (fun y : X => (((f y).comp (g y)).flip).comp (h y)) x :=
    ContDiffAt.clm_comp (𝕜 := ℝ) (X := X) (E := Z) (F := B)
      (G := Y →L[ℝ] F) (n := ⊤)
      (g := fun y : X => ((f y).comp (g y)).flip)
      (f := h) (x := x) hfgFlip hh
  have hfinal : ContDiffAt ℝ ⊤
      (fun y : X => ((((f y).comp (g y)).flip).comp (h y)).flip) x :=
    contDiffAt_metric_flip (X := X) (Y := Z) (Z := Y) (F := F)
      (f := fun y : X => (((f y).comp (g y)).flip).comp (h y))
      (x := x) hsecond
  have hsame :
      (fun y : X => ((((f y).comp (g y)).flip).comp (h y)).flip) =
      (fun y : X => (f y).bilinearComp (g y) (h y)) := by
    funext y
    rfl
  rw [hsame] at hfinal
  exact hfinal

/-- Internal chain certificate only; no arbitrary derivative is assumed. -/
private def metricTrilinearDerivative
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (P : SymmetricTrilinearForm E) (a b c : E) (da db dc : X →L[ℝ] E) :
    X →L[ℝ] ℝ :=
  (fullyCurried P a b).comp dc +
    ((fullyCurried P a).comp db).flip c +
    (((fullyCurried P).comp da).flip b).flip c

private theorem metricTrilinearDerivative_apply
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (P : SymmetricTrilinearForm E) (a b c : E) (da db dc : X →L[ℝ] E) (s : X) :
    metricTrilinearDerivative P a b c da db dc s =
      P.form ![a, b, dc s] + P.form ![a, db s, c] + P.form ![da s, b, c] := by
  simp only [metricTrilinearDerivative, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, fullyCurried_apply]

private theorem hasFDerivAt_metricTrilinear
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (P : SymmetricTrilinearForm E) {a b c : X → E}
    {da db dc : X →L[ℝ] E} {x : X}
    (ha : HasFDerivAt a da x) (hb : HasFDerivAt b db x) (hc : HasFDerivAt c dc x) :
    HasFDerivAt (fun y => P.form ![a y, b y, c y])
      (metricTrilinearDerivative P (a x) (b x) (c x) da db dc) x := by
  have hlinear : HasFDerivAt (fullyCurried P) (fullyCurried P) (a x) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := E)
      (F := E →L[ℝ] E →L[ℝ] ℝ) (fullyCurried P) (x := a x)
  have hcomp := HasFDerivAt.comp (𝕜 := ℝ) (E := X) (F := E)
    (G := E →L[ℝ] E →L[ℝ] ℝ) x hlinear ha
  have h := (hcomp.clm_apply hb).clm_apply hc
  simp only [Function.comp_apply, fullyCurried_apply] at h
  apply h.congr_fderiv
  ext s
  simp only [metricTrilinearDerivative, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  ring

variable (P : SymmetricTrilinearForm E) (e : E) (he : diagonalCubic P.form e = 1)
local notation "W" => tangentSpace P e
local notation "χ" => levelChartPoint P e he
local notation "Dχ" => levelChartD1 P e he
local notation "DDχ" => levelChartD2 P e he
local notation "DDDχ" => levelChartD3 P e he
local notation "U" => smoothLevelChartDomain P e he
local notation "G" => pullbackMetric P e he
local notation "DG" => pullbackMetricD1 P e he
local notation "DDG" => pullbackMetricD2 P e he
local notation "a" => logHessianForm P e

@[simp] theorem pullbackMetric_apply (x u w : W) :
    G x u w = logHessianForm P (χ x) (Dχ x u) (Dχ x w) :=
  ContinuousLinearMap.bilinearComp_apply _ _ _ _ _

/-- Whole-domain identity from Nχ=1 and DNχ Dχ=0, before metric derivatives. -/
theorem pullbackMetric_eq_formula (x : W) (hx : x ∈ U) :
    G x = pullbackMetricFormula P e he x := by
  have hN := levelChartPoint_on_level P e he x (smoothLevelChartDomain_subset P e he hx)
  have hpos : 0 < diagonalCubic P.form (χ x) := by rw [hN]; norm_num
  ext u w
  rw [pullbackMetric_apply, logHessianForm_apply P hpos, hN,
    levelChartD1_norm P e he x hx u, levelChartD1_norm P e he x hx w,
    cubicHessian_apply]
  simp only [pullbackMetricFormula, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, fullyCurried_apply]
  ring

theorem pullbackMetric_cubic_apply (x : W) (hx : x ∈ U) (u w : W) :
    G x u w = -2 * P.form ![χ x, Dχ x u, Dχ x w] := by
  rw [pullbackMetric_eq_formula P e he x hx]
  simp only [pullbackMetricFormula, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, fullyCurried_apply]

set_option maxHeartbeats 2000000 in
/-- Smoothness follows on this same fixed U from the actual cubic identity. -/
theorem contDiffAt_pullbackMetric (x : W) (hx : x ∈ U) : ContDiffAt ℝ ⊤ G x := by
  have hχ : ContDiffAt ℝ ⊤ (levelChartPoint P e he) x :=
    contDiffAt_levelChartPoint_smoothDomain P e he ⊤ x hx
  have hD : ContDiffAt ℝ ⊤ (levelChartD1 P e he) x :=
    contDiffAt_levelChartD1 P e he x hx
  have hscaled : ContDiff ℝ ⊤
      ((-2 : ℝ) • fullyCurried P : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := E)
      (F := E →L[ℝ] E →L[ℝ] ℝ) (n := ⊤) ((-2 : ℝ) • fullyCurried P)
  have hF : ContDiffAt ℝ ⊤
      (fun y : W => ((-2 : ℝ) • fullyCurried P) (χ y)) x :=
    ContDiffAt.fun_comp (𝕜 := ℝ) (E := W) (F := E)
      («G» := E →L[ℝ] E →L[ℝ] ℝ) (n := ⊤)
      (g := ((-2 : ℝ) • fullyCurried P)) (f := levelChartPoint P e he) x
      hscaled.contDiffAt hχ
  have hcomposed : ContDiffAt ℝ ⊤
      (fun y : W => (((-2 : ℝ) • fullyCurried P) (χ y)).bilinearComp
        (Dχ y) (Dχ y)) x :=
    contDiffAt_metric_bilinearComp (X := W) (Y := W) (Z := W)
      (A := E) (B := E) (F := ℝ)
      (f := fun y : W => ((-2 : ℝ) • fullyCurried P) (χ y))
      (g := levelChartD1 P e he) (h := levelChartD1 P e he) (x := x) hF hD hD
  have hsame :
      (fun y : W => (((-2 : ℝ) • fullyCurried P) (χ y)).bilinearComp
        (Dχ y) (Dχ y)) = pullbackMetricFormula P e he := by
    funext y
    rfl
  have hformula : ContDiffAt ℝ ⊤ (pullbackMetricFormula P e he) x := by
    rw [hsame] at hcomposed
    exact hcomposed
  have heventual : G =ᶠ[𝓝 x] pullbackMetricFormula P e he :=
    Filter.mem_of_superset ((isOpen_smoothLevelChartDomain P e he).mem_nhds hx)
      (fun y hy => pullbackMetric_eq_formula P e he y hy)
  exact hformula.congr_of_eventuallyEq heventual

theorem hasFDerivAt_pullbackMetric (x : W) (hx : x ∈ U) : HasFDerivAt G (DG x) x :=
  ((contDiffAt_pullbackMetric P e he x hx).differentiableAt (by simp)).hasFDerivAt

theorem hasFDerivAt_pullbackMetricD1 (x : W) (hx : x ∈ U) :
    HasFDerivAt DG (DDG x) x := by
  have h : ContDiffAt ℝ ⊤ DG x :=
    ContDiffAt.fderiv_right (𝕜 := ℝ) (E := W)
      (F := W →L[ℝ] W →L[ℝ] ℝ) (f := G) (x₀ := x) (n := ⊤) (m := ⊤)
      (contDiffAt_pullbackMetric P e he x hx) (by simp)
  exact (h.differentiableAt (by simp)).hasFDerivAt

/-- First actual metric derivative, established throughout U before differentiating again. -/
theorem pullbackMetricD1_formula (x : W) (hx : x ∈ U) (s u w : W) :
    DG x s u w = -2 *
      (P.form ![χ x, Dχ x u, DDχ x s w] +
        P.form ![χ x, DDχ x s u, Dχ x w] +
        P.form ![Dχ x s, Dχ x u, Dχ x w]) := by
  have hχ := hasFDerivAt_levelChartD0 P e he x hx
  have hD := hasFDerivAt_levelChartD1 P e he x hx
  have hf := (hasFDerivAt_metricTrilinear P hχ
    (metric_eval_const_hasFDerivAt hD u)
    (metric_eval_const_hasFDerivAt hD w)).const_smul (-2 : ℝ)
  have hc : (fun y => G y u w) =ᶠ[𝓝 x]
      (fun y => (-2 : ℝ) • P.form ![χ y, Dχ y u, Dχ y w]) :=
    Filter.mem_of_superset ((isOpen_smoothLevelChartDomain P e he).mem_nhds hx)
      (fun y hy => by
        simpa only [Set.mem_ofPred_eq, smul_eq_mul] using
          pullbackMetric_cubic_apply P e he y hy u w)
  have hg := metric_eval_const_hasFDerivAt
    (metric_eval_const_hasFDerivAt (hasFDerivAt_pullbackMetric P e he x hx) u) w
  have h := congrArg (fun L : W →L[ℝ] ℝ => L s)
    (hg.unique (hf.congr_of_eventuallyEq hc))
  simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, metricTrilinearDerivative_apply] using h

section AlignedLevelChartVectorEvaluation

attribute [local instance] levelChartLinearNormedAddCommGroup levelChartLinearNormedSpace
  levelChartBilinearNormedAddCommGroup levelChartBilinearNormedSpace

/-- Actual second metric derivative: differentiate the whole-U first formula. -/
theorem pullbackMetricD2_formula (x : W) (hx : x ∈ U) (t s u w : W) :
    DDG x t s u w = -2 *
      ((P.form ![χ x, Dχ x u, DDDχ x t s w] +
        P.form ![χ x, DDχ x t u, DDχ x s w] +
        P.form ![Dχ x t, Dχ x u, DDχ x s w]) +
      (P.form ![χ x, DDχ x s u, DDχ x t w] +
        P.form ![χ x, DDDχ x t s u, Dχ x w] +
        P.form ![Dχ x t, DDχ x s u, Dχ x w]) +
      (P.form ![Dχ x s, Dχ x u, DDχ x t w] +
        P.form ![Dχ x s, DDχ x t u, Dχ x w] +
        P.form ![DDχ x t s, Dχ x u, Dχ x w])) := by
  have hχ := hasFDerivAt_levelChartD0 P e he x hx
  have hD := hasFDerivAt_levelChartD1 P e he x hx
  have hDD := hasFDerivAt_levelChartD2 P e he x hx
  have hDu := metric_eval_const_hasFDerivAt hD u
  have hDw := metric_eval_const_hasFDerivAt hD w
  have hDs := metric_eval_const_hasFDerivAt hD s
  have hKs : HasFDerivAt (fun y : W => DDχ y s) ((DDDχ x).flip s) x :=
    metric_eval_const_hasFDerivAt (X := W) (Y := W) (Z := W →L[ℝ] E)
      (f := levelChartD2 P e he) (f' := levelChartD3 P e he x) (x := x) hDD s
  have hKsu : HasFDerivAt (fun y : W => DDχ y s u)
      (((DDDχ x).flip s).flip u) x :=
    metric_eval_const_hasFDerivAt (X := W) (Y := W) (Z := E)
      (f := fun y : W => DDχ y s) (f' := (DDDχ x).flip s) (x := x) hKs u
  have hKsw : HasFDerivAt (fun y : W => DDχ y s w)
      (((DDDχ x).flip s).flip w) x :=
    metric_eval_const_hasFDerivAt (X := W) (Y := W) (Z := E)
      (f := fun y : W => DDχ y s) (f' := (DDDχ x).flip s) (x := x) hKs w
  have hA := hasFDerivAt_metricTrilinear P hχ hDu hKsw
  have hB := hasFDerivAt_metricTrilinear P hχ hKsu hDw
  have hC := hasFDerivAt_metricTrilinear P hDs hDu hDw
  have hf := ((hA.add hB).add hC).const_smul (-2 : ℝ)
  have hc : (fun y => DG y s u w) =ᶠ[𝓝 x]
      (fun y => (-2 : ℝ) •
        (P.form ![χ y, Dχ y u, DDχ y s w] +
          P.form ![χ y, DDχ y s u, Dχ y w] +
          P.form ![Dχ y s, Dχ y u, Dχ y w])) :=
    Filter.mem_of_superset ((isOpen_smoothLevelChartDomain P e he).mem_nhds hx)
      (fun y hy => by
        simpa only [Set.mem_ofPred_eq, smul_eq_mul] using
          pullbackMetricD1_formula P e he y hy s u w)
  have hg := metric_eval_const_hasFDerivAt
    (metric_eval_const_hasFDerivAt
      (metric_eval_const_hasFDerivAt (hasFDerivAt_pullbackMetricD1 P e he x hx) s) u) w
  have h := congrArg (fun L : W →L[ℝ] ℝ => L t)
    (hg.unique (hf.congr_of_eventuallyEq hc))
  simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, smul_eq_mul, metricTrilinearDerivative_apply] using h

end AlignedLevelChartVectorEvaluation

/-- The zero metric is the restriction of the actual ambient metric. -/
theorem pullbackMetric_zero (u w : W) : G 0 u w = a (u : E) (w : E) := by
  simp only [pullbackMetric_apply, levelChartPoint_zero, levelChartD1_zero]

private theorem metric_p_smul1 (r : ℝ) (x y z : E) :
    P.form ![r • x, y, z] = r * P.form ![x, y, z] := by
  simp only [← fullyCurried_apply, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
private theorem metric_p_smul2 (r : ℝ) (x y z : E) :
    P.form ![x, r • y, z] = r * P.form ![x, y, z] := by
  simp only [← fullyCurried_apply, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
private theorem metric_p_smul3 (r : ℝ) (x y z : E) :
    P.form ![x, y, r • z] = r * P.form ![x, y, z] := by
  simp only [← fullyCurried_apply, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]

private theorem metric_p_e_e_tangent (u : W) : P.form ![e, e, (u : E)] = 0 := by
  have h : fderiv ℝ (diagonalCubic P.form) e (u : E) = 0 := u.property
  rw [fderiv_diagonalCubic_apply_symmetric] at h
  linarith
private theorem metric_p_e_tangent_e (u : W) : P.form ![e, (u : E), e] = 0 := by
  rw [P.swap23]
  exact metric_p_e_e_tangent P e u
include he in
private theorem metric_p_e_tangents (u w : W) :
    P.form ![e, (u : E), (w : E)] = -a (u : E) (w : E) / 2 := by
  have h := cubicHessian_tangent_at_one P e he u w
  rw [cubicHessian_apply] at h
  linarith
include he in
private theorem metric_p_tangent_e_tangent (u w : W) :
    P.form ![(u : E), e, (w : E)] = -a (u : E) (w : E) / 2 := by
  rw [P.swap12]
  exact metric_p_e_tangents P e he u w
include he in
private theorem metric_p_tangents_e (u w : W) :
    P.form ![(u : E), (w : E), e] = -a (u : E) (w : E) / 2 := by
  rw [P.swap23]
  exact metric_p_tangent_e_tangent P e he u w
include he in
private theorem metric_p_e_e_e : P.form ![e, e, e] = 1 := by
  have h : (fun _ : Fin 3 => e) = ![e, e, e] := by
    ext i
    fin_cases i <;> rfl
  simpa only [diagonalCubic, h] using he

/-- Actual first metric derivative at zero is the tangent cubic -2P. -/
theorem pullbackMetricD1_zero (s u w : W) :
    DG 0 s u w = -2 * P.form ![(s : E), (u : E), (w : E)] := by
  rw [pullbackMetricD1_formula P e he 0 (zero_mem_smoothLevelChartDomain P e he)]
  simp only [levelChartPoint_zero, levelChartD1_zero, levelChartD2_zero,
    metric_p_smul1, metric_p_smul2, metric_p_smul3,
    metric_p_e_e_tangent, metric_p_e_tangent_e, mul_zero, zero_add, add_zero]

/-- The actual second metric derivative has no unproved prescribed coefficient.
Six normal terms cancel in pairs, leaving the factor a(t,s)a(u,w). -/
theorem pullbackMetricD2_zero (t s u w : W) :
    DDG 0 t s u w = a (t : E) (s : E) * a (u : E) (w : E) := by
  rw [pullbackMetricD2_formula P e he 0 (zero_mem_smoothLevelChartDomain P e he)]
  simp only [levelChartPoint_zero, levelChartD1_zero, levelChartD2_zero,
    levelChartD3_zero, metric_p_smul1, metric_p_smul2, metric_p_smul3,
    metric_p_e_e_tangent, metric_p_e_tangent_e, metric_p_e_tangents P e he,
    metric_p_tangent_e_tangent P e he, metric_p_tangents_e P e he,
    metric_p_e_e_e P e he]
  ring

end CanonicalPullbackMetricNorms

end
end AlbertGeometry.Cubic
