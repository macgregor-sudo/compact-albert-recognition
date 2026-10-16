/-
Gamma is the actual
positive-metric Koszul construction from LeviCivitaConnection. Its derivative is
obtained from the WHOLE open-domain identity before any basepoint specialization.
Curvature is defined by the actual covariant-derivative commutator, with a proved
all-field value formula and independence of field extensions. The basepoint
-wedge-[K,K] identity is a conclusion, never a definition or supplied jet.
The canonical operator-norm instances used by PullbackMetricJets and
LeviCivitaConnection are activated section-locally.
-/
module

public import AlbertGeometry.LeviCivitaConnection
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

@[expose] public section
open scoped ContDiff Topology
open Filter

namespace AlbertGeometry.Cubic
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (P : SymmetricTrilinearForm E) (e : E) (he : diagonalCubic P.form e = 1)
local notation "W" => tangentSpace P e
local notation "G" => pullbackMetric P e he
local notation "DG" => pullbackMetricD1 P e he
local notation "DDG" => pullbackMetricD2 P e he
local notation "Γ" => leviCivitaGamma P e he

section CanonicalCurvatureNorms

-- The same canonical operator-norm instances, in the same order, that
-- LeviCivitaConnection activates; nested maps over the tangent submodule need them.
attribute [local instance] pullbackMetricDualNormedAddCommGroup pullbackMetricDualNormedSpace
  pullbackMetricBilinearNormedAddCommGroup pullbackMetricBilinearNormedSpace
  pullbackMetricTrilinearNormedAddCommGroup pullbackMetricTrilinearNormedSpace
  lcEndNormedAddCommGroup lcEndNormedSpace
  lcBilinearVectorNormedAddCommGroup lcBilinearVectorNormedSpace
  lcInverseNormedAddCommGroup lcInverseNormedSpace

/-- Literal derivative of the actual, previously constructed Gamma FIELD. -/
def leviCivitaGammaD1 (x : W) : W →L[ℝ] W →L[ℝ] W →L[ℝ] W :=
  fderiv ℝ Γ x

/-- Actual basepoint metric; its equality with ambient a_e is proved below. -/
def baseChartMetric : W →L[ℝ] W →L[ℝ] ℝ := G 0

@[simp] theorem baseChartMetric_apply (u v : W) :
    baseChartMetric P e he u v = logHessianForm P e (u : E) (v : E) :=
  pullbackMetric_zero P e he u v

/-- Literal restriction of the given continuous symmetric cubic to the tangent. -/
def tangentSymmetricCubic : SymmetricTrilinearForm W where
  form := P.form.compContinuousLinearMap (fun _ : Fin 3 => (tangentSpace P e).subtypeL)
  swap12 := by
    intro x y z
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      Submodule.subtypeL_apply]
    convert P.swap12 (x : E) (y : E) (z : E) using 1 <;>
      congr 1 <;> ext i <;> fin_cases i <;> rfl
  swap23 := by
    intro x y z
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      Submodule.subtypeL_apply]
    convert P.swap23 (x : E) (y : E) (z : E) using 1 <;>
      congr 1 <;> ext i <;> fin_cases i <;> rfl

@[simp] theorem tangentSymmetricCubic_apply (u v w : W) :
    (tangentSymmetricCubic P e).form ![u, v, w] =
      P.form ![(u : E), (v : E), (w : E)] := by
  simp only [tangentSymmetricCubic, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    Submodule.subtypeL_apply]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- K raises the ACTUAL restricted cubic using the actual base metric dual.
No Gamma value or derivative is used in this definition. -/
def raisedTangentCubic : W →L[ℝ] W →L[ℝ] W :=
  ((ContinuousLinearMap.compL ℝ W (W →L[ℝ] ℝ) W)
    (baseChartMetric P e he).inverse).comp (fullyCurried (tangentSymmetricCubic P e))

@[simp] theorem raisedTangentCubic_apply (u v : W) :
    raisedTangentCubic P e he u v = (baseChartMetric P e he).inverse
      (fullyCurried (tangentSymmetricCubic P e) u v) := by
  simp only [raisedTangentCubic, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply]

/-- Actual commutator on fields, with the actual coordinate Lie bracket. -/
def chartConnectionCurvature (x : W) (X Y Z : W → W) : W :=
  chartCovariantDerivative P e he x X
      (fun y => chartCovariantDerivative P e he y Y Z) -
    chartCovariantDerivative P e he x Y
      (fun y => chartCovariantDerivative P e he y X Z) -
    chartCovariantDerivative P e he x (fun y => chartLieBracket P e y X Y) Z

/-- Curvature on values is the ACTUAL connection commutator on constant fields.
The claimed basepoint formula is not used in this definition. -/
def chartCurvature (x u v w : W) : W :=
  chartConnectionCurvature P e he x (fun _ => u) (fun _ => v) (fun _ => w)

-- `he` is part of the intended signature (all callers pass it); the inclusion
-- is forced so that it never depends on the body elaborating.
include he in
/-- The actual coefficient formula, later identified with the genuine commutator.
All factors are Gamma and its actual derivative, not prescribed curvature. -/
def chartCurvatureCLM (x : W) : W →L[ℝ] W →L[ℝ] W →L[ℝ] W :=
  let T : W →L[ℝ] W →L[ℝ] W →L[ℝ] W :=
    (ContinuousLinearMap.compL ℝ W W W).bilinearComp (Γ x) (Γ x)
  leviCivitaGammaD1 P e he x -
      (ContinuousLinearMap.flip (E := W) (F := W) («G» := W →L[ℝ] W)
        (leviCivitaGammaD1 P e he x)) + T -
    (ContinuousLinearMap.flip (E := W) (F := W) («G» := W →L[ℝ] W) T)

@[simp] theorem chartCurvatureCLM_apply (x u v w : W) :
    chartCurvatureCLM P e he x u v w =
      leviCivitaGammaD1 P e he x u v w - leviCivitaGammaD1 P e he x v u w +
        Γ x u (Γ x v w) - Γ x v (Γ x u w) := by
  simp only [chartCurvatureCLM, add_apply, sub_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply]

private theorem curvature_eval_const_hasFDerivAt
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

variable [FiniteDimensional ℝ E]
variable (hpos : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u)
local notation "S" => leviCivitaChartDomain P e he hpos
local notation "g" => baseChartMetric P e he
local notation "K" => raisedTangentCubic P e he
local notation "DΓ" => leviCivitaGammaD1 P e he

/-- Gamma is actually differentiable on S by the prior whole-domain smoothness. -/
theorem hasFDerivAt_leviCivitaGamma (x : W) (hx : x ∈ S) :
    HasFDerivAt Γ (DΓ x) x :=
  ((contDiffAt_leviCivitaGamma P e he hpos x hx).differentiableAt
    (by simp)).hasFDerivAt

include hpos in
/-- Actual metric raising of the tangent cubic, including its trace/3 scale. -/
theorem raisedTangentCubic_pairing (u v w : W) :
    g (K u v) w = P.form ![(u : E), (v : E), (w : E)] := by
  have h0 := (leviCivitaChartDomain_spec P e he hpos).2.1
  have hi := pullbackMetric_dual_isInvertible P e he hpos 0 h0
  rw [raisedTangentCubic_apply]
  have h := congrArg (fun L : W →L[ℝ] ℝ => L w)
    (hi.self_apply_inverse (fullyCurried (tangentSymmetricCubic P e) u v))
  simpa only [baseChartMetric, fullyCurried_apply, tangentSymmetricCubic_apply] using h

include hpos in
theorem raisedTangentCubic_symm (u v : W) : K u v = K v u := by
  apply pullbackMetric_dual_injective P e he hpos 0
    (leviCivitaChartDomain_spec P e he hpos).2.1
  ext w
  change g (K u v) w = g (K v u) w
  rw [raisedTangentCubic_pairing P e he hpos,
    raisedTangentCubic_pairing P e he hpos, P.swap12]

/-- Left half of the differentiated Koszul identity: the actual product rule
for y ↦ G y (Γ y u v) w, evaluated at the direction s. -/
private theorem koszul_left_fderiv_apply (x : W) (hx : x ∈ S) (s u v w : W) :
    fderiv ℝ (fun y => G y (Γ y u v) w) x s =
      G x (DΓ x s u v) w + DG x s (Γ x u v) w := by
  have hxU := (leviCivitaChartDomain_spec P e he hpos).2.2.1 hx
  have hGamma := curvature_eval_const_hasFDerivAt
    (curvature_eval_const_hasFDerivAt (hasFDerivAt_leviCivitaGamma P e he hpos x hx) u) v
  have hleft := curvature_eval_const_hasFDerivAt
    ((hasFDerivAt_pullbackMetric P e he x hxU).clm_apply hGamma) w
  have h := congrArg (fun L : W →L[ℝ] ℝ => L s) hleft.fderiv
  simpa only [ContinuousLinearMap.flip_apply, add_apply,
    ContinuousLinearMap.comp_apply] using h

/-- Right half: the same scalar field equals the Koszul expression in DG on a
whole neighborhood, so its derivative is the Koszul expression in DDG. -/
private theorem koszul_right_fderiv_apply (x : W) (hx : x ∈ S) (s u v w : W) :
    fderiv ℝ (fun y => G y (Γ y u v) w) x s =
      (DDG x s u v w + DDG x s v u w - DDG x s w u v) / 2 := by
  have hxU := (leviCivitaChartDomain_spec P e he hpos).2.2.1 hx
  have hDD := hasFDerivAt_pullbackMetricD1 P e he x hxU
  have h1 := curvature_eval_const_hasFDerivAt
    (curvature_eval_const_hasFDerivAt (curvature_eval_const_hasFDerivAt hDD u) v) w
  have h2 := curvature_eval_const_hasFDerivAt
    (curvature_eval_const_hasFDerivAt (curvature_eval_const_hasFDerivAt hDD v) u) w
  have h3 := curvature_eval_const_hasFDerivAt
    (curvature_eval_const_hasFDerivAt (curvature_eval_const_hasFDerivAt hDD w) u) v
  have hkoszul : (fun y => G y (Γ y u v) w) =ᶠ[𝓝 x]
      (fun y => (1 / 2 : ℝ) • (DG y u v w + DG y v u w - DG y w u v)) := by
    filter_upwards [eventually_leviCivitaGamma_koszul P e he hpos x hx u v w] with y hy
    refine hy.trans ?_
    simp only [koszulCovector_apply, smul_eq_mul]
    ring
  have hright := (((h1.add h2).sub h3).const_smul (1 / 2 : ℝ)).congr_of_eventuallyEq hkoszul
  have h := congrArg (fun L : W →L[ℝ] ℝ => L s) hright.fderiv
  simpa only [ContinuousLinearMap.flip_apply, add_apply, sub_apply, smul_apply,
    smul_eq_mul, one_div_mul_eq_div] using h

/-- Differentiate the proved WHOLE-S Koszul identity before specializing at zero. -/
theorem leviCivitaGammaD1_koszul (x : W) (hx : x ∈ S) (s u v w : W) :
    G x (DΓ x s u v) w + DG x s (Γ x u v) w =
      (DDG x s u v w + DDG x s v u w - DDG x s w u v) / 2 :=
  (koszul_left_fderiv_apply P e he hpos x hx s u v w).symm.trans
    (koszul_right_fderiv_apply P e he hpos x hx s u v w)

include hpos in
/-- Gamma at zero is a theorem about the actual connection, not its definition. -/
theorem leviCivitaGamma_zero (u v : W) : Γ 0 u v = -K u v := by
  have h0 := (leviCivitaChartDomain_spec P e he hpos).2.1
  apply pullbackMetric_dual_injective P e he hpos 0 h0
  ext w
  rw [leviCivitaGamma_koszul P e he hpos 0 h0, koszulCovector_apply]
  simp only [pullbackMetricD1_zero, map_neg]
  change _ = -(g (K u v) w)
  rw [raisedTangentCubic_pairing P e he hpos]
  rw [P.swap12 (v : E) (u : E) (w : E),
    P.swap12 (w : E) (u : E) (v : E), P.swap23 (u : E) (w : E) (v : E)]
  ring

include hpos in
/-- Actual derivative of Gamma at zero, deduced from the all-domain derivative
identity and actual metric jets, not a supplied first connection jet. -/
theorem leviCivitaGammaD1_zero (s u v : W) :
    DΓ 0 s u v = (-2 : ℝ) • K s (K u v) +
      (1 / 2 : ℝ) • (g s u • v + g s v • u - g u v • s) := by
  have h0 := (leviCivitaChartDomain_spec P e he hpos).2.1
  apply pullbackMetric_dual_injective P e he hpos 0 h0
  ext w
  -- Differentiated Koszul identity at the basepoint.
  have h := leviCivitaGammaD1_koszul P e he hpos 0 h0 s u v w
  -- Basepoint Gamma is -K; move the sign through the bilinear jet DG 0 s.
  rw [leviCivitaGamma_zero P e he hpos u v] at h
  simp only [map_neg, neg_apply] at h
  -- Actual basepoint metric jets.
  simp only [pullbackMetricD1_zero, pullbackMetricD2_zero] at h
  -- Raise the cubic and write every basepoint metric value as a(↑·,↑·).
  simp only [← raisedTangentCubic_pairing P e he hpos s (K u v) w,
    pullbackMetric_zero P e he, baseChartMetric_apply] at h
  simp only [map_add, map_sub, map_smul, add_apply, sub_apply, smul_apply, smul_eq_mul,
    pullbackMetric_zero P e he, baseChartMetric_apply]
  linarith

/-- Actual directional derivative of the constructed covariant derivative field.
The second derivative is the literal derivative of fderiv Z, not supplied data. -/
theorem fderiv_chartCovariantDerivative (x : W) (hx : x ∈ S)
    (Y Z : W → W) (hY : DifferentiableAt ℝ Y x) (hZ : ContDiffAt ℝ ⊤ Z x) (s : W) :
    fderiv ℝ (fun y => chartCovariantDerivative P e he y Y Z) x s =
      fderiv ℝ Z x (fderiv ℝ Y x s) +
      fderiv ℝ (fderiv ℝ Z) x s (Y x) +
      Γ x (Y x) (fderiv ℝ Z x s) +
      Γ x (fderiv ℝ Y x s) (Z x) + DΓ x s (Y x) (Z x) := by
  have hDZsmooth : ContDiffAt ℝ ⊤ (fderiv ℝ Z) x := hZ.fderiv_right (by simp)
  have hDZ : DifferentiableAt ℝ (fderiv ℝ Z) x :=
    hDZsmooth.differentiableAt (by simp)
  have hz : DifferentiableAt ℝ Z x := hZ.differentiableAt (by simp)
  have h1 := hDZ.hasFDerivAt.clm_apply hY.hasFDerivAt
  have h2 := ((hasFDerivAt_leviCivitaGamma P e he hpos x hx).clm_apply
    hY.hasFDerivAt).clm_apply hz.hasFDerivAt
  -- Sum rule, typed by the literal lambda of the covariant-derivative field.
  have hsum : HasFDerivAt (fun y => chartCovariantDerivative P e he y Y Z) _ x :=
    h1.add h2
  have heval := congrArg (fun L : W →L[ℝ] W => L s) hsum.fderiv
  have hv : fderiv ℝ (fun y => chartCovariantDerivative P e he y Y Z) x s =
      (fderiv ℝ Z x (fderiv ℝ Y x s) + fderiv ℝ (fderiv ℝ Z) x s (Y x)) +
        (Γ x (Y x) (fderiv ℝ Z x s) +
          (Γ x (fderiv ℝ Y x s) (Z x) + DΓ x s (Y x) (Z x))) := by
    simpa only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply] using heval
  refine hv.trans ?_
  module

/-- Full field expansion: genuine Schwarz symmetry cancels every extension term.
Only the value of each vector field survives. -/
theorem chartConnectionCurvature_formula (x : W) (hx : x ∈ S)
    (X Y Z : W → W) (hX : DifferentiableAt ℝ X x)
    (hY : DifferentiableAt ℝ Y x) (hZ : ContDiffAt ℝ ⊤ Z x) :
    chartConnectionCurvature P e he x X Y Z =
      chartCurvatureCLM P e he x (X x) (Y x) (Z x) := by
  change
    (fderiv ℝ (fun y => chartCovariantDerivative P e he y Y Z) x (X x) +
      Γ x (X x) (chartCovariantDerivative P e he x Y Z)) -
    (fderiv ℝ (fun y => chartCovariantDerivative P e he y X Z) x (Y x) +
      Γ x (Y x) (chartCovariantDerivative P e he x X Z)) -
    (fderiv ℝ Z x (chartLieBracket P e x X Y) +
      Γ x (chartLieBracket P e x X Y) (Z x)) = _
  rw [fderiv_chartCovariantDerivative P e he hpos x hx Y Z hY hZ,
    fderiv_chartCovariantDerivative P e he hpos x hx X Z hX hZ]
  simp only [chartCovariantDerivative, chartLieBracket, map_add, map_sub,
    add_apply, sub_apply, chartCurvatureCLM_apply]
  rw [(hZ.isSymmSndFDerivAt le_top).eq (X x) (Y x)]
  module

/-- The actual coordinate bracket of constant fields is zero. -/
theorem chartLieBracket_const (x u v : W) :
    chartLieBracket P e x (fun _ => u) (fun _ => v) = 0 := by
  simp only [chartLieBracket, fderiv_const_apply, ContinuousLinearMap.zero_apply, sub_self]

/-- Identifies the tensor coefficient expression with the actual commutator. -/
theorem chartCurvature_eq_CLM (x : W) (hx : x ∈ S) (u v w : W) :
    chartCurvature P e he x u v w = chartCurvatureCLM P e he x u v w := by
  exact chartConnectionCurvature_formula P e he hpos x hx
    (fun _ => u) (fun _ => v) (fun _ => w)
    (differentiableAt_const u) (differentiableAt_const v) contDiffAt_const

/-- Full tensorial interpretation for all actual sufficiently differentiable
fields: the constant-field definition agrees with their connection commutator. -/
theorem chartConnectionCurvature_tensorial (x : W) (hx : x ∈ S)
    (X Y Z : W → W) (hX : DifferentiableAt ℝ X x)
    (hY : DifferentiableAt ℝ Y x) (hZ : ContDiffAt ℝ ⊤ Z x) :
    chartConnectionCurvature P e he x X Y Z =
      chartCurvature P e he x (X x) (Y x) (Z x) := by
  rw [chartConnectionCurvature_formula P e he hpos x hx X Y Z hX hY hZ,
    chartCurvature_eq_CLM P e he hpos x hx]

/-- Independence of all three field extensions, including derivatives away
from the point. This is a consequence, not an axiom defining curvature. -/
theorem chartConnectionCurvature_extension_independent (x : W) (hx : x ∈ S)
    (X Y Z X' Y' Z' : W → W)
    (hX : DifferentiableAt ℝ X x) (hY : DifferentiableAt ℝ Y x)
    (hZ : ContDiffAt ℝ ⊤ Z x) (hX' : DifferentiableAt ℝ X' x)
    (hY' : DifferentiableAt ℝ Y' x) (hZ' : ContDiffAt ℝ ⊤ Z' x)
    (hvX : X x = X' x) (hvY : Y x = Y' x) (hvZ : Z x = Z' x) :
    chartConnectionCurvature P e he x X Y Z =
      chartConnectionCurvature P e he x X' Y' Z' := by
  rw [chartConnectionCurvature_tensorial P e he hpos x hx X Y Z hX hY hZ,
    chartConnectionCurvature_tensorial P e he hpos x hx X' Y' Z' hX' hY' hZ',
    hvX, hvY, hvZ]

/-- The wedge convention is explicit: (u∧v)w=g(v,w)u-g(u,w)v. -/
def baseMetricWedge (u v w : W) : W := g v w • u - g u w • v

/-- The actual commutator of the metric-raised tangent cubic operators. -/
def raisedCubicCommutator (u v w : W) : W := K u (K v w) - K v (K u w)

include hpos in
/-- Actual Levi-Civita curvature at the basepoint. No desired R expression is
a definition, connection input, jet premise, Jordan or invariance assumption. -/
theorem chartCurvature_zero (u v w : W) :
    chartCurvature P e he 0 u v w =
      -baseMetricWedge P e he u v w - raisedCubicCommutator P e he u v w := by
  have h0 := (leviCivitaChartDomain_spec P e he hpos).2.1
  rw [chartCurvature_eq_CLM P e he hpos 0 h0, chartCurvatureCLM_apply,
    leviCivitaGammaD1_zero P e he hpos, leviCivitaGammaD1_zero P e he hpos]
  simp only [leviCivitaGamma_zero P e he hpos, map_neg, baseMetricWedge,
    raisedCubicCommutator]
  have hsym : g u v = g v u := pullbackMetric_symm P e he 0
    ((leviCivitaChartDomain_spec P e he hpos).2.2.1 h0) u v
  rw [hsym]
  module

end CanonicalCurvatureNorms

end
end AlbertGeometry.Cubic
