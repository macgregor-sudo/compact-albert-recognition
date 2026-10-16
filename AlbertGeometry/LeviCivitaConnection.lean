/-
A common positive domain is
produced from actual ambient positivity and the actual chart. The connection
coefficient is the inverse actual metric dual applied to the actual Koszul
covector, with torsion freedom, metric compatibility and uniqueness proved.
No connection/curvature jet or inverse field is an assumption.
-/
module

public import AlbertGeometry.PullbackMetricJets
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section
open scoped ContDiff Topology
open Filter

namespace AlbertGeometry.Cubic
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (P : SymmetricTrilinearForm E) (e : E) (he : diagonalCubic P.form e = 1)
local notation "W" => tangentSpace P e
local notation "χ" => levelChartPoint P e he
local notation "Dχ" => levelChartD1 P e he
local notation "U" => smoothLevelChartDomain P e he
local notation "G" => pullbackMetric P e he
local notation "DG" => pullbackMetricD1 P e he
local notation "DualW" => (W →L[ℝ] ℝ)

section CanonicalConnectionNorms

attribute [local instance] pullbackMetricDualNormedAddCommGroup pullbackMetricDualNormedSpace
  pullbackMetricBilinearNormedAddCommGroup pullbackMetricBilinearNormedSpace
  pullbackMetricTrilinearNormedAddCommGroup pullbackMetricTrilinearNormedSpace

local instance lcEndNormedAddCommGroup : NormedAddCommGroup (W →L[ℝ] W) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := W) (F := W) (σ₁₂ := RingHom.id ℝ)

local instance lcEndNormedSpace : NormedSpace ℝ (W →L[ℝ] W) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := W) (F := W) (σ₁₂ := RingHom.id ℝ)

local instance lcBilinearVectorNormedAddCommGroup : NormedAddCommGroup (W →L[ℝ] W →L[ℝ] W) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := W) (F := W →L[ℝ] W) (σ₁₂ := RingHom.id ℝ)

local instance lcBilinearVectorNormedSpace : NormedSpace ℝ (W →L[ℝ] W →L[ℝ] W) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := W) (F := W →L[ℝ] W) (σ₁₂ := RingHom.id ℝ)

local instance lcInverseNormedAddCommGroup : NormedAddCommGroup (DualW →L[ℝ] W) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := DualW) (F := W) (σ₁₂ := RingHom.id ℝ)

local instance lcInverseNormedSpace : NormedSpace ℝ (DualW →L[ℝ] W) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := DualW) (F := W) (σ₁₂ := RingHom.id ℝ)

/-- The actual chart derivative is injective throughout the same smooth domain. -/
theorem levelChartD1_injective (x : W) (hx : x ∈ U) : Function.Injective (Dχ x) :=
  Function.LeftInverse.injective (fun u => levelChartD1_projection P e he x hx u)

/-- Symmetry belongs to the actual pulled-back ambient metric. -/
theorem pullbackMetric_symm (x : W) (hx : x ∈ U) (u v : W) : G x u v = G x v u := by
  rw [pullbackMetric_cubic_apply P e he x hx,
    pullbackMetric_cubic_apply P e he x hx, P.swap23]

private theorem lc_eval_const_hasFDerivAt
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

private theorem lc_contDiffAt_flip
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

/-- Differentiate metric symmetry on a whole neighborhood, not just at x. -/
theorem pullbackMetricD1_slot_symm (x : W) (hx : x ∈ U) (s u v : W) :
    DG x s u v = DG x s v u := by
  have hG := hasFDerivAt_pullbackMetric P e he x hx
  have h1 := lc_eval_const_hasFDerivAt (lc_eval_const_hasFDerivAt hG u) v
  have h2 := lc_eval_const_hasFDerivAt (lc_eval_const_hasFDerivAt hG v) u
  have hc : (fun y => G y u v) =ᶠ[𝓝 x] (fun y => G y v u) :=
    Filter.mem_of_superset ((isOpen_smoothLevelChartDomain P e he).mem_nhds hx)
      (fun y hy => by
        simpa only [Set.mem_ofPred_eq] using pullbackMetric_symm P e he y hy u v)
  have h := congrArg (fun L : W →L[ℝ] ℝ => L s)
    (h1.unique (h2.congr_of_eventuallyEq hc))
  simpa only [ContinuousLinearMap.flip_apply] using h

/-- Literal Koszul covector field, bundled as a trilinear CLM using actual DG. -/
def koszulTensor (x : W) : W →L[ℝ] W →L[ℝ] DualW :=
  (1 / 2 : ℝ) • (DG x + (DG x).flip -
    ((((ContinuousLinearMap.flipₗᵢ ℝ W W ℝ).toContinuousLinearEquiv).toContinuousLinearMap :
      (W →L[ℝ] W →L[ℝ] ℝ) →L[ℝ] W →L[ℝ] W →L[ℝ] ℝ).comp
      ((DG x).flip : W →L[ℝ] W →L[ℝ] W →L[ℝ] ℝ)))

def koszulCovector (x u v : W) : DualW := koszulTensor P e he x u v

@[simp] theorem koszulCovector_apply (x u v w : W) :
    koszulCovector P e he x u v w =
      (DG x u v w + DG x v u w - DG x w u v) / 2 := by
  simp only [koszulCovector, koszulTensor, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]
  change (1 / 2 : ℝ) * (DG x u v w + DG x v u w - DG x w u v) = _
  ring

/-- Actual inverse metric raising of the Koszul covector. The total inverse is
zero off the invertible locus; every geometric statement is on the produced U+. -/
def leviCivitaGamma (x : W) : W →L[ℝ] W →L[ℝ] W :=
  (((ContinuousLinearMap.compL ℝ W DualW W :
    (DualW →L[ℝ] W) →L[ℝ] (W →L[ℝ] DualW) →L[ℝ] W →L[ℝ] W)
    ((G x).inverse : DualW →L[ℝ] W)).comp
    (koszulTensor P e he x))

@[simp] theorem leviCivitaGamma_apply (x u v : W) :
    leviCivitaGamma P e he x u v =
      (G x).inverse (koszulCovector P e he x u v) := by
  simp only [leviCivitaGamma, koszulCovector, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply]

/-- Chart-defined covariant derivative on actual vector fields. -/
def chartCovariantDerivative (x : W) (X Y : W → W) : W :=
  fderiv ℝ Y x (X x) + leviCivitaGamma P e he x (X x) (Y x)

/-- The genuine coordinate Lie bracket: difference of directional derivatives. -/
def chartLieBracket (x : W) (X Y : W → W) : W :=
  fderiv ℝ Y x (X x) - fderiv ℝ X x (Y x)

/-- ONE positive chart domain is produced, using the positive ambient neighborhood
and the true chart derivative left inverse. It is not a positivity premise. -/
theorem exists_positive_pullback_chart_domain [FiniteDimensional ℝ E]
    (hpos : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u) :
    ∃ S : Set W, IsOpen S ∧ 0 ∈ S ∧ S ⊆ U ∧
      ∀ x ∈ S, ∀ u : W, u ≠ 0 → 0 < G x u u := by
  have hN : 0 < diagonalCubic P.form e := by rw [he]; norm_num
  obtain ⟨V, hV, heV, hgood⟩ :=
    exists_positive_definite_logHessian_neighborhood P e hN hpos
  let S : Set W := U ∩ χ ⁻¹' V
  have hχ : ContinuousOn χ U :=
    (contDiffOn_levelChartPoint_smoothDomain P e he ⊤).continuousOn
  have hOpen : IsOpen S := hχ.isOpen_inter_preimage
    (isOpen_smoothLevelChartDomain P e he) hV
  have hzero : (0 : W) ∈ S := by
    refine ⟨zero_mem_smoothLevelChartDomain P e he, ?_⟩
    simpa only [Set.mem_preimage, levelChartPoint_zero] using heV
  refine ⟨S, hOpen, hzero, fun x hx => hx.1, fun x hx u hu => ?_⟩
  have hdu : Dχ x u ≠ 0 := by
    intro hz
    have h : u = 0 := (levelChartD1_injective P e he x hx.1)
      (by simpa only [map_zero] using hz)
    exact hu h
  rw [pullbackMetric_apply]
  exact (hgood (χ x) hx.2).2.2 (Dχ x u) hdu

/-- A chosen PRODUCED open neighborhood; no metric or inverse field is given. -/
def leviCivitaChartDomain [FiniteDimensional ℝ E]
    (hpos : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u) : Set W :=
  Classical.choose (exists_positive_pullback_chart_domain P e he hpos)

theorem leviCivitaChartDomain_spec [FiniteDimensional ℝ E]
    (hpos : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u) :
    IsOpen (leviCivitaChartDomain P e he hpos) ∧
      0 ∈ leviCivitaChartDomain P e he hpos ∧
      leviCivitaChartDomain P e he hpos ⊆ U ∧
      ∀ x ∈ leviCivitaChartDomain P e he hpos, ∀ u : W, u ≠ 0 → 0 < G x u u :=
  Classical.choose_spec (exists_positive_pullback_chart_domain P e he hpos)

variable [FiniteDimensional ℝ E]
variable (hpos : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u)
local notation "S" => leviCivitaChartDomain P e he hpos
local notation "Γ" => leviCivitaGamma P e he

/-- Positivity of the actual metric dual implies injectivity on the produced S. -/
theorem pullbackMetric_dual_injective (x : W) (hx : x ∈ S) :
    Function.Injective (G x) := by
  intro u v huv
  have h0 : G x (u - v) = 0 := by rw [map_sub, huv, sub_self]
  have h0' : G x (u - v) (u - v) = 0 := by rw [h0]; rfl
  have hz : u - v = 0 := by
    by_contra hne
    have hp := (leviCivitaChartDomain_spec P e he hpos).2.2.2 x hx (u - v) hne
    rw [h0'] at hp
    exact (lt_irrefl 0) hp
  exact sub_eq_zero.mp hz

/-- Equal dimensions come from the actual algebraic/continuous dual equivalence. -/
theorem tangent_continuousDual_finrank :
    Module.finrank ℝ W = Module.finrank ℝ DualW := by
  let d : Module.Dual ℝ W ≃ₗ[ℝ] DualW := LinearMap.toContinuousLinearMap
  calc
    Module.finrank ℝ W = Module.finrank ℝ (Module.Dual ℝ W) :=
      (Subspace.dual_finrank_eq (K := ℝ) (V := W)).symm
    _ = Module.finrank ℝ DualW := d.finrank_eq

/-- Improve this PARTICULAR actual injective metric map to a genuine CLEquiv. -/
def pullbackMetricDualEquiv (x : W) (hx : x ∈ S) : W ≃L[ℝ] DualW := by
  let d : Module.Dual ℝ W ≃ₗ[ℝ] DualW := LinearMap.toContinuousLinearMap
  letI : FiniteDimensional ℝ DualW := d.finiteDimensional
  exact (LinearEquiv.ofInjectiveOfFinrankEq (G x).toLinearMap
    (pullbackMetric_dual_injective P e he hpos x hx)
    (tangent_continuousDual_finrank P e)).toContinuousLinearEquiv

theorem pullbackMetric_dual_isInvertible (x : W) (hx : x ∈ S) :
    (G x).IsInvertible :=
  ⟨pullbackMetricDualEquiv P e he hpos x hx, rfl⟩

/-- Actual Koszul identity holds throughout S before any Γ differentiation. -/
theorem leviCivitaGamma_koszul (x : W) (hx : x ∈ S) (u v w : W) :
    G x (Γ x u v) w = koszulCovector P e he x u v w := by
  rw [leviCivitaGamma_apply]
  exact congrArg (fun L : DualW => L w)
    ((pullbackMetric_dual_isInvertible P e he hpos x hx).self_apply_inverse
      (koszulCovector P e he x u v))

/-- The proved Koszul identity holds in a full neighborhood before any Γ jet. -/
theorem eventually_leviCivitaGamma_koszul (x : W) (hx : x ∈ S) (u v w : W) :
    ∀ᶠ y in 𝓝 x, G y (Γ y u v) w = koszulCovector P e he y u v w :=
  Filter.mem_of_superset ((leviCivitaChartDomain_spec P e he hpos).1.mem_nhds hx)
    (fun y hy => by
      simpa only [Set.mem_ofPred_eq] using
        leviCivitaGamma_koszul P e he hpos y hy u v w)

/-- Torsion-free coordinate coefficients on the actual common domain. -/
theorem leviCivitaGamma_symm (x : W) (hx : x ∈ S) (u v : W) :
    Γ x u v = Γ x v u := by
  have hxU := (leviCivitaChartDomain_spec P e he hpos).2.2.1 hx
  apply pullbackMetric_dual_injective P e he hpos x hx
  ext w
  rw [leviCivitaGamma_koszul P e he hpos x hx,
    leviCivitaGamma_koszul P e he hpos x hx,
    koszulCovector_apply P e he x u v w, koszulCovector_apply P e he x v u w]
  have h := pullbackMetricD1_slot_symm P e he x hxU w u v
  linarith

/-- Actual metric compatibility throughout S, not a supplied Γ identity. -/
theorem leviCivitaGamma_metricCompatibility (x : W) (hx : x ∈ S) (u v w : W) :
    DG x u v w = G x (Γ x u v) w + G x v (Γ x u w) := by
  have hxU := (leviCivitaChartDomain_spec P e he hpos).2.2.1 hx
  rw [pullbackMetric_symm P e he x hxU v (Γ x u w),
    leviCivitaGamma_koszul P e he hpos x hx,
    leviCivitaGamma_koszul P e he hpos x hx,
    koszulCovector_apply P e he x u v w, koszulCovector_apply P e he x u w v]
  have h1 := pullbackMetricD1_slot_symm P e he x hxU u w v
  have h2 := pullbackMetricD1_slot_symm P e he x hxU v u w
  have h3 := pullbackMetricD1_slot_symm P e he x hxU w u v
  linarith

/-- Uniqueness follows from positivity and the two actual connection laws.
The competitor is arbitrary; these laws are NOT inputs to our Γ construction. -/
theorem leviCivitaGamma_unique (x : W) (hx : x ∈ S) (H : W → W → W)
    (hTor : ∀ u v, H u v = H v u)
    (hMet : ∀ u v w, DG x u v w = G x (H u v) w + G x v (H u w)) :
    ∀ u v, H u v = Γ x u v := by
  have hxU := (leviCivitaChartDomain_spec P e he hpos).2.2.1 hx
  intro u v
  apply pullbackMetric_dual_injective P e he hpos x hx
  ext w
  rw [leviCivitaGamma_koszul P e he hpos x hx, koszulCovector_apply P e he x u v w]
  have h1 := hMet u v w
  have h2 := hMet v u w
  have h3 := hMet w u v
  rw [pullbackMetric_symm P e he x hxU v (H u w)] at h1
  rw [hTor v u, pullbackMetric_symm P e he x hxU u (H v w)] at h2
  rw [hTor w u, hTor w v, pullbackMetric_symm P e he x hxU u (H v w)] at h3
  linarith

/-- Smooth actual inverse on S, obtained from official finite inverse calculus. -/
theorem contDiffAt_pullbackMetric_inverse (x : W) (hx : x ∈ S) :
    ContDiffAt ℝ ⊤ (fun y => (G y).inverse) x := by
  have hxU := (leviCivitaChartDomain_spec P e he hpos).2.2.1 hx
  have hi : ContDiffAt ℝ ⊤
      (ContinuousLinearMap.inverse : (W →L[ℝ] DualW) → (DualW →L[ℝ] W)) (G x) :=
    ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse (𝕜 := ℝ)
      (E := W) (F := DualW) (n := ⊤)
      (pullbackMetric_dual_isInvertible P e he hpos x hx)
  exact ContDiffAt.fun_comp (𝕜 := ℝ) (E := W) (F := W →L[ℝ] DualW)
    («G» := DualW →L[ℝ] W) (n := ⊤)
    (g := ContinuousLinearMap.inverse) (f := pullbackMetric P e he) x hi
    (contDiffAt_pullbackMetric P e he x hxU)

/-- Smooth Koszul tensor on the same domain, using actual DG smoothness. -/
theorem contDiffAt_koszulTensor (x : W) (hx : x ∈ S) :
    ContDiffAt ℝ ⊤ (koszulTensor P e he) x := by
  have hxU := (leviCivitaChartDomain_spec P e he hpos).2.2.1 hx
  have hD : ContDiffAt ℝ ⊤ DG x :=
    ContDiffAt.fderiv_right (𝕜 := ℝ) (E := W) (F := W →L[ℝ] DualW)
      (f := pullbackMetric P e he) (x₀ := x) (n := ⊤) (m := ⊤)
      (contDiffAt_pullbackMetric P e he x hxU) (by simp)
  have hflip : ContDiffAt ℝ ⊤ (fun y : W => (DG y).flip) x :=
    lc_contDiffAt_flip (X := W) (Y := W) (Z := W) (F := DualW)
      (f := pullbackMetricD1 P e he) (x := x) hD
  let L : (W →L[ℝ] DualW) →L[ℝ] W →L[ℝ] DualW :=
    ((ContinuousLinearMap.flipₗᵢ ℝ W W ℝ).toContinuousLinearEquiv).toContinuousLinearMap
  have hL : ContDiffAt ℝ ⊤ (fun _ : W => L) x := contDiffAt_const
  have hcycle : ContDiffAt ℝ ⊤ (fun y : W => L.comp (DG y).flip) x :=
    ContDiffAt.clm_comp (𝕜 := ℝ) (X := W) (E := W) (F := W →L[ℝ] DualW)
      («G» := W →L[ℝ] DualW) (n := ⊤)
      (g := fun _ : W => L) (f := fun y : W => (DG y).flip) (x := x) hL hflip
  exact ((hD.add hflip).sub hcycle).const_smul (1 / 2 : ℝ)

/-- The actual bilinear Γ FIELD is smooth throughout the ONE produced S.
No derivative of Γ is taken before these neighborhood laws and smoothness. -/
theorem contDiffAt_leviCivitaGamma (x : W) (hx : x ∈ S) : ContDiffAt ℝ ⊤ Γ x := by
  have hi : ContDiffAt ℝ ⊤ (fun y : W => (G y).inverse) x :=
    contDiffAt_pullbackMetric_inverse P e he hpos x hx
  have hcomp : ContDiff ℝ ⊤
      (ContinuousLinearMap.compL ℝ W DualW W :
        (DualW →L[ℝ] W) → ((W →L[ℝ] DualW) →L[ℝ] W →L[ℝ] W)) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := DualW →L[ℝ] W)
      (F := (W →L[ℝ] DualW) →L[ℝ] W →L[ℝ] W) (n := ⊤)
      (ContinuousLinearMap.compL ℝ W DualW W)
  have hleft : ContDiffAt ℝ ⊤
      (fun y : W => ContinuousLinearMap.compL ℝ W DualW W (G y).inverse) x :=
    ContDiffAt.fun_comp (𝕜 := ℝ) (E := W) (F := DualW →L[ℝ] W)
      («G» := (W →L[ℝ] DualW) →L[ℝ] W →L[ℝ] W) (n := ⊤)
      (g := ContinuousLinearMap.compL ℝ W DualW W)
      (f := fun y : W => (G y).inverse) x hcomp.contDiffAt hi
  exact ContDiffAt.clm_comp (𝕜 := ℝ) (X := W) (E := W) (F := W →L[ℝ] DualW)
    («G» := W →L[ℝ] W) (n := ⊤)
    (g := fun y : W => ContinuousLinearMap.compL ℝ W DualW W (G y).inverse)
    (f := koszulTensor P e he) (x := x) hleft
    (contDiffAt_koszulTensor P e he hpos x hx)

theorem contDiffOn_leviCivitaGamma : ContDiffOn ℝ ⊤ Γ S :=
  fun x hx => (contDiffAt_leviCivitaGamma P e he hpos x hx).contDiffWithinAt

/-- The constructed derivative sends actual smooth vector fields to smooth fields. -/
theorem contDiffAt_chartCovariantDerivative (x : W) (hx : x ∈ S)
    (X Y : W → W) (hX : ContDiffAt ℝ ⊤ X x) (hY : ContDiffAt ℝ ⊤ Y x) :
    ContDiffAt ℝ ⊤ (fun y => chartCovariantDerivative P e he y X Y) x := by
  have hDY : ContDiffAt ℝ ⊤ (fderiv ℝ Y) x := hY.fderiv_right (by simp)
  have hGamma := (contDiffAt_leviCivitaGamma P e he hpos x hx).clm_apply hX
  exact (hDY.clm_apply hX).add (hGamma.clm_apply hY)

/-- Metric compatibility on actual differentiable vector fields. -/
theorem chartCovariantDerivative_metric (x : W) (hx : x ∈ S)
    (X Y Z : W → W) (hY : DifferentiableAt ℝ Y x) (hZ : DifferentiableAt ℝ Z x) :
    fderiv ℝ (fun y => G y (Y y) (Z y)) x (X x) =
      G x (chartCovariantDerivative P e he x X Y) (Z x) +
        G x (Y x) (chartCovariantDerivative P e he x X Z) := by
  have hxU := (leviCivitaChartDomain_spec P e he hpos).2.2.1 hx
  have hd : HasFDerivAt (fun y : W => G y (Y y) (Z y))
      ((G x (Y x)).comp (fderiv ℝ Z x) +
        ((G x).comp (fderiv ℝ Y x) + (DG x).flip (Y x)).flip (Z x)) x := by
    exact ((hasFDerivAt_pullbackMetric P e he x hxU).clm_apply
      hY.hasFDerivAt).clm_apply hZ.hasFDerivAt
  have hv : fderiv ℝ (fun y => G y (Y y) (Z y)) x (X x) =
      G x (Y x) (fderiv ℝ Z x (X x)) +
        (G x (fderiv ℝ Y x (X x)) (Z x) + DG x (X x) (Y x) (Z x)) := by
    have heval := congrArg (fun L : W →L[ℝ] ℝ => L (X x)) hd.fderiv
    simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply] using heval
  rw [hv]
  simp only [chartCovariantDerivative, map_add, ContinuousLinearMap.add_apply]
  have h := leviCivitaGamma_metricCompatibility P e he hpos x hx (X x) (Y x) (Z x)
  linarith

/-- Actual torsion vanishes for the actual coordinate Lie bracket. -/
theorem chartCovariantDerivative_torsion (x : W) (hx : x ∈ S) (X Y : W → W) :
    chartCovariantDerivative P e he x X Y - chartCovariantDerivative P e he x Y X =
      chartLieBracket P e x X Y := by
  simp only [chartCovariantDerivative, chartLieBracket]
  rw [leviCivitaGamma_symm P e he hpos x hx (X x) (Y x)]
  module

/-- Additivity in the direction field is pointwise actual CLM linearity. -/
theorem chartCovariantDerivative_add_direction (x : W) (X Z Y : W → W) :
    chartCovariantDerivative P e he x (fun y => X y + Z y) Y =
      chartCovariantDerivative P e he x X Y + chartCovariantDerivative P e he x Z Y := by
  simp only [chartCovariantDerivative, map_add, ContinuousLinearMap.add_apply]
  module

/-- C∞-function linearity in the direction field is pointwise actual bilinearity. -/
theorem chartCovariantDerivative_smul_direction (x : W) (f : W → ℝ) (X Y : W → W) :
    chartCovariantDerivative P e he x (fun y => f y • X y) Y =
      f x • chartCovariantDerivative P e he x X Y := by
  simp only [chartCovariantDerivative, map_smul, ContinuousLinearMap.smul_apply, smul_add]

/-- Additivity in the differentiated field uses its genuine derivative certificate. -/
theorem chartCovariantDerivative_add_field (x : W) (X Y Z : W → W)
    (hY : DifferentiableAt ℝ Y x) (hZ : DifferentiableAt ℝ Z x) :
    chartCovariantDerivative P e he x X (fun y => Y y + Z y) =
      chartCovariantDerivative P e he x X Y + chartCovariantDerivative P e he x X Z := by
  -- Typed derivative function in the literal lambda form of the goal (`fderiv_fun_add`).
  have hd : fderiv ℝ (fun y => Y y + Z y) x = fderiv ℝ Y x + fderiv ℝ Z x :=
    fderiv_fun_add hY hZ
  -- Evaluate the derivative identity at the direction vector `X x`.
  have hv : fderiv ℝ (fun y => Y y + Z y) x (X x) =
      fderiv ℝ Y x (X x) + fderiv ℝ Z x (X x) := by
    have heval := congrArg (fun L : W →L[ℝ] W => L (X x)) hd
    simpa only [add_apply] using heval
  -- Additivity of the actual coefficient map in its second slot.
  have hg : leviCivitaGamma P e he x (X x) (Y x + Z x) =
      leviCivitaGamma P e he x (X x) (Y x) + leviCivitaGamma P e he x (X x) (Z x) :=
    map_add (leviCivitaGamma P e he x (X x)) (Y x) (Z x)
  show fderiv ℝ (fun y => Y y + Z y) x (X x) + leviCivitaGamma P e he x (X x) (Y x + Z x) =
    (fderiv ℝ Y x (X x) + leviCivitaGamma P e he x (X x) (Y x)) +
      (fderiv ℝ Z x (X x) + leviCivitaGamma P e he x (X x) (Z x))
  rw [hv, hg]
  exact add_add_add_comm (fderiv ℝ Y x (X x)) (fderiv ℝ Z x (X x))
    (leviCivitaGamma P e he x (X x) (Y x)) (leviCivitaGamma P e he x (X x) (Z x))

/-- Leibniz in the differentiated field uses the ACTUAL scalar/vector product rule. -/
theorem chartCovariantDerivative_leibniz (x : W) (f : W → ℝ) (X Y : W → W)
    (hf : DifferentiableAt ℝ f x) (hY : DifferentiableAt ℝ Y x) :
    chartCovariantDerivative P e he x X (fun y => f y • Y y) =
      fderiv ℝ f x (X x) • Y x + f x • chartCovariantDerivative P e he x X Y := by
  -- Typed derivative function in the literal lambda form of the goal (`fderiv_fun_smul`).
  have hd : fderiv ℝ (fun y => f y • Y y) x =
      f x • fderiv ℝ Y x + (fderiv ℝ f x).smulRight (Y x) :=
    fderiv_fun_smul hf hY
  -- Evaluate the product rule at the direction vector `X x`.
  have hv : fderiv ℝ (fun y => f y • Y y) x (X x) =
      f x • fderiv ℝ Y x (X x) + fderiv ℝ f x (X x) • Y x := by
    have heval := congrArg (fun L : W →L[ℝ] W => L (X x)) hd
    simpa only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply] using heval
  -- Real homogeneity of the actual coefficient map in its second slot.
  have hg : leviCivitaGamma P e he x (X x) (f x • Y x) =
      f x • leviCivitaGamma P e he x (X x) (Y x) :=
    map_smul (leviCivitaGamma P e he x (X x)) (f x) (Y x)
  -- Distributivity of the real scalar over the vector sum.
  have hs : f x • (fderiv ℝ Y x (X x) + leviCivitaGamma P e he x (X x) (Y x)) =
      f x • fderiv ℝ Y x (X x) + f x • leviCivitaGamma P e he x (X x) (Y x) :=
    smul_add (f x) (fderiv ℝ Y x (X x)) (leviCivitaGamma P e he x (X x) (Y x))
  show fderiv ℝ (fun y => f y • Y y) x (X x) + leviCivitaGamma P e he x (X x) (f x • Y x) =
    fderiv ℝ f x (X x) • Y x +
      f x • (fderiv ℝ Y x (X x) + leviCivitaGamma P e he x (X x) (Y x))
  rw [hv, hg, hs]
  exact (add_assoc (f x • fderiv ℝ Y x (X x)) (fderiv ℝ f x (X x) • Y x)
      (f x • leviCivitaGamma P e he x (X x) (Y x))).trans
    (add_left_comm (f x • fderiv ℝ Y x (X x)) (fderiv ℝ f x (X x) • Y x)
      (f x • leviCivitaGamma P e he x (X x) (Y x)))

end CanonicalConnectionNorms
end
end AlbertGeometry.Cubic
