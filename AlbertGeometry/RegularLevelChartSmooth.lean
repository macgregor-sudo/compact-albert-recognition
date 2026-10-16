/-
The genuine normal-chart derivative is invertible
at every point with nonzero normal derivative. A fixed restriction of the actual
inverse-theorem chart is smooth throughout its actual open level-chart domain.
No inverse, chart jet, metric or curvature conclusion is supplied as input.
-/
module

public import AlbertGeometry.RegularLevelChart
public import AlbertGeometry.LogHessianPositiveNeighborhood
public import Mathlib.Topology.OpenPartialHomeomorph.IsImage
public import Mathlib.Tactic.FieldSimp

@[expose] public section
open scoped ContDiff Topology

namespace AlbertGeometry.Cubic
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The fixed projection is the identity on the actual basepoint tangent kernel. -/
theorem tangentProjection_tangent (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) (v : tangentSpace P e) :
    tangentProjection P e he (v : E) = v := by
  have hv : fderiv ℝ (diagonalCubic P.form) e (v : E) = 0 := v.property
  apply Subtype.ext
  simp only [tangentProjection_coe, hv, zero_div, zero_smul, sub_zero]

/-- The actual normal-chart derivative at an arbitrary ambient point. -/
theorem hasFDerivAt_normalChartMap_at (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) (x : E) :
    HasFDerivAt (normalChartMap P e he)
      ((fderiv ℝ (diagonalCubic P.form) x).prod (tangentProjection P e he)) x := by
  have hN := (hasFDerivAt_diagonalCubic P.form x).congr_fderiv
    (fderiv_diagonalCubic P.form x).symm
  exact hN.prodMk (tangentProjection P e he).hasFDerivAt

/-- The inverse formula uses the actual derivative at x and the fixed tangent
projection at e. It is a function to be proved inverse, not an inverse premise. -/
def normalDerivativeInverse (P : SymmetricTrilinearForm E) (e x : E)
    (p : ℝ × tangentSpace P e) : E :=
  (p.2 : E) +
    ((p.1 - fderiv ℝ (diagonalCubic P.form) x (p.2 : E)) /
      fderiv ℝ (diagonalCubic P.form) x e) • e

theorem normalDerivative_left_inverse (P : SymmetricTrilinearForm E) (e x : E)
    (he : diagonalCubic P.form e = 1)
    (hx : fderiv ℝ (diagonalCubic P.form) x e ≠ 0) (w : E) :
    normalDerivativeInverse P e x
      (fderiv ℝ (diagonalCubic P.form) x w, tangentProjection P e he w) = w := by
  have hproj : fderiv ℝ (diagonalCubic P.form) x
      (tangentProjection P e he w : E) =
      fderiv ℝ (diagonalCubic P.form) x w -
        (fderiv ℝ (diagonalCubic P.form) e w / 3) *
          fderiv ℝ (diagonalCubic P.form) x e := by
    simp only [tangentProjection_coe, map_sub, map_smul, smul_eq_mul]
  have hcoef :
      (fderiv ℝ (diagonalCubic P.form) x w -
        fderiv ℝ (diagonalCubic P.form) x (tangentProjection P e he w : E)) /
          fderiv ℝ (diagonalCubic P.form) x e =
        fderiv ℝ (diagonalCubic P.form) e w / 3 := by
    rw [hproj]
    field_simp [hx] <;> ring
  simp only [normalDerivativeInverse]
  rw [hcoef]
  simp only [tangentProjection_coe]
  module

theorem normalDerivative_right_inverse (P : SymmetricTrilinearForm E) (e x : E)
    (he : diagonalCubic P.form e = 1)
    (hx : fderiv ℝ (diagonalCubic P.form) x e ≠ 0)
    (p : ℝ × tangentSpace P e) :
    (fderiv ℝ (diagonalCubic P.form) x (normalDerivativeInverse P e x p),
      tangentProjection P e he (normalDerivativeInverse P e x p)) = p := by
  have hn : fderiv ℝ (diagonalCubic P.form) x
      (normalDerivativeInverse P e x p) = p.1 := by
    simp only [normalDerivativeInverse, map_add, map_smul, smul_eq_mul]
    field_simp [hx] <;> ring
  apply Prod.ext hn
  simp only [normalDerivativeInverse, map_add, map_smul,
    tangentProjection_tangent, tangentProjection_basepoint, smul_zero, add_zero]

/-- Continuous invertibility of the actual derivative, with proved explicit
inverse laws. No extra inverse or regularity fields are assumptions. -/
def normalDerivativeSplit (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) (x : E)
    (hx : fderiv ℝ (diagonalCubic P.form) x e ≠ 0) :
    E ≃L[ℝ] ℝ × tangentSpace P e :=
  { ((fderiv ℝ (diagonalCubic P.form) x).prod
      (tangentProjection P e he)).toLinearMap with
    invFun := normalDerivativeInverse P e x
    left_inv := normalDerivative_left_inverse P e x he hx
    right_inv := normalDerivative_right_inverse P e x he hx
    continuous_toFun :=
      (fderiv ℝ (diagonalCubic P.form) x).continuous.prodMk
        (tangentProjection P e he).continuous
    continuous_invFun :=
      (continuous_subtype_val.comp continuous_snd).add
        (((continuous_fst.sub
          ((fderiv ℝ (diagonalCubic P.form) x).continuous.comp
            (continuous_subtype_val.comp continuous_snd))).div_const
          (fderiv ℝ (diagonalCubic P.form) x e)).smul continuous_const) }

@[simp] theorem normalDerivativeSplit_apply (P : SymmetricTrilinearForm E)
    (e : E) (he : diagonalCubic P.form e = 1) (x : E)
    (hx : fderiv ℝ (diagonalCubic P.form) x e ≠ 0) (w : E) :
    normalDerivativeSplit P e he x hx w =
      (fderiv ℝ (diagonalCubic P.form) x w, tangentProjection P e he w) := rfl

theorem hasFDerivAt_normalChartMap_split (P : SymmetricTrilinearForm E)
    (e : E) (he : diagonalCubic P.form e = 1) (x : E)
    (hx : fderiv ℝ (diagonalCubic P.form) x e ≠ 0) :
    HasFDerivAt (normalChartMap P e he)
      (normalDerivativeSplit P e he x hx : E →L[ℝ] (ℝ × tangentSpace P e)) x :=
  hasFDerivAt_normalChartMap_at P e he x

/-- This open set is defined by an actual derivative evaluation, not by desired
chart regularity. Its openness uses continuity of the true DN map. -/
def normalNonzeroLocus (P : SymmetricTrilinearForm E) (e : E) : Set E :=
  {x | fderiv ℝ (diagonalCubic P.form) x e ≠ 0}

theorem isOpen_normalNonzeroLocus (P : SymmetricTrilinearForm E) (e : E) :
    IsOpen (normalNonzeroLocus P e) :=
  isOpen_ne.preimage ((continuous_fderiv_diagonalCubic P).clm_apply continuous_const)

theorem basepoint_mem_normalNonzeroLocus (P : SymmetricTrilinearForm E)
    (e : E) (he : diagonalCubic P.form e = 1) : e ∈ normalNonzeroLocus P e := by
  change fderiv ℝ (diagonalCubic P.form) e e ≠ 0
  rw [fderiv_diagonalCubic_at_one P.form e he]
  norm_num

/-- Normed tangent structures are inherited from the actual submodule. Ambient
completeness also supplies tangent completeness because the true DN kernel is
closed; no extra tangent completeness assumption is needed. -/
theorem tangentSpace_isClosed (P : SymmetricTrilinearForm E) (e : E) :
    IsClosed (tangentSpace P e : Set E) :=
  (fderiv ℝ (diagonalCubic P.form) e).isClosed_ker

theorem completeSpace_tangentSpace [CompleteSpace E]
    (P : SymmetricTrilinearForm E) (e : E) : CompleteSpace (tangentSpace P e) := by
  unfold tangentSpace
  infer_instance

variable [CompleteSpace E]

/-- Restrict the actual C1 inverse-theorem chart to the proved open nonzero
normal locus. This is one fixed chart, independent of differentiation order. -/
def regularSmoothLevelChart (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) :
    OpenPartialHomeomorph E (ℝ × tangentSpace P e) :=
  (regularLevelChart P e he).restrOpen (normalNonzeroLocus P e)
    (isOpen_normalNonzeroLocus P e)

@[simp] theorem regularSmoothLevelChart_apply (P : SymmetricTrilinearForm E)
    (e x : E) (he : diagonalCubic P.form e = 1) :
    regularSmoothLevelChart P e he x = normalChartMap P e he x := rfl

theorem regularSmoothLevelChart_coe (P : SymmetricTrilinearForm E)
    (e : E) (he : diagonalCubic P.form e = 1) :
    (regularSmoothLevelChart P e he : E → ℝ × tangentSpace P e) =
      normalChartMap P e he := by
  funext x
  exact regularSmoothLevelChart_apply P e x he

@[simp] theorem regularSmoothLevelChart_symm_apply (P : SymmetricTrilinearForm E)
    (e : E) (he : diagonalCubic P.form e = 1) (y : ℝ × tangentSpace P e) :
    (regularSmoothLevelChart P e he).symm y = (regularLevelChart P e he).symm y := rfl

theorem regularSmoothLevelChart_source (P : SymmetricTrilinearForm E)
    (e : E) (he : diagonalCubic P.form e = 1) :
    (regularSmoothLevelChart P e he).source =
      (regularLevelChart P e he).source ∩ normalNonzeroLocus P e := rfl

theorem regularSmoothLevelChart_target (P : SymmetricTrilinearForm E)
    (e : E) (he : diagonalCubic P.form e = 1) :
    (regularSmoothLevelChart P e he).target =
      (regularLevelChart P e he).target ∩
        (regularLevelChart P e he).symm ⁻¹' normalNonzeroLocus P e := rfl

theorem regularSmoothLevelChart_basepoint_mem (P : SymmetricTrilinearForm E)
    (e : E) (he : diagonalCubic P.form e = 1) :
    e ∈ (regularSmoothLevelChart P e he).source := by
  rw [regularSmoothLevelChart_source]
  exact ⟨regularLevelChart_basepoint_mem P e he, basepoint_mem_normalNonzeroLocus P e he⟩

/-- At every actual inverse point, use the proved derivative equivalence and
smoothness of the genuine forward map to obtain inverse smoothness. -/
theorem contDiffAt_regularSmoothLevelChart_symm (P : SymmetricTrilinearForm E)
    (e : E) (he : diagonalCubic P.form e = 1) (n : ℕ∞ω)
    (y : ℝ × tangentSpace P e) (hy : y ∈ (regularSmoothLevelChart P e he).target) :
    ContDiffAt ℝ n (regularSmoothLevelChart P e he).symm y := by
  have hsource := (regularSmoothLevelChart P e he).map_target hy
  rw [regularSmoothLevelChart_source] at hsource
  have hx : fderiv ℝ (diagonalCubic P.form)
      ((regularSmoothLevelChart P e he).symm y) e ≠ 0 := hsource.2
  have hd : HasFDerivAt (regularSmoothLevelChart P e he)
      (normalDerivativeSplit P e he ((regularSmoothLevelChart P e he).symm y) hx :
        E →L[ℝ] (ℝ × tangentSpace P e)) ((regularSmoothLevelChart P e he).symm y) :=
    by simpa only [regularSmoothLevelChart_coe] using
      hasFDerivAt_normalChartMap_split P e he
        ((regularSmoothLevelChart P e he).symm y) hx
  have hs : ContDiffAt ℝ n (regularSmoothLevelChart P e he)
      ((regularSmoothLevelChart P e he).symm y) :=
    by simpa only [regularSmoothLevelChart_coe] using
      (contDiff_normalChartMap P e he n).contDiffAt
  exact (regularSmoothLevelChart P e he).contDiffAt_symm hy hd hs

/-- The level-domain is selected from the actual restricted chart target. -/
def smoothLevelChartDomain (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) : Set (tangentSpace P e) :=
  {v | (1, v) ∈ (regularSmoothLevelChart P e he).target}

theorem isOpen_smoothLevelChartDomain (P : SymmetricTrilinearForm E)
    (e : E) (he : diagonalCubic P.form e = 1) :
    IsOpen (smoothLevelChartDomain P e he) :=
  (regularSmoothLevelChart P e he).open_target.preimage
    (continuous_const.prodMk continuous_id)

theorem zero_mem_smoothLevelChartDomain (P : SymmetricTrilinearForm E)
    (e : E) (he : diagonalCubic P.form e = 1) :
    (0 : tangentSpace P e) ∈ smoothLevelChartDomain P e he := by
  have h := (regularSmoothLevelChart P e he).map_source
    (regularSmoothLevelChart_basepoint_mem P e he)
  simpa only [regularSmoothLevelChart_apply, normalChartMap_basepoint,
    smoothLevelChartDomain, Set.mem_setOf_eq] using h

theorem smoothLevelChartDomain_subset (P : SymmetricTrilinearForm E)
    (e : E) (he : diagonalCubic P.form e = 1) :
    smoothLevelChartDomain P e he ⊆ levelChartDomain P e he := by
  intro v hv
  change (1, v) ∈ (regularSmoothLevelChart P e he).target at hv
  rw [regularSmoothLevelChart_target] at hv
  exact hv.1

/-- The ORIGINAL inverse-theorem levelChartPoint is smooth on the new fixed
open domain. Only its domain is restricted; its function is unchanged. -/
theorem contDiffAt_levelChartPoint_smoothDomain (P : SymmetricTrilinearForm E)
    (e : E) (he : diagonalCubic P.form e = 1) (n : ℕ∞ω)
    (v : tangentSpace P e) (hv : v ∈ smoothLevelChartDomain P e he) :
    ContDiffAt ℝ n (levelChartPoint P e he) v := by
  have h := contDiffAt_regularSmoothLevelChart_symm P e he n (1, v) hv
  have hp : ContDiffAt ℝ n
      (fun w : tangentSpace P e => ((1 : ℝ), w)) v :=
    contDiffAt_const.prodMk contDiffAt_id
  have hcomp : ContDiffAt ℝ n
      (fun w : tangentSpace P e =>
        (regularSmoothLevelChart P e he).symm (1, w)) v :=
    h.fun_comp v hp
  have hsame : (fun w : tangentSpace P e =>
      (regularSmoothLevelChart P e he).symm (1, w)) =
      levelChartPoint P e he := by
    funext w
    change (regularSmoothLevelChart P e he).symm (1, w) =
      (regularLevelChart P e he).symm (1, w)
    exact regularSmoothLevelChart_symm_apply P e he (1, w)
  rw [hsame] at hcomp
  exact hcomp

theorem contDiffOn_levelChartPoint_smoothDomain (P : SymmetricTrilinearForm E)
    (e : E) (he : diagonalCubic P.form e = 1) (n : ℕ∞ω) :
    ContDiffOn ℝ n (levelChartPoint P e he) (smoothLevelChartDomain P e he) := by
  intro v hv
  exact (contDiffAt_levelChartPoint_smoothDomain P e he n v hv).contDiffWithinAt

/-- A genuine common smooth level-chart neighborhood, with actual level and
projection identities inherited from the actual inverse-theorem chart. -/
theorem exists_smooth_level_chart_neighborhood (P : SymmetricTrilinearForm E)
    (e : E) (he : diagonalCubic P.form e = 1) :
    ∃ U : Set (tangentSpace P e), IsOpen U ∧ 0 ∈ U ∧
      ContDiffOn ℝ ⊤ (levelChartPoint P e he) U ∧
      ∀ v ∈ U, diagonalCubic P.form (levelChartPoint P e he v) = 1 ∧
        tangentProjection P e he (levelChartPoint P e he v) = v := by
  refine ⟨smoothLevelChartDomain P e he, isOpen_smoothLevelChartDomain P e he,
    zero_mem_smoothLevelChartDomain P e he,
    contDiffOn_levelChartPoint_smoothDomain P e he ⊤, fun v hv => ?_⟩
  have hOld := smoothLevelChartDomain_subset P e he hv
  exact ⟨levelChartPoint_on_level P e he v hOld,
    levelChartPoint_projection P e he v hOld⟩

end
end AlbertGeometry.Cubic
