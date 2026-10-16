/-
Actual regular cubic level set via the inverse
function theorem. No supplied chart, prescribed jets or curvature conclusion.
This module supplies the regular level chart, not arbitrary-polynomial representation
or the full geometric recognition theorem.
-/
module

public import AlbertGeometry.CubicDerivatives
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Tactic.Module

@[expose] public section
open scoped ContDiff Topology

namespace AlbertGeometry.Cubic
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Tangents are the actual differential's kernel. -/
def tangentSpace (P : SymmetricTrilinearForm E) (e : E) : Submodule ℝ E :=
  (fderiv ℝ (diagonalCubic P.form) e).ker

/-- The explicit ambient continuous projection, before codomain restriction. -/
def tangentProjectionRaw (P : SymmetricTrilinearForm E) (e : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - (1 / 3 : ℝ) •
    (ContinuousLinearMap.toSpanSingleton ℝ e).comp
      (fderiv ℝ (diagonalCubic P.form) e)

@[simp] theorem tangentProjectionRaw_apply (P : SymmetricTrilinearForm E)
    (e x : E) : tangentProjectionRaw P e x =
      x - (fderiv ℝ (diagonalCubic P.form) e x / 3) • e := by
  simp only [tangentProjectionRaw, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_smul, div_eq_mul_inv]
  congr 2
  ring

theorem tangentProjectionRaw_mem (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) (x : E) :
    tangentProjectionRaw P e x ∈ tangentSpace P e := by
  change fderiv ℝ (diagonalCubic P.form) e (tangentProjectionRaw P e x) = 0
  rw [tangentProjectionRaw_apply, map_sub, map_smul,
    fderiv_diagonalCubic_at_one P.form e he]
  simp only [smul_eq_mul]
  ring

/-- Restriction to the actual differential kernel is proved, not assumed. -/
def tangentProjection (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) : E →L[ℝ] tangentSpace P e :=
  (tangentProjectionRaw P e).codRestrict (tangentSpace P e)
    (tangentProjectionRaw_mem P e he)

@[simp] theorem tangentProjection_coe (P : SymmetricTrilinearForm E) (e x : E)
    (he : diagonalCubic P.form e = 1) :
    (tangentProjection P e he x : E) =
      x - (fderiv ℝ (diagonalCubic P.form) e x / 3) • e :=
  tangentProjectionRaw_apply P e x

@[simp] theorem tangentProjection_basepoint (P : SymmetricTrilinearForm E)
    (e : E) (he : diagonalCubic P.form e = 1) :
    tangentProjection P e he e = 0 := by
  apply Subtype.ext
  simp only [tangentProjection_coe,
    fderiv_diagonalCubic_at_one P.form e he, div_self (by norm_num : (3 : ℝ) ≠ 0),
    one_smul, sub_self, ZeroMemClass.coe_zero]

/-- Literal inverse of the derivative split: the normal coordinate uses DN(e)=3. -/
def normalSplitInverse (P : SymmetricTrilinearForm E) (e : E)
    (p : ℝ × tangentSpace P e) : E := (p.1 / 3) • e + p.2

theorem normalSplit_left_inverse (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) (x : E) :
    normalSplitInverse P e
      (fderiv ℝ (diagonalCubic P.form) e x, tangentProjection P e he x) = x := by
  simp only [normalSplitInverse, tangentProjection_coe]
  module

theorem normalSplit_right_inverse (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) (p : ℝ × tangentSpace P e) :
    (fderiv ℝ (diagonalCubic P.form) e (normalSplitInverse P e p),
      tangentProjection P e he (normalSplitInverse P e p)) = p := by
  have hv : fderiv ℝ (diagonalCubic P.form) e (p.2 : E) = 0 := p.2.property
  have hn : fderiv ℝ (diagonalCubic P.form) e (normalSplitInverse P e p) = p.1 := by
    simp only [normalSplitInverse, map_add, map_smul,
      fderiv_diagonalCubic_at_one P.form e he, hv, smul_eq_mul]
    ring
  apply Prod.ext hn
  apply Subtype.ext
  rw [tangentProjection_coe, hn]
  simp only [normalSplitInverse]
  module

/-- The actual derivative split is a continuous linear equivalence with its
explicit inverse. Invertibility is derived from normalization and Euler. -/
def normalSplit (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) : E ≃L[ℝ] ℝ × tangentSpace P e :=
  { ((fderiv ℝ (diagonalCubic P.form) e).prod
      (tangentProjection P e he)).toLinearMap with
    invFun := normalSplitInverse P e
    left_inv := normalSplit_left_inverse P e he
    right_inv := normalSplit_right_inverse P e he
    continuous_toFun :=
      (fderiv ℝ (diagonalCubic P.form) e).continuous.prodMk
        (tangentProjection P e he).continuous
    continuous_invFun :=
      (continuous_fst.div_const (3 : ℝ)).smul continuous_const |>.add
        (continuous_subtype_val.comp continuous_snd) }

@[simp] theorem normalSplit_apply (P : SymmetricTrilinearForm E) (e x : E)
    (he : diagonalCubic P.form e = 1) :
    normalSplit P e he x =
      (fderiv ℝ (diagonalCubic P.form) e x, tangentProjection P e he x) := rfl

/-- The nonlinear chart map uses the actual cubic and the proved projection. -/
def normalChartMap (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) (x : E) : ℝ × tangentSpace P e :=
  (diagonalCubic P.form x, tangentProjection P e he x)

@[simp] theorem normalChartMap_basepoint (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) : normalChartMap P e he e = (1, 0) := by
  simp only [normalChartMap, he, tangentProjection_basepoint]

theorem contDiff_normalChartMap (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) (n : ℕ∞ω) :
    ContDiff ℝ n (normalChartMap P e he) :=
  (contDiff_diagonalCubic P.form n).prodMk (tangentProjection P e he).contDiff

theorem hasFDerivAt_normalChartMap (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) :
    HasFDerivAt (normalChartMap P e he) (normalSplit P e he : E →L[ℝ] _ ) e := by
  have hN := (hasFDerivAt_diagonalCubic P.form e).congr_fderiv
    (fderiv_diagonalCubic P.form e).symm
  exact hN.prodMk (tangentProjection P e he).hasFDerivAt

variable [CompleteSpace E]

/-- A genuine open partial homeomorphism obtained from the inverse theorem.
No partial inverse or chart laws are stored as input fields. -/
def regularLevelChart (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) :
    OpenPartialHomeomorph E (ℝ × tangentSpace P e) :=
  (contDiff_normalChartMap P e he 1).contDiffAt.toOpenPartialHomeomorph
    (normalChartMap P e he) (hasFDerivAt_normalChartMap P e he) (by norm_num)

@[simp] theorem regularLevelChart_apply (P : SymmetricTrilinearForm E)
    (e x : E) (he : diagonalCubic P.form e = 1) :
    regularLevelChart P e he x = normalChartMap P e he x := rfl

theorem regularLevelChart_basepoint_mem (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) : e ∈ (regularLevelChart P e he).source :=
  (contDiff_normalChartMap P e he 1).contDiffAt.mem_toOpenPartialHomeomorph_source
    (hasFDerivAt_normalChartMap P e he) (by norm_num)

theorem regularLevelChart_normal_mem (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) : (1, (0 : tangentSpace P e)) ∈
      (regularLevelChart P e he).target := by
  have h := (regularLevelChart P e he).map_source
    (regularLevelChart_basepoint_mem P e he)
  simpa only [regularLevelChart_apply, normalChartMap_basepoint] using h

/-- The actual level chart uses the inverse theorem's own inverse at (1,v). -/
def levelChartPoint (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) (v : tangentSpace P e) : E :=
  (regularLevelChart P e he).symm (1, v)

def levelChartDomain (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) : Set (tangentSpace P e) :=
  {v | (1, v) ∈ (regularLevelChart P e he).target}

theorem isOpen_levelChartDomain (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) : IsOpen (levelChartDomain P e he) :=
  (regularLevelChart P e he).open_target.preimage
    (continuous_const.prodMk continuous_id)

theorem zero_mem_levelChartDomain (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) : (0 : tangentSpace P e) ∈ levelChartDomain P e he :=
  regularLevelChart_normal_mem P e he

theorem levelChartPoint_on_level (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) (v : tangentSpace P e)
    (hv : v ∈ levelChartDomain P e he) : diagonalCubic P.form (levelChartPoint P e he v) = 1 := by
  have h := (regularLevelChart P e he).right_inv hv
  exact congrArg Prod.fst h

theorem levelChartPoint_projection (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) (v : tangentSpace P e)
    (hv : v ∈ levelChartDomain P e he) : tangentProjection P e he (levelChartPoint P e he v) = v := by
  have h := (regularLevelChart P e he).right_inv hv
  exact congrArg Prod.snd h

theorem levelChartPoint_zero (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) : levelChartPoint P e he 0 = e := by
  have h := (regularLevelChart P e he).left_inv
    (regularLevelChart_basepoint_mem P e he)
  simpa only [regularLevelChart_apply, normalChartMap_basepoint, levelChartPoint] using h

end
end AlbertGeometry.Cubic
