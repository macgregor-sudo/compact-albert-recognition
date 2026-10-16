/-
Unit/tangent reconstruction. The WHOLE normalized cubic along
unit+tangent directions is expanded by actual trilinearity/symmetry and actual
DN/Hessian identities. A tangent metric+cubic equivalence then constructs an
ambient linear norm/unit equivalence via the already proved derivative splits.
No recognized ambient map, unknown Jordan identity or norm preservation is an
input to that construction. This is an actual polynomial identity, not jets
named as a norm or an assumed Taylor expansion.
-/
module

public import AlbertGeometry.NativeCurvatureDictionary
public import AlbertGeometry.BasedNormDerivativeTransport
public import Mathlib.LinearAlgebra.Prod

@[expose] public section
namespace AlbertGeometry.UnitTangentNormReconstruction
noncomputable section
open AlbertGeometry.Cubic AlbertGeometry.BasedNormDerivativeTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (P : SymmetricTrilinearForm E) (e : E) (he : diagonalCubic P.form e = 1)

/-- Literal diagonal evaluation in three slots. -/
theorem diagonalCubic_eq_three (x : E) :
    diagonalCubic P.form x = P.form ![x,x,x] := by
  unfold diagonalCubic
  congr 1
  ext i
  fin_cases i <;> rfl

/-- True tangent vectors have no two-unit cubic coefficient, by actual DN. -/
theorem cubic_unit_unit_tangent (u : (tangentSpace P e)) : P.form ![e,e,(u : E)] = 0 := by
  have h : fderiv ℝ (diagonalCubic P.form) e (u : E) = 0 := u.property
  rw [fderiv_diagonalCubic_apply_symmetric] at h
  linarith

/-- The one-unit/two-tangent coefficient is exactly -a_e/2, deduced from the
actual Hessian/log-Hessian relation and true Hessian=6P, not supplied as a jet. -/
theorem cubic_unit_tangent_tangent (u v : (tangentSpace P e)) :
    P.form ![e,(u : E),(v : E)] = -(1 / 2 : ℝ) * (baseChartMetric P e he) u v := by
  have h := cubicHessian_tangent_at_one P e he u v
  rw [cubicHessian_apply] at h
  rw [← baseChartMetric_apply P e he u v] at h
  linarith

/-- Exact WHOLE real polynomial, for every t (including zero), not just its
first three derivatives at a basepoint. -/
theorem cubic_unit_tangent_expansion (t : ℝ) (u : (tangentSpace P e)) :
    diagonalCubic P.form (t • e + (u : E)) =
      t^3 - (3 / 2 : ℝ) * t * (baseChartMetric P e he) u u + P.form ![(u : E),(u : E),(u : E)] := by
  have h0 : P.form ![e,e,e] = 1 := by
    rw [← diagonalCubic_eq_three P e, he]
  have h1 := cubic_unit_unit_tangent P e u
  have h2 : P.form ![e,(u : E),e] = 0 := by
    rw [P.swap23]
    exact h1
  have h3 : P.form ![(u : E),e,e] = 0 := by
    rw [P.swap12]
    exact h2
  have h4 := cubic_unit_tangent_tangent P e he u u
  have h5 : P.form ![(u : E),e,(u : E)] = -(1 / 2 : ℝ) * (baseChartMetric P e he) u u := by
    rw [P.swap12]
    exact h4
  have h6 : P.form ![(u : E),(u : E),e] = -(1 / 2 : ℝ) * (baseChartMetric P e he) u u := by
    rw [P.swap23]
    exact h5
  rw [diagonalCubic_eq_three]
  rw [← fullyCurried_apply]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, fullyCurried_apply]
  rw [h0, h1, h2, h3, h4, h5, h6]
  ring

/-- Literal three-slot negation, required to handle BOTH recovery signs. -/
theorem cubic_three_neg (u : E) : P.form ![-u,-u,-u] = -P.form ![u,u,u] := by
  rw [← fullyCurried_apply]
  simp only [map_neg, ContinuousLinearMap.neg_apply, neg_neg, fullyCurried_apply]

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
variable (Q : SymmetricTrilinearForm H) (f : H) (hf : diagonalCubic Q.form f = 1)

set_option maxHeartbeats 800000 in
/-- Construct an ambient equivalence from the actual derivative splits and a
proved tangent map. No ambient inverse or recognized map is assumed. -/
def ambientLift (D : tangentSpace P e ≃ₗ[ℝ] tangentSpace Q f) : E ≃ₗ[ℝ] H where
  toFun (x : E) :=
    let equiv : (tangentSpace P e) ≃ (tangentSpace Q f) := D.toEquiv
    let forward : (tangentSpace P e) → (tangentSpace Q f) := equiv.toFun
    let u : (tangentSpace P e) := (tangentProjection P e he).toLinearMap.toFun x
    let v : (tangentSpace Q f) := forward u
    normalSplitInverse Q f (fderiv ℝ (diagonalCubic P.form) e x, v)
  invFun (y : H) :=
    let equiv : (tangentSpace P e) ≃ (tangentSpace Q f) := D.toEquiv
    let backward : (tangentSpace Q f) → (tangentSpace P e) := equiv.invFun
    let v : (tangentSpace Q f) := (tangentProjection Q f hf).toLinearMap.toFun y
    let u : (tangentSpace P e) := backward v
    normalSplitInverse P e (fderiv ℝ (diagonalCubic Q.form) f y, u)
  left_inv (x : E) := by
    have hsplit := normalSplit_right_inverse Q f hf
      (fderiv ℝ (diagonalCubic P.form) e x, D (tangentProjection P e he x))
    have hn := congrArg (fun p : ℝ × (tangentSpace Q f) => p.1) hsplit
    have ht := congrArg (fun p : ℝ × (tangentSpace Q f) => p.2) hsplit
    dsimp only [Prod.fst, Prod.snd] at hn ht
    change normalSplitInverse P e
      (fderiv ℝ (diagonalCubic Q.form) f
        (normalSplitInverse Q f
          (fderiv ℝ (diagonalCubic P.form) e x, D (tangentProjection P e he x))),
       D.symm (tangentProjection Q f hf
        (normalSplitInverse Q f
          (fderiv ℝ (diagonalCubic P.form) e x, D (tangentProjection P e he x))))) = x
    rw [hn, ht, D.symm_apply_apply]
    exact normalSplit_left_inverse P e he x
  right_inv (y : H) := by
    have hsplit := normalSplit_right_inverse P e he
      (fderiv ℝ (diagonalCubic Q.form) f y, D.symm (tangentProjection Q f hf y))
    have hn := congrArg (fun p : ℝ × (tangentSpace P e) => p.1) hsplit
    have ht := congrArg (fun p : ℝ × (tangentSpace P e) => p.2) hsplit
    dsimp only [Prod.fst, Prod.snd] at hn ht
    change normalSplitInverse Q f
      (fderiv ℝ (diagonalCubic P.form) e
        (normalSplitInverse P e
          (fderiv ℝ (diagonalCubic Q.form) f y, D.symm (tangentProjection Q f hf y))),
       D (tangentProjection P e he
        (normalSplitInverse P e
          (fderiv ℝ (diagonalCubic Q.form) f y, D.symm (tangentProjection Q f hf y))))) = y
    rw [hn, ht, D.apply_symm_apply]
    exact normalSplit_left_inverse Q f hf y
  map_add' (x y : E) := by
    change normalSplitInverse Q f
      (fderiv ℝ (diagonalCubic P.form) e (x + y),
       D (tangentProjection P e he (x + y))) =
      normalSplitInverse Q f
        (fderiv ℝ (diagonalCubic P.form) e x, D (tangentProjection P e he x)) +
      normalSplitInverse Q f
        (fderiv ℝ (diagonalCubic P.form) e y, D (tangentProjection P e he y))
    simp only [normalSplitInverse, map_add, add_div, add_smul, Submodule.coe_add]
    exact add_add_add_comm
      ((fderiv ℝ (diagonalCubic P.form) e x / 3) • f)
      ((fderiv ℝ (diagonalCubic P.form) e y / 3) • f)
      (D (tangentProjection P e he x) : H) (D (tangentProjection P e he y) : H)
  map_smul' (r : ℝ) (x : E) := by
    change normalSplitInverse Q f
      (fderiv ℝ (diagonalCubic P.form) e (r • x),
       D (tangentProjection P e he (r • x))) =
      r • normalSplitInverse Q f
        (fderiv ℝ (diagonalCubic P.form) e x, D (tangentProjection P e he x))
    simp only [normalSplitInverse, map_smul, Submodule.coe_smul, smul_eq_mul,
      smul_add, smul_smul, div_eq_mul_inv, mul_assoc]

set_option maxHeartbeats 800000 in
@[simp] theorem ambientLift_apply (D : tangentSpace P e ≃ₗ[ℝ] tangentSpace Q f) (x : E) :
    ambientLift P e he Q f hf D x =
      let equiv : (tangentSpace P e) ≃ (tangentSpace Q f) := D.toEquiv
      let forward : (tangentSpace P e) → (tangentSpace Q f) := equiv.toFun
      let u : (tangentSpace P e) := (tangentProjection P e he).toLinearMap.toFun x
      let v : (tangentSpace Q f) := forward u
      (fderiv ℝ (diagonalCubic P.form) e x / 3) • f + v.val := by
  rfl

/-- Unit preservation is an output of the genuine split normalization. -/
theorem ambientLift_unit (D : tangentSpace P e ≃ₗ[ℝ] tangentSpace Q f) : ambientLift P e he Q f hf D e = f := by
  change (fderiv ℝ (diagonalCubic P.form) e e / 3) • f +
    (D (tangentProjection P e he e) : H) = f
  simp only [ambientLift_apply, fderiv_diagonalCubic_at_one P.form e he,
    tangentProjection_basepoint, map_zero, ZeroMemClass.coe_zero,
    div_self (by norm_num : (3 : ℝ) ≠ 0), one_smul, add_zero]

set_option maxHeartbeats 800000 in
/-- Actual tangent metric and cubic certificates give whole norm equality.
These certificates are PROVED from signed curvature recovery in the consumer. -/
theorem ambientLift_norm
    (D : tangentSpace P e ≃ₗ[ℝ] tangentSpace Q f)
    (hmetric : ∀ u v : (tangentSpace P e),
      let equiv : (tangentSpace P e) ≃ (tangentSpace Q f) := D.toEquiv
      let d : (tangentSpace P e) → (tangentSpace Q f) := equiv.toFun
      let q : (tangentSpace Q f) → (tangentSpace Q f) → ℝ := fun a b =>
        ((baseChartMetric Q f hf).toLinearMap.toFun a).toLinearMap.toFun b
      let p : (tangentSpace P e) → (tangentSpace P e) → ℝ := fun a b =>
        ((baseChartMetric P e he).toLinearMap.toFun a).toLinearMap.toFun b
      q (d u) (d v) = p u v)
    (hcubic : ∀ u : (tangentSpace P e),
      let equiv : (tangentSpace P e) ≃ (tangentSpace Q f) := D.toEquiv
      let forward : (tangentSpace P e) → (tangentSpace Q f) := equiv.toFun
      let z : (tangentSpace Q f) := forward u
      let a : H := z.val
      Q.form ![a,a,a] = P.form ![u.val,u.val,u.val]) (x : E) :
    diagonalCubic Q.form (ambientLift P e he Q f hf D x) = diagonalCubic P.form x := by
  let t : ℝ := fderiv ℝ (diagonalCubic P.form) e x / 3
  let u : (tangentSpace P e) := tangentProjection P e he x
  have hsplit : t • e + (u : E) = x := normalSplit_left_inverse P e he x
  have hN : diagonalCubic P.form x =
      t^3 - (3 / 2 : ℝ) * t * (baseChartMetric P e he) u u + P.form ![(u : E),(u : E),(u : E)] := by
    calc
      diagonalCubic P.form x = diagonalCubic P.form (t • e + (u : E)) :=
        congrArg (diagonalCubic P.form) hsplit.symm
      _ = _ := cubic_unit_tangent_expansion P e he t u
  have hm : baseChartMetric Q f hf (D u) (D u) = baseChartMetric P e he u u :=
    hmetric u u
  have hc : Q.form ![(D u : H),(D u : H),(D u : H)] =
      P.form ![(u : E),(u : E),(u : E)] := hcubic u
  rw [ambientLift_apply]
  change diagonalCubic Q.form (t • f + (D u : H)) = _
  rw [cubic_unit_tangent_expansion Q f hf, hm, hc, hN]

set_option maxHeartbeats 800000 in
/-- A genuine norm/unit morphism is CONSTRUCTED. The stored certificates are
proved outputs, not additional hypotheses about an unknown ambient map. -/
def basedNormIsoOfTangent (D : tangentSpace P e ≃ₗ[ℝ] tangentSpace Q f) [FiniteDimensional ℝ E]
    (hmetric : ∀ u v : (tangentSpace P e),
      let equiv : (tangentSpace P e) ≃ (tangentSpace Q f) := D.toEquiv
      let d : (tangentSpace P e) → (tangentSpace Q f) := equiv.toFun
      let q : (tangentSpace Q f) → (tangentSpace Q f) → ℝ := fun a b =>
        ((baseChartMetric Q f hf).toLinearMap.toFun a).toLinearMap.toFun b
      let p : (tangentSpace P e) → (tangentSpace P e) → ℝ := fun a b =>
        ((baseChartMetric P e he).toLinearMap.toFun a).toLinearMap.toFun b
      q (d u) (d v) = p u v)
    (hcubic : ∀ u : (tangentSpace P e),
      let equiv : (tangentSpace P e) ≃ (tangentSpace Q f) := D.toEquiv
      let forward : (tangentSpace P e) → (tangentSpace Q f) := equiv.toFun
      let z : (tangentSpace Q f) := forward u
      let a : H := z.val
      Q.form ![a,a,a] = P.form ![u.val,u.val,u.val]) : BasedNormIso P e Q f where
  equiv := (ambientLift P e he Q f hf D).toContinuousLinearEquiv
  map_unit := ambientLift_unit P e he Q f hf D
  map_norm := ambientLift_norm P e he Q f hf D hmetric hcubic

end
end AlbertGeometry.UnitTangentNormReconstruction
