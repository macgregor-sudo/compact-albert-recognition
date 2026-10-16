/-
Genuine second Frechet derivatives and log-Hessian forms.
The arbitrary homogeneous-cubic/polarization correspondence remains a separate
full-scope obligation. No geometric metric positivity or curvature is assumed.
-/
module

public import AlbertGeometry.CubicDerivatives
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Topology.Order.OrderClosed

@[expose] public section

open scoped BigOperators ContDiff Topology
open Filter

namespace AlbertGeometry.Cubic
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Genuine currying of the continuous trilinear form, with a CLM-valued result. -/
def rightCurried (P : SymmetricTrilinearForm E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) (E →L[ℝ] ℝ) :=
  P.form.curryRight

private theorem constant_two (x : E) : (fun _ : Fin 2 => x) = ![x, x] := by
  ext i
  fin_cases i <;> rfl

@[simp] theorem rightCurried_apply (P : SymmetricTrilinearForm E) (x y z : E) :
    rightCurried P ![x, y] z = P.form ![x, y, z] := by
  change P.form (Fin.snoc ![x, y] z) = P.form ![x, y, z]
  congr 1
  ext i
  fin_cases i <;> simp

def diagonalEmbeddingTwo : E →L[ℝ] (Fin 2 → E) :=
  ContinuousLinearMap.pi (fun _ : Fin 2 => ContinuousLinearMap.id ℝ E)

@[simp] theorem diagonalEmbeddingTwo_apply (x : E) (i : Fin 2) :
    diagonalEmbeddingTwo (E := E) x i = x := rfl

/-- Equality of the already proved actual first derivative with a CLM-valued
continuous quadratic expression. This permits differentiating the derivative. -/
theorem fderiv_diagonalCubic_eq_curried (P : SymmetricTrilinearForm E) (x : E) :
    fderiv ℝ (diagonalCubic P.form) x =
      (3 : ℝ) • rightCurried P (fun _ : Fin 2 => x) := by
  ext y
  rw [fderiv_diagonalCubic_apply_symmetric]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hc : rightCurried P (fun _ : Fin 2 => x) y = P.form ![x, x, y] :=
    (congrArg (fun z : Fin 2 → E => rightCurried P z y) (constant_two x)).trans
      (rightCurried_apply P x x y)
  exact congrArg (fun r : ℝ => 3 * r) hc.symm

/-- An explicit continuous bilinear candidate, later identified with true fderiv. -/
def hessianFormula (P : SymmetricTrilinearForm E) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (3 : ℝ) • ((rightCurried P).linearDeriv (fun _ : Fin 2 => x)).comp
    (diagonalEmbeddingTwo (E := E))

/-- The derivative of the actual first-derivative map, by multilinear calculus. -/
theorem hasFDerivAt_fderiv_diagonalCubic (P : SymmetricTrilinearForm E) (x : E) :
    HasFDerivAt (fun z : E => fderiv ℝ (diagonalCubic P.form) z)
      (hessianFormula P x) x := by
  simp only [fderiv_diagonalCubic_eq_curried]
  change HasFDerivAt
    (fun z : E => (3 : ℝ) • rightCurried P (diagonalEmbeddingTwo (E := E) z))
    ((3 : ℝ) • ((rightCurried P).linearDeriv
      (diagonalEmbeddingTwo (E := E) x)).comp (diagonalEmbeddingTwo (E := E))) x
  exact (((rightCurried P).hasFDerivAt (diagonalEmbeddingTwo (E := E) x)).comp x
    (diagonalEmbeddingTwo (E := E)).hasFDerivAt).const_smul (3 : ℝ)

/-- Actual second Frechet derivative, obtained by differentiating actual fderiv.
It is not defined as six times a form or as a desired log-Hessian identity. -/
def cubicHessian (P : SymmetricTrilinearForm E) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fun z : E => fderiv ℝ (diagonalCubic P.form) z) x

theorem cubicHessian_eq_formula (P : SymmetricTrilinearForm E) (x : E) :
    cubicHessian P x = hessianFormula P x :=
  (hasFDerivAt_fderiv_diagonalCubic P x).fderiv

theorem hasFDerivAt_fderiv_diagonalCubic_actual (P : SymmetricTrilinearForm E)
    (x : E) :
    HasFDerivAt (fun z : E => fderiv ℝ (diagonalCubic P.form) z)
      (cubicHessian P x) x :=
  (hasFDerivAt_fderiv_diagonalCubic P x).congr_fderiv
    (cubicHessian_eq_formula P x).symm

theorem hessianFormula_apply (P : SymmetricTrilinearForm E) (x u v : E) :
    hessianFormula P x u v = 6 * P.form ![x, u, v] := by
  have h0 : Function.update (fun _ : Fin 2 => x) 0 u = ![u, x] := by
    ext i
    fin_cases i <;> simp
  have h1 : Function.update (fun _ : Fin 2 => x) 1 u = ![x, u] := by
    ext i
    fin_cases i <;> simp
  change 3 * (((rightCurried P).linearDeriv
    (fun _ : Fin 2 => x) (fun _ : Fin 2 => u)) v) = 6 * P.form ![x, u, v]
  rw [ContinuousMultilinearMap.linearDeriv_apply, Fin.sum_univ_two, h0, h1]
  simp only [ContinuousLinearMap.add_apply, rightCurried_apply, P.swap12 u x v]
  ring

theorem cubicHessian_apply (P : SymmetricTrilinearForm E) (x u v : E) :
    cubicHessian P x u v = 6 * P.form ![x, u, v] := by
  rw [cubicHessian_eq_formula, hessianFormula_apply]

theorem cubicHessian_symm (P : SymmetricTrilinearForm E) (x u v : E) :
    cubicHessian P x u v = cubicHessian P x v u := by
  rw [cubicHessian_apply, cubicHessian_apply]
  exact congrArg (fun t : ℝ => 6 * t) (P.swap23 x u v)

/-- Second Euler identity for the actual Hessian and actual first derivative. -/
theorem cubicHessian_radial (P : SymmetricTrilinearForm E) (x u : E) :
    cubicHessian P x x u = 2 * fderiv ℝ (diagonalCubic P.form) x u := by
  rw [cubicHessian_apply, fderiv_diagonalCubic_apply_symmetric]
  ring

/-- The positive locus is selected from the actual cubic, never assumed globally. -/
def positiveLocus (P : SymmetricTrilinearForm E) : Set E :=
  {x | 0 < diagonalCubic P.form x}

theorem isOpen_positiveLocus (P : SymmetricTrilinearForm E) :
    IsOpen (positiveLocus P) :=
  isOpen_lt continuous_const (differentiable_diagonalCubic P.form).continuous

theorem eventually_positive (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) :
    ∀ᶠ z in 𝓝 x, 0 < diagonalCubic P.form z :=
  (isOpen_positiveLocus P).mem_nhds hx

theorem exists_positive_open_neighborhood (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ∀ z ∈ U, 0 < diagonalCubic P.form z :=
  ⟨positiveLocus P, isOpen_positiveLocus P, hx, fun _ hz => hz⟩

/-- Literal log composed with the actual cubic. Identities require positivity. -/
def logCubic (P : SymmetricTrilinearForm E) (x : E) : ℝ :=
  Real.log (diagonalCubic P.form x)

theorem hasFDerivAt_logCubic (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) :
    HasFDerivAt (logCubic P)
      ((diagonalCubic P.form x)⁻¹ • fderiv ℝ (diagonalCubic P.form) x) x := by
  have hN : HasFDerivAt (diagonalCubic P.form)
      (fderiv ℝ (diagonalCubic P.form) x) x :=
    (hasFDerivAt_diagonalCubic P.form x).congr_fderiv
      (fderiv_diagonalCubic P.form x).symm
  exact hN.log (ne_of_gt hx)

theorem fderiv_logCubic (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) :
    fderiv ℝ (logCubic P) x =
      (diagonalCubic P.form x)⁻¹ • fderiv ℝ (diagonalCubic P.form) x :=
  (hasFDerivAt_logCubic P hx).fderiv

/-- Explicit inverse-cubic derivative candidate certified by the true chain rule. -/
def inverseCubicDerivative (P : SymmetricTrilinearForm E) (x : E) : E →L[ℝ] ℝ :=
  (-(diagonalCubic P.form x ^ 2)⁻¹) • fderiv ℝ (diagonalCubic P.form) x

theorem hasFDerivAt_inverseCubic (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) :
    HasFDerivAt (fun z : E => (diagonalCubic P.form z)⁻¹)
      (inverseCubicDerivative P x) x := by
  have hN : HasFDerivAt (diagonalCubic P.form)
      (fderiv ℝ (diagonalCubic P.form) x) x :=
    (hasFDerivAt_diagonalCubic P.form x).congr_fderiv
      (fderiv_diagonalCubic P.form x).symm
  exact (hasDerivAt_inv (ne_of_gt hx)).comp_hasFDerivAt x hN

/-- Explicit candidate from differentiating inverse N times actual DN. -/
def logHessianFormula (P : SymmetricTrilinearForm E) (x : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  (diagonalCubic P.form x)⁻¹ • cubicHessian P x +
    (inverseCubicDerivative P x).smulRight (fderiv ℝ (diagonalCubic P.form) x)

/-- The first-derivative identity is used on a proved positive neighborhood,
not merely at x, before differentiating it to obtain the actual log Hessian. -/
theorem hasFDerivAt_fderiv_logCubic (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) :
    HasFDerivAt (fun z : E => fderiv ℝ (logCubic P) z)
      (logHessianFormula P x) x := by
  have h : HasFDerivAt
      (fun z : E => (diagonalCubic P.form z)⁻¹ • fderiv ℝ (diagonalCubic P.form) z)
      (logHessianFormula P x) x :=
    (hasFDerivAt_inverseCubic P hx).smul
      (hasFDerivAt_fderiv_diagonalCubic_actual P x)
  exact h.congr_of_eventuallyEq
    ((eventually_positive P hx).mono (fun z hz => fderiv_logCubic P hz))

/-- Actual second derivative of literal log N, with positivity-gated theorems. -/
def logHessian (P : SymmetricTrilinearForm E) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fun z : E => fderiv ℝ (logCubic P) z) x

theorem logHessian_eq_formula (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) :
    logHessian P x = logHessianFormula P x :=
  (hasFDerivAt_fderiv_logCubic P hx).fderiv

theorem logHessian_apply (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) (u v : E) :
    logHessian P x u v = cubicHessian P x u v / diagonalCubic P.form x -
      fderiv ℝ (diagonalCubic P.form) x u * fderiv ℝ (diagonalCubic P.form) x v /
        diagonalCubic P.form x ^ 2 := by
  rw [logHessian_eq_formula P hx]
  simp only [logHessianFormula, inverseCubicDerivative, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    smul_eq_mul, div_eq_mul_inv]
  ring

/-- The actual normalized log-Hessian bilinear form. Positive definiteness is
not asserted here; the recognition input must establish it at the base point. -/
def logHessianForm (P : SymmetricTrilinearForm E) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (-1 / 3 : ℝ) • logHessian P x

theorem logHessianForm_apply (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) (u v : E) :
    logHessianForm P x u v = -cubicHessian P x u v / (3 * diagonalCubic P.form x) +
      fderiv ℝ (diagonalCubic P.form) x u * fderiv ℝ (diagonalCubic P.form) x v /
        (3 * diagonalCubic P.form x ^ 2) := by
  simp only [logHessianForm, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [logHessian_apply P hx]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem logHessianForm_symm (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) (u v : E) :
    logHessianForm P x u v = logHessianForm P x v u := by
  rw [logHessianForm_apply P hx, logHessianForm_apply P hx, cubicHessian_symm P x u v]
  ring

/-- Euler identities derive the radial/tangent metric relation at normalized e. -/
theorem logHessianForm_radial_at_one (P : SymmetricTrilinearForm E) (e u : E)
    (he : diagonalCubic P.form e = 1) :
    logHessianForm P e e u = fderiv ℝ (diagonalCubic P.form) e u / 3 := by
  have hpos : 0 < diagonalCubic P.form e := by rw [he]; norm_num
  rw [logHessianForm_apply P hpos, he, cubicHessian_radial,
    fderiv_diagonalCubic_at_one P.form e he]
  ring

theorem logHessianForm_radial_self_at_one (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) :
    logHessianForm P e e e = 1 := by
  rw [logHessianForm_radial_at_one P e e he,
    fderiv_diagonalCubic_at_one P.form e he]
  norm_num

end
end AlbertGeometry.Cubic
