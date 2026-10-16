/-
Geometric foundation. No geometric recognition or arbitrary-polynomial representation
correspondence is claimed here.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

open scoped BigOperators ContDiff

namespace AlbertGeometry.Cubic

noncomputable section

/-- An actual continuous trilinear form, not a collection of desired jets. -/
abbrev TrilinearForm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The continuous linear diagonal embedding into the three slots. -/
def diagonalEmbedding : E →L[ℝ] (Fin 3 → E) :=
  ContinuousLinearMap.pi (fun _ : Fin 3 => ContinuousLinearMap.id ℝ E)

@[simp] theorem diagonalEmbedding_apply (x : E) (i : Fin 3) :
    diagonalEmbedding (E := E) x i = x := rfl

/-- The literal diagonal degree-three polynomial attached to the form. -/
def diagonalCubic (P : TrilinearForm E) (x : E) : ℝ :=
  P (fun _ : Fin 3 => x)

/-- The explicit slot-sum candidate, subsequently certified by HasFDerivAt.
The derivative itself is never defined by an assumed Euler/gradient identity. -/
def diagonalDerivative (P : TrilinearForm E) (x : E) : E →L[ℝ] ℝ :=
  (P.linearDeriv (fun _ : Fin 3 => x)).comp (diagonalEmbedding (E := E))

/-- The actual derivative follows by the chain rule for the diagonal embedding. -/
theorem hasFDerivAt_diagonalCubic (P : TrilinearForm E) (x : E) :
    HasFDerivAt (diagonalCubic P) (diagonalDerivative P x) x := by
  change HasFDerivAt
    (fun z : E => P (diagonalEmbedding (E := E) z))
    ((P.linearDeriv (diagonalEmbedding (E := E) x)).comp
      (diagonalEmbedding (E := E))) x
  exact (P.hasFDerivAt (diagonalEmbedding (E := E) x)).comp x
    (diagonalEmbedding (E := E)).hasFDerivAt

/-- This uses proved differentiability, never the total fderiv fallback. -/
theorem fderiv_diagonalCubic (P : TrilinearForm E) (x : E) :
    fderiv ℝ (diagonalCubic P) x = diagonalDerivative P x :=
  (hasFDerivAt_diagonalCubic P x).fderiv

theorem differentiable_diagonalCubic (P : TrilinearForm E) :
    Differentiable ℝ (diagonalCubic P) :=
  fun x => (hasFDerivAt_diagonalCubic P x).differentiableAt

/-- Smoothness comes from a continuous polynomial and a continuous linear map. -/
theorem contDiff_diagonalCubic (P : TrilinearForm E) (n : ℕ∞ω) :
    ContDiff ℝ n (diagonalCubic P) := by
  change ContDiff ℝ n (fun z : E => P (diagonalEmbedding (E := E) z))
  exact P.contDiff.comp (diagonalEmbedding (E := E)).contDiff

/-- The three replacements are the differentiated slots of the true form. -/
theorem diagonalDerivative_apply (P : TrilinearForm E) (x y : E) :
    diagonalDerivative P x y =
      ∑ i : Fin 3, P (Function.update (fun _ : Fin 3 => x) i y) := by
  simp only [diagonalDerivative, ContinuousLinearMap.comp_apply,
    ContinuousMultilinearMap.linearDeriv_apply, diagonalEmbedding_apply]

/-- Homogeneity is a consequence of multilinearity, including at scalar zero. -/
theorem diagonalCubic_smul (P : TrilinearForm E) (r : ℝ) (x : E) :
    diagonalCubic P (r • x) = r ^ 3 * diagonalCubic P x := by
  change P (fun _ : Fin 3 => r • x) = r ^ 3 * P (fun _ : Fin 3 => x)
  rw [P.map_smul_univ (fun _ : Fin 3 => r) (fun _ : Fin 3 => x)]
  simp only [Fin.prod_univ_three, smul_eq_mul]
  ring

/-- Euler's radial identity requires no symmetry premise. -/
theorem diagonalDerivative_radial (P : TrilinearForm E) (x : E) :
    diagonalDerivative P x x = 3 * diagonalCubic P x := by
  have hu (i : Fin 3) :
      Function.update (fun _ : Fin 3 => x) i x = (fun _ : Fin 3 => x) :=
    Function.update_eq_self i (fun _ : Fin 3 => x)
  rw [diagonalDerivative_apply]
  simp only [hu, Fin.sum_univ_three]
  change P (fun _ : Fin 3 => x) + P (fun _ : Fin 3 => x) +
    P (fun _ : Fin 3 => x) = 3 * P (fun _ : Fin 3 => x)
  ring

/-- Euler is stated for the genuine Fréchet derivative. -/
theorem fderiv_diagonalCubic_radial (P : TrilinearForm E) (x : E) :
    fderiv ℝ (diagonalCubic P) x x = 3 * diagonalCubic P x := by
  rw [fderiv_diagonalCubic, diagonalDerivative_radial]

/-- A normalized base point is a regular point; this is not assumed as a field. -/
theorem fderiv_diagonalCubic_at_one (P : TrilinearForm E) (e : E)
    (he : diagonalCubic P e = 1) :
    fderiv ℝ (diagonalCubic P) e e = 3 := by
  rw [fderiv_diagonalCubic_radial, he]
  ring

theorem fderiv_diagonalCubic_ne_zero_at_one (P : TrilinearForm E) (e : E)
    (he : diagonalCubic P e = 1) :
    fderiv ℝ (diagonalCubic P) e ≠ 0 := by
  intro hz
  have hr := fderiv_diagonalCubic_at_one P e he
  rw [hz] at hr
  norm_num at hr

/-- Symmetry of a trilinear representation. The full arbitrary homogeneous-cubic
correspondence with such representations is not part of this structure definition;
this structure is not a replacement recognition endpoint or a Jordan premise. -/
structure SymmetricTrilinearForm (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  form : TrilinearForm E
  swap12 : ∀ (x y z : E), form ![x, y, z] = form ![y, x, z]
  swap23 : ∀ (x y z : E), form ![x, y, z] = form ![x, z, y]

/-- The true slot-sum derivative simplifies to the expected threefold term. -/
theorem diagonalDerivative_apply_symmetric (P : SymmetricTrilinearForm E)
    (x y : E) :
    diagonalDerivative P.form x y = 3 * P.form ![x, x, y] := by
  have h0 : Function.update (fun _ : Fin 3 => x) 0 y = ![y, x, x] := by
    ext i
    fin_cases i <;> simp
  have h1 : Function.update (fun _ : Fin 3 => x) 1 y = ![x, y, x] := by
    ext i
    fin_cases i <;> simp
  have h2 : Function.update (fun _ : Fin 3 => x) 2 y = ![x, x, y] := by
    ext i
    fin_cases i <;> simp
  rw [diagonalDerivative_apply, Fin.sum_univ_three, h0, h1, h2]
  simp only [P.swap12 y x x, P.swap23 x y x]
  ring

/-- The symmetric formula is identified with actual fderiv, not defined as it. -/
theorem fderiv_diagonalCubic_apply_symmetric (P : SymmetricTrilinearForm E)
    (x y : E) :
    fderiv ℝ (diagonalCubic P.form) x y = 3 * P.form ![x, x, y] := by
  rw [fderiv_diagonalCubic, diagonalDerivative_apply_symmetric]

end
end AlbertGeometry.Cubic
