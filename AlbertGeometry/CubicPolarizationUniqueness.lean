/-
Symmetric continuous trilinear representations
are unique because their equal whole diagonal functions have equal actual third
Frechet derivatives. No prescribed jet, uniqueness premise or recognition
conclusion is assumed. This does not yet bind arbitrary carrier coordinates or
native Newton coefficients to the geometric endpoint.
-/
module

public import AlbertGeometry.CubicThirdDerivative
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic

@[expose] public section

namespace AlbertGeometry.Cubic
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Whole-function equality is carried through two actual derivatives. -/
theorem cubicHessian_function_eq_of_diagonal_eq
    (P Q : SymmetricTrilinearForm E)
    (hN : diagonalCubic P.form = diagonalCubic Q.form) :
    cubicHessian P = cubicHessian Q := by
  exact congrArg
    (fun N : E → ℝ => fun x : E =>
      fderiv ℝ (fun z : E => fderiv ℝ N z) x) hN

/-- Equal whole diagonal functions have equal literal third derivatives. -/
theorem cubicThirdDerivative_eq_of_diagonal_eq
    (P Q : SymmetricTrilinearForm E)
    (hN : diagonalCubic P.form = diagonalCubic Q.form) (x : E) :
    cubicThirdDerivative P x = cubicThirdDerivative Q x := by
  exact congrArg
    (fun H : E → (E →L[ℝ] E →L[ℝ] ℝ) => fderiv ℝ H x)
    (cubicHessian_function_eq_of_diagonal_eq P Q hN)

/-- The already proved one-sixth recovery formula cancels the third derivative.
The basepoint zero is arbitrary; the derivative theorem is global. -/
theorem form_apply_eq_of_diagonal_eq
    (P Q : SymmetricTrilinearForm E)
    (hN : diagonalCubic P.form = diagonalCubic Q.form) (u v w : E) :
    P.form ![u, v, w] = Q.form ![u, v, w] := by
  calc
    P.form ![u, v, w] =
        (1 / 6 : ℝ) * cubicThirdDerivative P (0 : E) u v w :=
      (form_from_actual_thirdDerivative P 0 u v w).symm
    _ = (1 / 6 : ℝ) * cubicThirdDerivative Q (0 : E) u v w :=
      congrArg
        (fun A : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ => (1 / 6 : ℝ) * A u v w)
        (cubicThirdDerivative_eq_of_diagonal_eq P Q hN 0)
    _ = Q.form ![u, v, w] :=
      form_from_actual_thirdDerivative Q 0 u v w

/-- Equality on every ordered triple gives equality of the actual CMMs. -/
theorem form_eq_of_diagonal_eq
    (P Q : SymmetricTrilinearForm E)
    (hN : diagonalCubic P.form = diagonalCubic Q.form) : P.form = Q.form := by
  apply ContinuousMultilinearMap.ext
  intro m
  have hm : m = ![m 0, m 1, m 2] := by
    ext i
    fin_cases i <;> rfl
  rw [hm]
  exact form_apply_eq_of_diagonal_eq P Q hN (m 0) (m 1) (m 2)

/-- Symmetry certificates are propositions, so equality of forms determines the
whole representation structure. -/
theorem symmetricTrilinearForm_ext
    (P Q : SymmetricTrilinearForm E) (hform : P.form = Q.form) : P = Q := by
  cases P with
  | mk p hp12 hp23 =>
    cases Q with
    | mk q hq12 hq23 =>
      change p = q at hform
      cases hform
      rfl

/-- Uniqueness is a conclusion, not a representation structure field. -/
theorem symmetric_diagonalCubic_injective :
    Function.Injective (fun P : SymmetricTrilinearForm E => diagonalCubic P.form) := by
  intro P Q hN
  exact symmetricTrilinearForm_ext P Q (form_eq_of_diagonal_eq P Q hN)

theorem symmetric_diagonalCubic_eq_iff (P Q : SymmetricTrilinearForm E) :
    diagonalCubic P.form = diagonalCubic Q.form ↔ P = Q := by
  constructor
  -- explicit arguments.
  · intro h
    exact symmetricTrilinearForm_ext P Q (form_eq_of_diagonal_eq P Q h)
  · intro h
    cases h
    rfl

end
end AlbertGeometry.Cubic
