/- For an arbitrary triple T:
  * `toMatrix'_rowLedgerDeriv`: the matrix of the strict derivative
    `rowLedgerDeriv T` in the standard basis is `jacobianEntry T`.
  * `exists_equiv_of_det_ne_zero`: if that matrix has nonzero determinant,
    `rowLedgerDeriv T` is a continuous linear equivalence of R^20, so
    `rowLedger T` has an invertible strict derivative at 0 (the input of the
    inverse function theorem).
  * `jacobianEntry_ctx0/ctx1` and `inner_innerDer_left`: the entry formula reduced
    to one trace pairing, the form the flat-base bridge will evaluate.
  * `rank20_of_bridge`: conditional on the entrywise bridge
    `jacobianEntry T r n = JQ r n` (stated as an explicit hypothesis, not
    assumed anywhere), rank 20 follows from the certificate `det_JQ_ne_zero`. -/
module

public import Glennie.Compact.FlowFamily
public import Glennie.Compact.Rank20Certificate
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

namespace Glennie.Compact.Rank20

open Glennie.Compact.NativeDictionary Glennie.Compact.Flows Glennie.Compact.FlowFamily
  Glennie.Compact.Rank20Certificate

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-! ## The derivative matrix and invertibility -/

/-- The matrix of `rowLedgerDeriv T` in the standard basis is `jacobianEntry T`. -/
theorem toMatrix'_rowLedgerDeriv (T : Fin 3 → Fin 3 → Albert) :
    LinearMap.toMatrix' ((rowLedgerDeriv T : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) :
      (Fin 20 → ℝ) →ₗ[ℝ] (Fin 20 → ℝ)) = Matrix.of (jacobianEntry T) := by
  ext r n
  rw [LinearMap.toMatrix'_apply, Matrix.of_apply, ContinuousLinearMap.coe_coe,
    rowLedgerDeriv_single]

/-- A nonzero determinant of the jacobianEntry matrix makes the strict derivative of the
twenty selected ledger rows a continuous linear equivalence of R^20. -/
theorem exists_equiv_of_det_ne_zero (T : Fin 3 → Fin 3 → Albert)
    (h : (Matrix.of (jacobianEntry T)).det ≠ 0) :
    ∃ e : (Fin 20 → ℝ) ≃L[ℝ] (Fin 20 → ℝ),
      (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) = rowLedgerDeriv T := by
  have hdet : (rowLedgerDeriv T).det ≠ 0 := by
    intro h0
    apply h
    rw [← toMatrix'_rowLedgerDeriv, LinearMap.det_toMatrix']
    exact h0
  exact ⟨(rowLedgerDeriv T).toContinuousLinearEquivOfDetNeZero hdet,
    (rowLedgerDeriv T).coe_toContinuousLinearEquivOfDetNeZero hdet⟩

/-- The twenty rows then have an invertible strict derivative at 0. -/
theorem hasStrictFDerivAt_rowLedger_of_equiv (T : Fin 3 → Fin 3 → Albert)
    (e : (Fin 20 → ℝ) ≃L[ℝ] (Fin 20 → ℝ))
    (he : (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) = rowLedgerDeriv T) :
    HasStrictFDerivAt (rowLedger T) (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) 0 := by
  rw [he]
  exact hasStrictFDerivAt_rowLedger T

/-- Conditional rank 20: if the derivative matrix at T is the certified matrix JQ, the
strict derivative of the twenty rows at T is a continuous linear equivalence. -/
theorem rank20_of_bridge (T : Fin 3 → Fin 3 → Albert)
    (hT : ∀ r n : Fin 20, jacobianEntry T r n = JQ r n) :
    ∃ e : (Fin 20 → ℝ) ≃L[ℝ] (Fin 20 → ℝ),
      (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) = rowLedgerDeriv T := by
  apply exists_equiv_of_det_ne_zero
  have hJ : Matrix.of (jacobianEntry T) = JQ := by
    ext r n
    exact hT r n
  rw [hJ]
  exact det_JQ_ne_zero

/-! ## Entry formulas for the bridge -/

/-- First-frame columns: one trace pairing. -/
theorem jacobianEntry_ctx0 (T : Fin 3 → Fin 3 → Albert) (r n : Fin 20)
    (h : contextIndex n = 0) :
    jacobianEntry T r n = inner (direction n (T 0 (rowIndex r).1))
      (jordan (T 1 (rowIndex r).2.1) (T 2 (rowIndex r).2.2)) := by
  have e0 : atomTangent T n 0 (rowIndex r).1 = direction n (T 0 (rowIndex r).1) := by
    rw [atomTangent, ite_eq_left h.symm]
  have e1 : atomTangent T n 1 (rowIndex r).2.1 = 0 := by
    rw [atomTangent, ite_eq_right (show (1 : Fin 3) ≠ contextIndex n by rw [h]; decide)]
  have e2 : atomTangent T n 2 (rowIndex r).2.2 = 0 := by
    rw [atomTangent, ite_eq_right (show (2 : Fin 3) ≠ contextIndex n by rw [h]; decide)]
  simp only [jacobianEntry, e0, e1, e2, jordan_zero_left, jordan_zero_right, add_zero,
    zero_add]
  show inner (jordan (direction n (T 0 (rowIndex r).1)) (T 1 (rowIndex r).2.1))
    (T 2 (rowIndex r).2.2) = _
  exact inner_jordan_associative _ _ _

/-- Second-frame columns: one trace pairing. -/
theorem jacobianEntry_ctx1 (T : Fin 3 → Fin 3 → Albert) (r n : Fin 20)
    (h : contextIndex n = 1) :
    jacobianEntry T r n = inner (direction n (T 1 (rowIndex r).2.1))
      (jordan (T 0 (rowIndex r).1) (T 2 (rowIndex r).2.2)) := by
  have e0 : atomTangent T n 0 (rowIndex r).1 = 0 := by
    rw [atomTangent, ite_eq_right (show (0 : Fin 3) ≠ contextIndex n by rw [h]; decide)]
  have e1 : atomTangent T n 1 (rowIndex r).2.1 = direction n (T 1 (rowIndex r).2.1) := by
    rw [atomTangent, ite_eq_left h.symm]
  have e2 : atomTangent T n 2 (rowIndex r).2.2 = 0 := by
    rw [atomTangent, ite_eq_right (show (2 : Fin 3) ≠ contextIndex n by rw [h]; decide)]
  simp only [jacobianEntry, e0, e1, e2, jordan_zero_left, jordan_zero_right, add_zero,
    zero_add]
  rw [jordan_comm (T 0 (rowIndex r).1) (direction n (T 1 (rowIndex r).2.1))]
  show inner (jordan (direction n (T 1 (rowIndex r).2.1)) (T 0 (rowIndex r).1))
    (T 2 (rowIndex r).2.2) = _
  exact inner_jordan_associative _ _ _

/-- The pairing of an inner derivation [L_a, L_b] x with W isolates b. -/
theorem inner_innerDer_left (a b x w : Albert) :
    inner (innerDer a b x) w =
      inner b (jordan x (jordan a w) - jordan (jordan a x) w) := by
  have h1 : inner (jordan a (jordan b x)) w = inner b (jordan x (jordan a w)) := by
    rw [jordan_comm a (jordan b x), inner_jordan_associative, inner_jordan_associative]
  have h2 : inner (jordan b (jordan a x)) w = inner b (jordan (jordan a x) w) :=
    inner_jordan_associative _ _ _
  rw [innerDer, inner_sub_left, h1, h2, inner_sub_right]

/-- The same for the directions. -/
theorem inner_direction_left (n : Fin 20) (x w : Albert) :
    inner (direction n x) w =
      inner (extDecode (extUnit (partnerIndex n)))
        (jordan x (jordan (extDecode (extUnit 1)) w) -
          jordan (jordan (extDecode (extUnit 1)) x) w) := by
  rw [direction, innerDerLinear_apply, inner_innerDer_left]

end
end Glennie.Compact.Rank20
