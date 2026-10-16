/-
Differentiating the actual second Frechet
 derivative as a map into continuous bilinear forms. No assumed third jet,
 arbitrary-polynomial representation, recognition or curvature conclusion.
-/
module

public import AlbertGeometry.CubicHessian

@[expose] public section

open scoped ContDiff

namespace AlbertGeometry.Cubic
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The genuine fully curried continuous trilinear form. -/
def fullyCurried (P : SymmetricTrilinearForm E) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  (((continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] ℝ)).toContinuousLinearEquiv).toContinuousLinearMap).comp
    ((rightCurried P).curryLeft)

@[simp] theorem fullyCurried_apply (P : SymmetricTrilinearForm E) (x u v : E) :
    fullyCurried P x u v = P.form ![x, u, v] := by
  change continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] ℝ)
    ((rightCurried P).curryLeft x) u v = P.form ![x, u, v]
  rw [continuousMultilinearCurryFin1_apply,
    ContinuousMultilinearMap.curryLeft_apply]
  have h : Fin.cons x (Fin.snoc (0 : Fin 0 → E) u) = ![x, u] := by
    ext i
    fin_cases i <;> simp
  rw [h, rightCurried_apply]

/-- Whole-function identification is obtained from the true Hessian theorem,
 before taking another derivative. It does not follow from basepoint jets. -/
theorem cubicHessian_eq_fullyCurried (P : SymmetricTrilinearForm E) (x : E) :
    cubicHessian P x = (6 : ℝ) • fullyCurried P x := by
  ext u v
  rw [cubicHessian_apply]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, fullyCurried_apply]

/-- Actual derivative of the actual Hessian, proved via its global linear form. -/
theorem hasFDerivAt_cubicHessian (P : SymmetricTrilinearForm E) (x : E) :
    HasFDerivAt (cubicHessian P) ((6 : ℝ) • fullyCurried P) x := by
  have h : HasFDerivAt (fun z : E => (6 : ℝ) • fullyCurried P z)
      ((6 : ℝ) • fullyCurried P) x :=
    by
      let L : E →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) := fullyCurried P
      have hlinear : HasFDerivAt
          (((6 : ℝ) • L) : E → (E →L[ℝ] E →L[ℝ] ℝ)) ((6 : ℝ) • L) x :=
        ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := E)
          (F := E →L[ℝ] E →L[ℝ] ℝ) ((6 : ℝ) • L) (x := x)
      have hfun : (fun z : E => (6 : ℝ) • L z) =
          (6 : ℝ) • (L : E → (E →L[ℝ] E →L[ℝ] ℝ)) := by
        funext z
        exact (Pi.smul_apply (6 : ℝ) (L : E → (E →L[ℝ] E →L[ℝ] ℝ)) z).symm
      have hcoe : (6 : ℝ) • (L : E → (E →L[ℝ] E →L[ℝ] ℝ)) =
          (((6 : ℝ) • L) : E → (E →L[ℝ] E →L[ℝ] ℝ)) :=
        (FunLike.coe_smul (6 : ℝ) L).symm
      exact hlinear.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun z => congrFun (hfun.trans hcoe) z))
  exact h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun z => cubicHessian_eq_fullyCurried P z))

theorem differentiable_cubicHessian (P : SymmetricTrilinearForm E) :
    Differentiable ℝ (cubicHessian P) :=
  fun x => (hasFDerivAt_cubicHessian P x).differentiableAt

/-- Literal third Frechet derivative: derivative of the literal second one. -/
def cubicThirdDerivative (P : SymmetricTrilinearForm E) (x : E) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (cubicHessian P) x

theorem cubicThirdDerivative_eq (P : SymmetricTrilinearForm E) (x : E) :
    cubicThirdDerivative P x = (6 : ℝ) • fullyCurried P :=
  (hasFDerivAt_cubicHessian P x).fderiv

theorem cubicThirdDerivative_apply (P : SymmetricTrilinearForm E)
    (x u v w : E) :
    cubicThirdDerivative P x u v w = 6 * P.form ![u, v, w] := by
  rw [cubicThirdDerivative_eq]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, fullyCurried_apply]

/-- Independence from the basepoint is proved, never a structure field. -/
theorem cubicThirdDerivative_basepoint_independent (P : SymmetricTrilinearForm E)
    (x y : E) : cubicThirdDerivative P x = cubicThirdDerivative P y := by
  rw [cubicThirdDerivative_eq, cubicThirdDerivative_eq]

/-- The one-sixth normalization recovers the actual symmetric trilinear form. -/
theorem form_from_actual_thirdDerivative (P : SymmetricTrilinearForm E)
    (x u v w : E) :
    (1 / 6 : ℝ) * cubicThirdDerivative P x u v w = P.form ![u, v, w] := by
  rw [cubicThirdDerivative_apply]
  ring

end
end AlbertGeometry.Cubic
