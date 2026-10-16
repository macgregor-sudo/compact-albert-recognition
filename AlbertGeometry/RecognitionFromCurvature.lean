/-
The INPUT is the TARGET's actual
one-point tangent metric/curvature isometry, not a recognized ambient map. The
frame F=nativeMetricFrame.trans I.symm therefore has the actual full-R matching
certificate. unrestricted q recovery gives both possible cubic signs;
I or tangent-negated I then constructs a genuine whole cubic norm/unit ambient
equivalence by the exact unit+tangent polynomial identity. No arbitrary chosen
orthonormal frame is assumed curvature-matching. No unknown Jordan/invariance.
-/
module

public import AlbertGeometry.UnitTangentNormReconstruction
public import Mathlib.Algebra.Module.Equiv.Basic

@[expose] public section
namespace AlbertGeometry.RecognitionFromCurvature
noncomputable section
open Module Glennie AlbertRecognition
open AlbertGeometry.Cubic AlbertGeometry.CubicPolynomialRepresentation
open AlbertGeometry.NativeNormAlgebra AlbertGeometry.NativeEuclideanNormBinding
open AlbertGeometry.NativeCoordinateDerivatives AlbertGeometry.NativeCoordinateDictionary
open AlbertGeometry.NativeCurvatureDictionary
open AlbertGeometry.UnitTangentNormReconstruction
open AlbertGeometry.BasedNormDerivativeTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (P : SymmetricTrilinearForm E) (e : E) (he : diagonalCubic P.form e = 1)

/-- Exactly an actual pointwise metric+FULL curvature matching isomorphism.
No whole norm, unit, trace, product or already-recognized ambient F is stored. -/
structure TangentCurvatureIso where
  equiv : (tangentSpace P e) ≃ₗ[ℝ] NativeChartTangent
  map_metric : ∀ u v : (tangentSpace P e), (baseChartMetric nativeEuclideanRepresentation nativeCoordinateUnit nativeNormalization) (equiv u) (equiv v) = (baseChartMetric P e he) u v
  map_curvature : ∀ u v w : (tangentSpace P e),
    equiv (chartCurvature P e he 0 u v w) = (chartCurvature nativeEuclideanRepresentation nativeCoordinateUnit nativeNormalization 0) (equiv u) (equiv v) (equiv w)

variable (I : TangentCurvatureIso P e he)

/-- The frame is selected FROM THE ACTUAL MATCHING I, not an arbitrary Gram
choice. This is an algebraic coordinate map only, with its certificates below. -/
def matchingMetricFrame : V ≃ₗ[ℝ] (tangentSpace P e) := nativeMetricFrame.trans I.equiv.symm

@[simp] theorem matchingMetricFrame_image (x : V) :
    I.equiv (matchingMetricFrame P e he I x) = nativeMetricFrame x := by
  exact I.equiv.apply_symm_apply (nativeMetricFrame x)

/-- True metric matching in the chosen frame follows from the target isometry. -/
theorem matchingMetricFrame_metric (x y : V) :
    (baseChartMetric P e he) (matchingMetricFrame P e he I x) (matchingMetricFrame P e he I y) = gA x y := by
  have h := I.map_metric (matchingMetricFrame P e he I x) (matchingMetricFrame P e he I y)
  rw [matchingMetricFrame_image, matchingMetricFrame_image, nativeMetricFrame_metric] at h
  exact h.symm

/-- FULL actual vector-valued matching in THIS frame, derived from the target
matching. No inference of R preservation under an arbitrary orthogonal map. -/
theorem matchingMetricFrame_curvature (x y z : V) :
    chartCurvature P e he 0 (matchingMetricFrame P e he I x)
      (matchingMetricFrame P e he I y) (matchingMetricFrame P e he I z) =
      matchingMetricFrame P e he I (nativeCurvatureValue x y z) := by
  apply I.equiv.injective
  rw [I.map_curvature, matchingMetricFrame_image, matchingMetricFrame_image,
    matchingMetricFrame_image, matchingMetricFrame_image]
  exact (nativeMetricFrame.apply_symm_apply ((chartCurvature nativeEuclideanRepresentation nativeCoordinateUnit nativeNormalization 0) (nativeMetricFrame x)
    (nativeMetricFrame y) (nativeMetricFrame z))).symm

/-- If another Gram frame F0 was chosen, this is the actual coordinate change
F0⁻¹∘F. It is an algebraic correction, not an assumed R automorphism. -/
def matchingFrameChange (F0 : V ≃ₗ[ℝ] (tangentSpace P e)) : V ≃ₗ[ℝ] V :=
  (matchingMetricFrame P e he I).trans F0.symm

@[simp] theorem matchingFrameChange_apply (F0 : V ≃ₗ[ℝ] (tangentSpace P e)) (x : V) :
    F0 (matchingFrameChange P e he I F0 x) = matchingMetricFrame P e he I x :=
  F0.apply_symm_apply _

variable [FiniteDimensional ℝ E]
variable (hpos : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u)

include hpos in
/-- The arbitrary quadratic fiber applies in the actual matching
frame, with no chosen-frame equality replacing the target's existential I. -/
theorem matchingFrameCubic_sign :
    frameCubic P e (matchingMetricFrame P e he I) = referenceCubic ∨ frameCubic P e (matchingMetricFrame P e he I) = scalarCubic (-1) referenceCubic :=
  frameCubic_sign_of_full_curvature P e he (matchingMetricFrame P e he I) hpos
    (matchingMetricFrame_metric P e he I) (matchingMetricFrame_curvature P e he I)

/-- The positive sign gives the actual diagonal tangent cubic transport. -/
theorem tangentCubic_positive
    (hB : frameCubic P e (matchingMetricFrame P e he I) = referenceCubic) (u : (tangentSpace P e)) :
    nativeEuclideanRepresentation.form ![(I.equiv u : Coordinates),(I.equiv u : Coordinates),(I.equiv u : Coordinates)] =
      P.form ![(u : E),(u : E),(u : E)] := by
  obtain ⟨x, rfl⟩ := (matchingMetricFrame P e he I).surjective u
  rw [matchingMetricFrame_image, nativeMetricFrame_cubic]
  have h := congrArg (fun B : SymmetricCubic => B.form x x x) hB
  simpa only [frameCubic_apply] using h.symm

/-- Negative tangent map is an ACTUAL linear equivalence, preserving unit only
when subsequently lifted through the unit/tangent split. -/
def negativeTangentEquiv : (tangentSpace P e) ≃ₗ[ℝ] NativeChartTangent :=
  I.equiv.trans (LinearEquiv.neg ℝ)

@[simp] theorem negativeTangentEquiv_apply (u : (tangentSpace P e)) :
    negativeTangentEquiv P e he I u = -(I.equiv u) := rfl

theorem negativeTangentEquiv_metric (u v : (tangentSpace P e)) :
    (baseChartMetric nativeEuclideanRepresentation nativeCoordinateUnit nativeNormalization) (negativeTangentEquiv P e he I u) (negativeTangentEquiv P e he I v) = (baseChartMetric P e he) u v := by
  simp only [negativeTangentEquiv_apply, map_neg, ContinuousLinearMap.neg_apply, neg_neg]
  exact I.map_metric u v

/-- The negative cubic sign is corrected by tangent negation; unit stays fixed
in the full ambient lift. Triple negation contributes exactly one minus sign. -/
theorem tangentCubic_negative
    (hB : frameCubic P e (matchingMetricFrame P e he I) = scalarCubic (-1) referenceCubic) (u : (tangentSpace P e)) :
    nativeEuclideanRepresentation.form ![(negativeTangentEquiv P e he I u : Coordinates),
      (negativeTangentEquiv P e he I u : Coordinates),
      (negativeTangentEquiv P e he I u : Coordinates)] =
      P.form ![(u : E),(u : E),(u : E)] := by
  obtain ⟨x, rfl⟩ := (matchingMetricFrame P e he I).surjective u
  simp only [negativeTangentEquiv_apply, matchingMetricFrame_image, Submodule.coe_neg]
  rw [cubic_three_neg, nativeMetricFrame_cubic]
  have h := congrArg (fun B : SymmetricCubic => B.form x x x) hB
  simpa only [frameCubic_apply, scalarCubic_form, neg_mul, one_mul] using h.symm

include I hpos in
/-- Whole norm/unit equivalence is PRODUCED in either sign. The only input map
was the actual target tangent metric/full-curvature matching. -/
theorem basedNormIso_of_tangentCurvature : Nonempty (BasedNormIso P e nativeEuclideanRepresentation nativeCoordinateUnit) := by
  have build (Q : SymmetricTrilinearForm Coordinates) (f : Coordinates)
      (hf : diagonalCubic Q.form f = 1)
      (D : tangentSpace P e ≃ₗ[ℝ] tangentSpace Q f)
      (hmetric : ∀ u v : tangentSpace P e,
        baseChartMetric Q f hf (D u) (D v) = baseChartMetric P e he u v)
      (hcubic : ∀ u : tangentSpace P e,
        Q.form ![(D u : Coordinates),(D u : Coordinates),(D u : Coordinates)] =
          P.form ![(u : E),(u : E),(u : E)]) : BasedNormIso P e Q f := by
    refine basedNormIsoOfTangent (E := E) (H := Coordinates) P e he Q f hf D ?_ ?_
    · intro u v
      exact hmetric u v
    · intro u
      exact hcubic u
  rcases matchingFrameCubic_sign P e he I hpos with hp | hn
  · with_implicit exact ⟨build nativeEuclideanRepresentation nativeCoordinateUnit nativeNormalization
      I.equiv I.map_metric (tangentCubic_positive P e he I hp)⟩
  · with_implicit exact ⟨build nativeEuclideanRepresentation nativeCoordinateUnit nativeNormalization
      (negativeTangentEquiv P e he I) (negativeTangentEquiv_metric P e he I)
      (tangentCubic_negative P e he I hn)⟩

include hpos in
/-- Genuine TARGET existential matching is consumed directly, without selecting
an unrelated Gram frame or asking its entries to match reference curvature. -/
theorem basedNormIso_of_exists_tangentCurvature
    (hI : Nonempty (TangentCurvatureIso P e he)) : Nonempty (BasedNormIso P e nativeEuclideanRepresentation nativeCoordinateUnit) := by
  obtain ⟨I⟩ := hI
  exact basedNormIso_of_tangentCurvature P e he I hpos

include hpos in
/-- Algebraic native-coordinate recognition in literal Newton norm and unit.
Native Albert receives no normed/continuous-space instance. -/
theorem nativeNewtonRecognition_of_exists_tangentCurvature
    (hI : Nonempty (TangentCurvatureIso P e he)) :
    ∃ A : E ≃ₗ[ℝ] Albert, A e = 1 ∧
      ∀ x : E, nativeNewtonNorm (A x) = diagonalCubic P.form x := by
  obtain ⟨J⟩ := basedNormIso_of_exists_tangentCurvature P e he hpos hI
  let A : E ≃ₗ[ℝ] Albert := J.equiv.toLinearEquiv.trans delta
  refine ⟨A, ?_, fun x => ?_⟩
  · change delta (J.equiv e) = 1
    rw [J.map_unit, delta_nativeCoordinateUnit]
  · change nativeNewtonNorm (delta (J.equiv x)) = diagonalCubic P.form x
    rw [← diagonal_nativeEuclideanRepresentation]
    exact J.map_norm x

include hpos in
/-- Literal compact determinant recognition after the genuine whole native
Newton/determinant identity, with ALL unknowns still unrestricted. -/
theorem nativeDeterminantRecognition_of_exists_tangentCurvature
    (hI : Nonempty (TangentCurvatureIso P e he)) :
    ∃ A : E ≃ₗ[ℝ] Albert, A e = 1 ∧
      ∀ x : E, nativeDeterminant (A x) = diagonalCubic P.form x := by
  obtain ⟨A, hu, hN⟩ := nativeNewtonRecognition_of_exists_tangentCurvature P e he hpos hI
  exact ⟨A, hu, fun x => (nativeNewtonNorm_eq_nativeDeterminant (A x)).symm.trans (hN x)⟩

end
end AlbertGeometry.RecognitionFromCurvature
