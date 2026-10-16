/-
Thin integration of the original unrestricted actual
metric/full-vector-curvature entrance with the SAME constructed ambient map's
whole norm, unit, actual metric, intrinsic product, connection and curvature.
The whole DN/3 split and both cubic-sign cases are already proved in the
UnitTangent/Recognition sources; none of those constructions is duplicated here.
No unknown Jordan, cubic-invariance, derivation, classification, F4-image,
genericity or recognized ambient map is an input. Polynomial presentation stays
explicit in its existing frontend; this is the exact symmetric-cubic consumer.
-/
module

public import AlbertGeometry.RecognitionFromCurvature
public import AlbertGeometry.NativeNormUnitAmbientForward

@[expose] public section
namespace AlbertGeometry.ActualU2NativeGeometry
noncomputable section
open Module Glennie
open AlbertGeometry.Cubic AlbertGeometry.BasedNormAdjointTransport
open AlbertGeometry.RecognitionFromCurvature
open AlbertGeometry.NativeNormAlgebra
open AlbertGeometry.NativeNormUnitAmbientForward
open AlbertGeometry.AmbientLeviCivitaProduct AlbertGeometry.AmbientCurvatureProduct

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
variable (P : SymmetricTrilinearForm E) (e : E)
  (he : diagonalCubic P.form e = 1)
  (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u)

set_option autoImplicit false in
/-- The ORIGINAL tangent metric and every vector-valued R slot produce one
ambient equivalence with all six actual geometric outputs. In particular,
metric, product and all ambient/radial curvature slots use that same A. -/
theorem exists_native_norm_unit_actual_geometry
    (hR : Nonempty (TangentCurvatureIso P e he)) :
    ∃ A : E ≃ₗ[ℝ] Glennie.Albert,
      A e = (1 : Glennie.Albert) ∧
      (∀ x : E, AlbertGeometry.NativeCoordinateDictionary.nativeDeterminant (A x) = diagonalCubic P.form x) ∧
      (∀ x y : E,
        logHessianForm P e x y = Glennie.trace (jordan (A x) (A y)) / 3) ∧
      (∀ x y : E,
        A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
          jordan (A x) (A y)) ∧
      (∀ x y : E, A (ambientGamma P e x y) = -jordan (A x) (A y)) ∧
      (∀ u v w : E,
        A (ambientCurvature P e u v w) =
          -(jordan (A u) (jordan (A v) (A w)) -
            jordan (A v) (jordan (A u) (A w)))) := by
  obtain ⟨A, hunit, hnorm⟩ :=
    nativeDeterminantRecognition_of_exists_tangentCurvature P e he hp hR
  exact ⟨A, native_norm_unit_actual_geometry_forward P e he hp A hunit hnorm⟩

end
end AlbertGeometry.ActualU2NativeGeometry
