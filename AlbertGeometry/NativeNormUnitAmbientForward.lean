/-
One joint forward consumer for the SAME supplied
real linear map preserving the whole literal compact determinant and unit.
It reuses the existing actual native intrinsic-product/positivity and typed
ambient Gamma/R leaves, using their stated identities. The metric
is the actual log-Hessian, with trace/3 calibration; every ambient/radial slot
is retained. Constructing this map from unrestricted full actual curvature
isometry remains a separate recognition theorem.
-/
module

public import AlbertGeometry.NativeAmbientCurvatureBridge
public import AlbertGeometry.NativeCoordinateDictionary

@[expose] public section
namespace AlbertGeometry.NativeNormUnitAmbientForward
noncomputable section
open Module Glennie
open AlbertGeometry.Cubic
open AlbertGeometry.BasedNormDerivativeTransport
open AlbertGeometry.BasedNormAdjointTransport
open AlbertGeometry.NativeEuclideanNormBinding AlbertGeometry.NativeNormAlgebra
open AlbertGeometry.NativeCoordinateDictionary
open AlbertGeometry.NativeAmbientConnectionBridge
open AlbertGeometry.NativeAmbientCurvatureBridge
open AlbertGeometry.AmbientLeviCivitaProduct AlbertGeometry.AmbientCurvatureProduct

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
variable (P : SymmetricTrilinearForm E) (e : E)
  (he : diagonalCubic P.form e = 1)
  (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u)

set_option autoImplicit false in
/-- Whole norm/unit preservation is the ONLY map data. Actual metric, derivative-
defined half-product, affine Levi-Civita connection and its D-Gamma curvature
are derived for that same map. No unknown Jordan or curvature-invariance
premise, tangent-only restriction, determinant surrogate or recognized map
existence is supplied by this conditional forward theorem. -/
theorem native_norm_unit_actual_geometry_forward
    (A : E ≃ₗ[ℝ] Glennie.Albert)
    (hunit : A e = (1 : Glennie.Albert))
    (hnorm : ∀ x : E, nativeDeterminant (A x) = diagonalCubic P.form x) :
    A e = (1 : Glennie.Albert) ∧
    (∀ x : E, nativeDeterminant (A x) = diagonalCubic P.form x) ∧
    (∀ x y : E,
      logHessianForm P e x y = Glennie.trace (jordan (A x) (A y)) / 3) ∧
    (∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y)) ∧
    (∀ x y : E,
      A (ambientGamma P e x y) = -jordan (A x) (A y)) ∧
    (∀ u v w : E,
      A (ambientCurvature P e u v w) =
        -(jordan (A u) (jordan (A v) (A w)) -
          jordan (A v) (jordan (A u) (A w)))) := by
  let F : E ≃ₗ[ℝ] AlbertGeometry.CubicPolynomialRepresentation.Coordinates := A.trans delta.symm
  have hFu : F e = nativeCoordinateUnit := by
    apply delta.injective
    change delta (delta.symm (A e)) = delta nativeCoordinateUnit
    rw [LinearEquiv.apply_symm_apply, delta_nativeCoordinateUnit]
    exact hunit
  have hFN : ∀ x : E,
      diagonalCubic nativeEuclideanRepresentation.form (F x) = diagonalCubic P.form x := by
    intro x
    rw [diagonal_nativeEuclideanRepresentation]
    change nativeNewtonNorm (delta (delta.symm (A x))) = diagonalCubic P.form x
    rw [LinearEquiv.apply_symm_apply]
    exact (nativeNewtonNorm_eq_nativeDeterminant (A x)).trans (hnorm x)
  let I : BasedNormIso P e nativeEuclideanRepresentation nativeCoordinateUnit :=
    BasedNormIso.ofLinearEquiv F hFu hFN
  have hA : ∀ x : E, delta (I.equiv x) = A x := by
    intro x
    change delta (delta.symm (A x)) = A x
    exact delta.apply_symm_apply (A x)
  have hepos : 0 < diagonalCubic P.form e := by
    rw [he]
    norm_num
  refine ⟨hunit, hnorm, ?_, ?_, ?_, ?_⟩
  · intro x y
    have hm := I.logHessianForm_pull e hepos x y
    rw [I.map_unit] at hm
    exact hm.trans (by
      rw [nativeAmbientMetric_eq_trace_third, hA x, hA y])
  · intro x y
    simpa only [hA] using nativeRecognition_product P e he hp I x y
  · intro x y
    simpa only [hA] using nativeRecognition_ambientGamma P e he hp I x y
  · intro u v w
    simpa only [hA] using nativeRecognition_ambientCurvature P e he hp I u v w

end
end AlbertGeometry.NativeNormUnitAmbientForward
