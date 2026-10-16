/-
The actual-curvature entrance followed by intrinsic ordered-frame reconstruction.
The section and orbit conclusions are local to the established chart domain.
The readouts are algebraic and presuppose the recovered Jordan product.
-/
module

public import AlbertGeometry.IntrinsicLocalTransport

@[expose] public section
namespace AlbertGeometry.IntrinsicLocalReconstruction
noncomputable section

open Glennie
open AlbertGeometry.Cubic AlbertGeometry.BasedNormAdjointTransport
open AlbertGeometry.RecognitionFromCurvature
open AlbertGeometry.IntrinsicLocalTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
variable (P : SymmetricTrilinearForm E) (e : E)
  (he : diagonalCubic P.form e = 1)
  (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u)

/-- One recognized ambient algebra and its local frame reconstruction data.
The two sections classify the full fibre of actual ordered source frames under
the complete simultaneous product-and-trace automorphism action. -/
structure Data where
  A : E ≃ₗ[ℝ] Albert
  map_unit : A e = 1
  map_norm : ∀ x : E,
    AlbertGeometry.NativeCoordinateDictionary.nativeDeterminant (A x) =
      diagonalCubic P.form x
  map_metric : ∀ x y : E,
    logHessianForm P e x y = trace (jordan (A x) (A y)) / 3
  map_product : ∀ x y : E,
    A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
      jordan (A x) (A y)
  map_connection : ∀ x y : E,
    A (AlbertGeometry.AmbientLeviCivitaProduct.ambientGamma P e x y) =
      -jordan (A x) (A y)
  map_curvature : ∀ u v w : E,
    A (AlbertGeometry.AmbientCurvatureProduct.ambientCurvature P e u v w) =
      -(jordan (A u) (jordan (A v) (A w)) -
        jordan (A v) (jordan (A u) (A w)))
  V : Set (Fin 20 → ℝ)
  V_open : IsOpen V
  flat_mem : Glennie.Compact.Affine20.encode20
    (sourceLedger54 P e he hp
      (pullTriple A Glennie.Compact.Sections.flatBase)) ∈ V
  two_orbits : TwoOrbitSections P e he hp V
  finite_observation_test : ScoreComplete P e he hp V

/-- Intrinsic local reconstruction under the exact normalized positive based-cubic
and actual tangent-metric/full-vector-curvature recognition hypotheses. -/
theorem exists_intrinsic_local_reconstruction
    (hR : Nonempty (TangentCurvatureIso P e he)) : Nonempty (Data P e he hp) := by
  obtain ⟨A, hunit, hnorm, hmetric, hproduct, hconnection, hcurvature⟩ :=
    AlbertGeometry.ActualU2NativeGeometry.exists_native_norm_unit_actual_geometry
      P e he hp hR
  obtain ⟨V, hVopen, hflat, htwo, htest⟩ :=
    common_local_reconstruction_of_equiv P e he hp A hunit hmetric hproduct
  exact ⟨Data.mk A hunit hnorm hmetric hproduct hconnection hcurvature
    V hVopen hflat htwo htest⟩

end
end AlbertGeometry.IntrinsicLocalReconstruction
