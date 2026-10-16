/- The actual Euclidean27 native model instantiates the conditional intrinsic
local theorem. This source is a separate witness consumer; it does not enter
the capstone proof or weaken its hypotheses. -/
module

public import AlbertGeometry.IntrinsicLocalReconstruction

@[expose] public section
namespace AlbertGeometry.IntrinsicLocalNativeWitness
noncomputable section

open AlbertGeometry.Cubic AlbertGeometry.CubicPolynomialRepresentation
open AlbertGeometry.NativeEuclideanNormBinding
open AlbertGeometry.NativeCurvatureDictionary
open AlbertGeometry.RecognitionFromCurvature
open AlbertGeometry.IntrinsicLocalTransport

abbrev NativeData :=
  IntrinsicLocalReconstruction.Data nativeEuclideanRepresentation
    nativeCoordinateUnit nativeNormalization nativeBaseMetricPositive

/-- In the actual native model, the requested tangent metric and full
vector-valued curvature are compared with themselves. -/
def nativeTangentCurvatureIso :
    TangentCurvatureIso nativeEuclideanRepresentation nativeCoordinateUnit
      nativeNormalization where
  equiv := LinearEquiv.refl ℝ _
  map_metric := by intro u v; rfl
  map_curvature := by intro u v w; rfl

/-- The native cubic discharges normalization, positivity, and the full
tangent-isometry premise, without passing any desired conclusion as input. -/
theorem exists_native_model_data : Nonempty NativeData :=
  IntrinsicLocalReconstruction.exists_intrinsic_local_reconstruction
    nativeEuclideanRepresentation nativeCoordinateUnit nativeNormalization
    nativeBaseMetricPositive ⟨nativeTangentCurvatureIso⟩

/-- A genuine ordered source-frame triple lies in the capstone's common local
domain and has nonzero Phi and six-contrast score in the native model. -/
theorem native_model_nonzero_frame_in_local_domain :
    ∃ d : NativeData, ∃ T : SourceTriple Coordinates,
      (∀ a, SourceFrame nativeEuclideanRepresentation nativeCoordinateUnit
        nativeNormalization nativeBaseMetricPositive (T a)) ∧
      Glennie.Compact.Affine20.encode20
        (sourceLedger54 nativeEuclideanRepresentation nativeCoordinateUnit
          nativeNormalization nativeBaseMetricPositive T) ∈ d.V ∧
      sourcePhi nativeEuclideanRepresentation nativeCoordinateUnit
        nativeNormalization nativeBaseMetricPositive
        (sourceEncoder (T 0)) (sourceEncoder (T 1))
        (sourceEncoder (T 2)) ≠ 0 ∧
      sourceScore nativeEuclideanRepresentation nativeCoordinateUnit
        nativeNormalization nativeBaseMetricPositive T ≠ 0 := by
  obtain ⟨d⟩ := exists_native_model_data
  let T : SourceTriple Coordinates :=
    pullTriple d.A Glennie.Compact.Sections.flatBase
  have hframes : ∀ a, SourceFrame nativeEuclideanRepresentation nativeCoordinateUnit
      nativeNormalization nativeBaseMetricPositive (T a) := by
    apply (sourceTriple_frames_iff nativeEuclideanRepresentation nativeCoordinateUnit
      nativeNormalization nativeBaseMetricPositive d.A d.map_unit d.map_metric
      d.map_product T).mpr
    simpa only [T, mapTriple_pullTriple] using
      Glennie.Compact.Sections.flatBase_frames
  have hb : Glennie.Compact.Affine20.encode20
      (sourceLedger54 nativeEuclideanRepresentation nativeCoordinateUnit
        nativeNormalization nativeBaseMetricPositive T) ∈ d.V := d.flat_mem
  have hscore : sourceScore nativeEuclideanRepresentation nativeCoordinateUnit
      nativeNormalization nativeBaseMetricPositive T ≠ 0 :=
    (d.finite_observation_test T T hframes hframes hb).1
  have hphi : sourcePhi nativeEuclideanRepresentation nativeCoordinateUnit
      nativeNormalization nativeBaseMetricPositive
      (sourceEncoder (T 0)) (sourceEncoder (T 1))
      (sourceEncoder (T 2)) ≠ 0 := by
    intro hz
    have hs := sourceScore_eq_twoPhi nativeEuclideanRepresentation
      nativeCoordinateUnit nativeNormalization nativeBaseMetricPositive
      d.A d.map_unit d.map_metric d.map_product T
    rw [hz, mul_zero] at hs
    exact hscore hs
  exact ⟨d, T, hframes, hb, hphi, hscore⟩

end
end AlbertGeometry.IntrinsicLocalNativeWitness
