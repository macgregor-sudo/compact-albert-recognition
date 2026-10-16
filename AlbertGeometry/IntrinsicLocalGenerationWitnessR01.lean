/- Nonvacuity of the generation extension in the actual native model. -/
module
public import AlbertGeometry.IntrinsicLocalGenerationCapstoneR01
public import AlbertGeometry.IntrinsicLocalNativeWitness

@[expose] public section
namespace AlbertGeometry.IntrinsicLocalGenerationWitnessR01
noncomputable section
open AlbertGeometry.IntrinsicLocalTransport
open AlbertGeometry.IntrinsicLocalNativeWitness
open AlbertGeometry.IntrinsicGenerationStabilizersR01
open AlbertGeometry.CubicPolynomialRepresentation
open AlbertGeometry.NativeEuclideanNormBinding

/-- An actual ordered source-frame triple lies in the original local domain,
and its labeled atoms generate the recovered source algebra there. -/
theorem native_model_local_atoms_generate :
    ∃ d : NativeData, ∃ T : SourceTriple Coordinates,
      (∀ a, SourceFrame nativeEuclideanRepresentation nativeCoordinateUnit
        nativeNormalization nativeBaseMetricPositive (T a)) ∧
      Glennie.Compact.Affine20.encode20
        (sourceLedger54 nativeEuclideanRepresentation nativeCoordinateUnit
          nativeNormalization nativeBaseMetricPositive T) ∈ d.V ∧
      ∀ K : Submodule ℝ Coordinates,
        (∀ p ∈ K, ∀ q ∈ K,
          sourceProduct nativeEuclideanRepresentation nativeCoordinateUnit
            nativeNormalization nativeBaseMetricPositive p q ∈ K) →
        (∀ a i, T a i ∈ K) → K = ⊤ := by
  obtain ⟨d, T, hT, hb, _, _⟩ := native_model_nonzero_frame_in_local_domain
  exact ⟨d, T, hT, hb,
    fun K hJ hAtoms => local_source_atoms_generate d T hT hb K hJ hAtoms⟩

end
end AlbertGeometry.IntrinsicLocalGenerationWitnessR01
