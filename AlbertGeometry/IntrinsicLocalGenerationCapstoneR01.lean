/- Intrinsic local reconstruction with generation. -/
module
public import AlbertGeometry.IntrinsicGenerationStabilizersR01

@[expose] public section
namespace AlbertGeometry.IntrinsicLocalGenerationCapstoneR01
noncomputable section
open AlbertGeometry.Cubic AlbertGeometry.BasedNormAdjointTransport
open AlbertGeometry.RecognitionFromCurvature
open AlbertGeometry.IntrinsicLocalTransport
open AlbertGeometry.IntrinsicGenerationStabilizersR01

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
variable (P : SymmetricTrilinearForm E) (e : E)
  (he : diagonalCubic P.form e = 1)
  (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u)

/-- Recognition yields the original two-orbit/score data together with full
unital generation and trivial stabilizers for actual ordered source frames
in exactly its established local ledger domain. -/
theorem exists_intrinsic_local_reconstruction_with_generation
    (hR : Nonempty (TangentCurvatureIso P e he)) :
    ∃ d : IntrinsicLocalReconstruction.Data P e he hp,
      (∀ (T : SourceTriple E), (∀ a, SourceFrame P e he hp (T a)) →
        Glennie.Compact.Affine20.encode20 (sourceLedger54 P e he hp T) ∈ d.V →
        ∀ K : Submodule ℝ E,
          (∀ p ∈ K, ∀ q ∈ K, sourceProduct P e he hp p q ∈ K) →
          (∀ a i, T a i ∈ K) → K = ⊤) ∧
      (∀ (T : SourceTriple E), (∀ a, SourceFrame P e he hp (T a)) →
        Glennie.Compact.Affine20.encode20 (sourceLedger54 P e he hp T) ∈ d.V →
        ∀ g : SourceAutomorphism P e he hp,
          sourceMapAtoms P e he hp g T = T → g.equiv = LinearEquiv.refl ℝ E) ∧
      (∀ (T : SourceTriple E), (∀ a, SourceFrame P e he hp (T a)) →
        Glennie.Compact.Affine20.encode20 (sourceLedger54 P e he hp T) ∈ d.V →
        ∀ D : E →ₗ[ℝ] E,
          (∀ p q, D (sourceProduct P e he hp p q) =
            sourceProduct P e he hp (D p) q + sourceProduct P e he hp p (D q)) →
          (∀ a i, D (T a i) = 0) → D = 0) := by
  obtain ⟨d⟩ := IntrinsicLocalReconstruction.exists_intrinsic_local_reconstruction
    P e he hp hR
  refine ⟨d, ?_, ?_, ?_⟩
  · intro T hT hb K hJ hAtoms
    exact local_source_atoms_generate d T hT hb K hJ hAtoms
  · intro T hT hb g hfix
    exact local_source_atom_stabilizer d T hT hb g hfix
  · intro T hT hb D hD hkill
    exact local_source_atom_derivation d T hT hb D hD hkill

end
end AlbertGeometry.IntrinsicLocalGenerationCapstoneR01
