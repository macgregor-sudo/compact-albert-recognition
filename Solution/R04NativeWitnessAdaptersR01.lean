/- Supporting native witness adapters.
AI-generated under Robert MacGregor's direction; no novelty asserted.
These declarations preserve the central intrinsic statement and Local.Result structure. -/
module
public import Solution.R04IntrinsicUnifiedCandidate
public import AlbertGeometry.IntrinsicLocalNativeWitness

@[expose] public section
namespace Glennie.SubmissionR03
noncomputable section
open Glennie

/-- The actual native carrier satisfies the exact submission vocabulary,
including full ambient product norms. No table equality is assumed. -/
theorem native_match27 :
    Match27 (E := Albert) 1 nativeMarks jordanLinear := by
  constructor
  · intro i k
    rfl
  · intro i k l
    rfl
  · intro i k
    rfl

/-- Explicit application of the existing selected recognition theorem. -/
theorem native_word_recognition :
    ∃! L : Albert →ₗ[ℝ] Albert,
      L 1 = 1 ∧
      (∀ i : Fin 3, L (nativeMarks i) = nativeMarks i) ∧
      (∀ x y : Albert, L (jordan x y) = jordanLinear (L x) (L y)) ∧
      (∀ x y : Albert, Inner.inner ℝ (L x) (L y) = inner x y) ∧
      Function.Injective L ∧
        LinearMap.range L = generated 1 nativeMarks jordanLinear :=
  finite_word_marked_recognition 1 nativeMarks jordanLinear native_match27

end
end Glennie.SubmissionR03

@[expose] public section
namespace Glennie.SubmissionR04Intrinsic.Local
noncomputable section
set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {e : E} {N t : E → ℝ} {a B : E → E → ℝ}
  {j Gamma : E → E → E} {R : E → E → E → E}
  {nativeN : Glennie.Albert → ℝ}

/-- Frame transport derived from the output equivalence, not an extra field
or a premise of recognition. -/
theorem Result.flat_frames
    (d : Result e N t a B j Gamma R nativeN) :
    ∀ f, Frame e t j
      (fun i => d.A.symm (Glennie.SubmissionR03.flatBase f i)) := by
  have hf : ∀ f, Glennie.Frame (Glennie.SubmissionR03.flatBase f) := by
    rw [Glennie.SubmissionR04Intrinsic.LocalBridge.flatBase_binding]
    exact Glennie.Compact.Sections.flatBase_frames
  intro f
  constructor
  · intro i
    rw [d.map_trace, d.A.apply_symm_apply]
    exact (hf f).trace_one i
  · intro i
    apply d.A.injective
    simpa only [d.map_product, d.A.apply_symm_apply] using (hf f).idempotent i
  · intro i k hik
    apply d.A.injective
    simpa only [d.map_product, d.A.apply_symm_apply, map_zero] using
      (hf f).orthogonal i k hik
  · apply d.A.injective
    simpa only [map_add, d.A.apply_symm_apply, d.map_unit] using (hf f).sum_unit

/-- A named derived lemma avoids changing the Result structure or theorem 21. -/
theorem Result.flat_admitted
    (d : Result e N t a B j Gamma R nativeN) :
    Admitted e t j d.V
      (fun f i => d.A.symm (Glennie.SubmissionR03.flatBase f i)) :=
  ⟨d.flat_frames, d.flat_mem⟩

theorem Result.flat_score_ne_zero
    (d : Result e N t a B j Gamma R nativeN) :
    score e t j
      (fun f i => d.A.symm (Glennie.SubmissionR03.flatBase f i)) ≠ 0 := by
  let T : Triple E :=
    fun f i => d.A.symm (Glennie.SubmissionR03.flatBase f i)
  exact (d.score_complete T T d.flat_frames d.flat_frames d.flat_mem).1

theorem Result.flat_atoms_generate
    (d : Result e N t a B j Gamma R nativeN)
    (K : Submodule ℝ E)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, j p q ∈ K)
    (hAtoms : ∀ f i, d.A.symm (Glennie.SubmissionR03.flatBase f i) ∈ K) :
    K = ⊤ :=
  d.atoms_generate _ d.flat_admitted K hJ hAtoms

theorem Result.flat_atom_stabilizer
    (d : Result e N t a B j Gamma R nativeN)
    (g : Automorphism t j)
    (hfix : mapAtoms g
      (fun f i => d.A.symm (Glennie.SubmissionR03.flatBase f i)) =
      (fun f i => d.A.symm (Glennie.SubmissionR03.flatBase f i))) :
    g.equiv = LinearEquiv.refl ℝ E :=
  d.atom_stabilizer _ d.flat_admitted g hfix

theorem Result.flat_atom_derivation
    (d : Result e N t a B j Gamma R nativeN)
    (D : E →ₗ[ℝ] E)
    (hD : ∀ p q, D (j p q) = j (D p) q + j p (D q))
    (hkill : ∀ f i, D (d.A.symm (Glennie.SubmissionR03.flatBase f i)) = 0) :
    D = 0 :=
  d.atom_derivation _ d.flat_admitted D hD hkill

end
end Glennie.SubmissionR04Intrinsic.Local

@[expose] public section
namespace Glennie.SubmissionR04Intrinsic
noncomputable section
open AlbertGeometry.CubicPolynomialRepresentation
open AlbertGeometry.NativeEuclideanNormBinding

/-- The existing native symmetric trilinear form in BasedCubic vocabulary. -/
def nativeBasedCubic : BasedCubic Coordinates where
  form := nativeEuclideanRepresentation.form
  swap12 := nativeEuclideanRepresentation.swap12
  swap23 := nativeEuclideanRepresentation.swap23

theorem toSource_nativeBasedCubic :
    toSource nativeBasedCubic = nativeEuclideanRepresentation := rfl

theorem nativeBasedCubic_normalized :
    cubic nativeBasedCubic nativeCoordinateUnit = 1 :=
  AlbertGeometry.NativeCurvatureDictionary.nativeNormalization

theorem nativeBasedCubic_positive (x : Coordinates) (hx : x ≠ 0) :
    0 < metric nativeBasedCubic nativeCoordinateUnit x x :=
  AlbertGeometry.NativeCurvatureDictionary.nativeBaseMetricPositive x hx

/-- Satisfiability of the exact tangent-only entrance in theorem 21.
The existing native identity isometry is converted through a proved iff,
then the NativeTangent/AlbertRecognition.V dictionary is composed explicitly. -/
theorem nativeBasedCubic_match :
    ∃ F : NativeTangent ≃ₗ[ℝ] tangent nativeBasedCubic nativeCoordinateUnit,
      (∀ x y : NativeTangent,
        metric nativeBasedCubic nativeCoordinateUnit
          (F x : Coordinates) (F y : Coordinates) = nativeMetric x y) ∧
      (∀ x y z : NativeTangent,
        independentCurvature nativeBasedCubic nativeCoordinateUnit
          (F x) (F y) (F z) = F (nativeCurvature x y z)) := by
  have hActual : Nonempty
      (AlbertGeometry.RecognitionFromCurvature.TangentCurvatureIso
        (toSource nativeBasedCubic) nativeCoordinateUnit
        nativeBasedCubic_normalized) :=
    ⟨AlbertGeometry.IntrinsicLocalNativeWitness.nativeTangentCurvatureIso⟩
  obtain ⟨F, hm, hc⟩ :=
    (actualIso_iff_independentRaisedFrame nativeBasedCubic nativeCoordinateUnit
      nativeBasedCubic_normalized nativeBasedCubic_positive).mp hActual
  refine ⟨nativeToSource.trans F, ?_, ?_⟩
  · intro x y
    change metric nativeBasedCubic nativeCoordinateUnit
      (F (nativeToSource x) : Coordinates) (F (nativeToSource y) : Coordinates) =
      nativeMetric x y
    exact (hm (nativeToSource x) (nativeToSource y)).trans
      (nativeToSource_metric x y).symm
  · intro x y z
    change independentCurvature nativeBasedCubic nativeCoordinateUnit
      (F (nativeToSource x)) (F (nativeToSource y)) (F (nativeToSource z)) =
      F (nativeToSource (nativeCurvature x y z))
    simpa only [nativeCurvatureOnV, LinearEquiv.symm_apply_apply] using
      hc (nativeToSource x) (nativeToSource y) (nativeToSource z)

/-- An application of the unchanged central selected theorem. -/
theorem native_reconstruction_result :
    Nonempty (ReconstructionResult nativeBasedCubic nativeCoordinateUnit) :=
  intrinsic_local_reconstruction nativeBasedCubic nativeCoordinateUnit
    nativeBasedCubic_normalized nativeBasedCubic_positive
    nativeBasedCubic_match

/-- One returned A and its very same V have an actual admitted triple with
nonzero score. The preceding derived lemmas instantiate all three atom results. -/
theorem native_reconstruction_with_local_witness :
    ∃ d : ReconstructionResult nativeBasedCubic nativeCoordinateUnit,
      ∃ T : Local.Triple Coordinates,
        Local.Admitted nativeCoordinateUnit
          (fun x => traceAt nativeBasedCubic nativeCoordinateUnit x)
          (product nativeBasedCubic nativeCoordinateUnit) d.V T ∧
        Local.score nativeCoordinateUnit
          (fun x => traceAt nativeBasedCubic nativeCoordinateUnit x)
          (product nativeBasedCubic nativeCoordinateUnit) T ≠ 0 := by
  obtain ⟨d⟩ := native_reconstruction_result
  exact ⟨d, (fun f i => d.A.symm (Glennie.SubmissionR03.flatBase f i)),
    d.flat_admitted, d.flat_score_ne_zero⟩

end
end Glennie.SubmissionR04Intrinsic
