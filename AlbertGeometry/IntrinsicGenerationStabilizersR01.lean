/- Intrinsic extension of the local reconstruction capstone.
Uses recognition/local Data and native unital generation. -/
module
public import Glennie.NativeGenerationEndpointR01
public import AlbertGeometry.IntrinsicLocalReconstruction

@[expose] public section
namespace AlbertGeometry.IntrinsicGenerationStabilizersR01
noncomputable section
open Glennie
open Glennie.NativeGenerationEndpointR01
open AlbertGeometry.Cubic AlbertGeometry.BasedNormAdjointTransport
open AlbertGeometry.IntrinsicLocalTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
variable {P : SymmetricTrilinearForm E} {e : E}
  {he : diagonalCubic P.form e = 1}
  {hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u}

/-- The existing recognized product and nonzero intrinsic scalar force full
unital generation in every real source submodule. -/
theorem source_submodule_eq_top_of_phi
    (d : IntrinsicLocalReconstruction.Data P e he hp)
    (K : Submodule ℝ E) (hu : e ∈ K)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, sourceProduct P e he hp p q ∈ K)
    (x y z : E) (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K)
    (hphi : sourcePhi P e he hp x y z ≠ 0) : K = ⊤ := by
  let L : Submodule ℝ Albert := K.map d.A.toLinearMap
  have hL : L = ⊤ := eq_top_of_phi_ne_zero L
    ⟨e, hu, d.map_unit⟩
    (by
      rintro _ ⟨p, hpk, rfl⟩ _ ⟨q, hqk, rfl⟩
      exact ⟨sourceProduct P e he hp p q, hJ p hpk q hqk,
        sourceProduct_map P e he hp d.A d.map_product p q⟩)
    (d.A x) (d.A y) (d.A z) ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩
    (by
      rw [← sourcePhi_eq P e he hp d.A d.map_unit d.map_metric d.map_product]
      exact hphi)
  apply top_unique
  intro t ht
  have hAt : d.A t ∈ L := by rw [hL]; trivial
  rcases hAt with ⟨s, hs, heq⟩
  exact d.A.injective heq ▸ hs

theorem source_unit_left (d : IntrinsicLocalReconstruction.Data P e he hp) (t : E) :
    sourceProduct P e he hp e t = t := by
  apply d.A.injective
  rw [sourceProduct_map P e he hp d.A d.map_product, d.map_unit, jordan_unit_left]

theorem source_unit_right (d : IntrinsicLocalReconstruction.Data P e he hp) (t : E) :
    sourceProduct P e he hp t e = t := by
  apply d.A.injective
  rw [sourceProduct_map P e he hp d.A d.map_product, d.map_unit, jordan_unit_right]

theorem source_automorphism_fixes_all
    (d : IntrinsicLocalReconstruction.Data P e he hp)
    (g : SourceAutomorphism P e he hp) (x y z : E)
    (hphi : sourcePhi P e he hp x y z ≠ 0)
    (hx : g.equiv x = x) (hy : g.equiv y = y) (hz : g.equiv z = z) :
    ∀ t : E, g.equiv t = t := by
  let K : Submodule ℝ E :=
    { carrier := {t | g.equiv t = t}
      zero_mem' := by simp
      add_mem' := by
        intro p q hp hq
        change g.equiv p = p at hp
        change g.equiv q = q at hq
        change g.equiv (p + q) = p + q
        rw [map_add, hp, hq]
      smul_mem' := by
        intro r p hp
        change g.equiv p = p at hp
        change g.equiv (r • p) = r • p
        rw [map_smul, hp] }
  have hunit : g.equiv e = e := by
    have h := g.map_product e (g.equiv.symm e)
    simpa only [source_unit_left d, source_unit_right d,
      LinearEquiv.apply_symm_apply] using h.symm
  have hK : K = ⊤ := source_submodule_eq_top_of_phi d K hunit
    (by
      intro p hpk q hqk
      change g.equiv p = p at hpk
      change g.equiv q = q at hqk
      change g.equiv (sourceProduct P e he hp p q) = sourceProduct P e he hp p q
      rw [g.map_product, hpk, hqk]) x y z hx hy hz hphi
  intro t
  have ht : t ∈ K := by rw [hK]; trivial
  exact ht

theorem source_derivation_eq_zero
    (d : IntrinsicLocalReconstruction.Data P e he hp)
    (D : E →ₗ[ℝ] E)
    (hD : ∀ p q, D (sourceProduct P e he hp p q) =
      sourceProduct P e he hp (D p) q + sourceProduct P e he hp p (D q))
    (x y z : E) (hphi : sourcePhi P e he hp x y z ≠ 0)
    (hx : D x = 0) (hy : D y = 0) (hz : D z = 0) : D = 0 := by
  have hu : D e = 0 := by
    have h := hD e e
    rw [source_unit_left d e, source_unit_right d (D e), source_unit_left d (D e)] at h
    exact add_left_cancel (show D e + D e = D e + 0 by simpa using h.symm)
  have hK : LinearMap.ker D = ⊤ := source_submodule_eq_top_of_phi d (LinearMap.ker D) hu
    (by
      intro p hpk q hqk
      change D p = 0 at hpk
      change D q = 0 at hqk
      change D (sourceProduct P e he hp p q) = 0
      apply d.A.injective
      rw [hD p q, hpk, hqk, map_add,
        sourceProduct_map P e he hp d.A d.map_product,
        sourceProduct_map P e he hp d.A d.map_product, map_zero]
      simp) x y z hx hy hz hphi
  apply LinearMap.ext
  intro t
  have ht : t ∈ LinearMap.ker D := by rw [hK]; trivial
  exact ht

/-- Local frame admissibility supplies nonvanishing through the existing
finite-observation test on precisely d.V. -/
theorem local_source_phi_ne_zero
    (d : IntrinsicLocalReconstruction.Data P e he hp) (T : SourceTriple E)
    (hT : ∀ a, SourceFrame P e he hp (T a))
    (hb : Glennie.Compact.Affine20.encode20 (sourceLedger54 P e he hp T) ∈ d.V) :
    sourcePhi P e he hp (sourceEncoder (T 0))
      (sourceEncoder (T 1)) (sourceEncoder (T 2)) ≠ 0 := by
  have hs := (d.finite_observation_test T T hT hT hb).1
  intro hz
  apply hs
  rw [sourceScore_eq_twoPhi P e he hp d.A d.map_unit d.map_metric d.map_product,
    hz, mul_zero]

theorem local_source_atom_stabilizer
    (d : IntrinsicLocalReconstruction.Data P e he hp) (T : SourceTriple E)
    (hT : ∀ a, SourceFrame P e he hp (T a))
    (hb : Glennie.Compact.Affine20.encode20 (sourceLedger54 P e he hp T) ∈ d.V)
    (g : SourceAutomorphism P e he hp)
    (hfix : sourceMapAtoms P e he hp g T = T) :
    g.equiv = LinearEquiv.refl ℝ E := by
  have hf : ∀ a i, g.equiv (T a i) = T a i := by
    intro a i
    exact congrFun (congrFun hfix a) i
  apply LinearEquiv.ext
  apply source_automorphism_fixes_all d g
    (sourceEncoder (T 0)) (sourceEncoder (T 1)) (sourceEncoder (T 2))
    (local_source_phi_ne_zero d T hT hb)
  all_goals simp only [sourceEncoder, map_sub, hf]

theorem local_source_atoms_generate
    (d : IntrinsicLocalReconstruction.Data P e he hp) (T : SourceTriple E)
    (hT : ∀ a, SourceFrame P e he hp (T a))
    (hb : Glennie.Compact.Affine20.encode20 (sourceLedger54 P e he hp T) ∈ d.V)
    (K : Submodule ℝ E)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, sourceProduct P e he hp p q ∈ K)
    (hAtoms : ∀ a i, T a i ∈ K) : K = ⊤ := by
  have hu : e ∈ K := by
    rw [← (hT 0).sum_unit]
    exact K.add_mem (K.add_mem (hAtoms 0 0) (hAtoms 0 1)) (hAtoms 0 2)
  apply source_submodule_eq_top_of_phi d K hu hJ
    (sourceEncoder (T 0)) (sourceEncoder (T 1)) (sourceEncoder (T 2))
  · exact K.sub_mem (hAtoms 0 2) (hAtoms 0 0)
  · exact K.sub_mem (hAtoms 1 2) (hAtoms 1 0)
  · exact K.sub_mem (hAtoms 2 2) (hAtoms 2 0)
  · exact local_source_phi_ne_zero d T hT hb

theorem local_source_atom_derivation
    (d : IntrinsicLocalReconstruction.Data P e he hp) (T : SourceTriple E)
    (hT : ∀ a, SourceFrame P e he hp (T a))
    (hb : Glennie.Compact.Affine20.encode20 (sourceLedger54 P e he hp T) ∈ d.V)
    (D : E →ₗ[ℝ] E)
    (hD : ∀ p q, D (sourceProduct P e he hp p q) =
      sourceProduct P e he hp (D p) q + sourceProduct P e he hp p (D q))
    (hkill : ∀ a i, D (T a i) = 0) : D = 0 := by
  apply source_derivation_eq_zero d D hD
    (sourceEncoder (T 0)) (sourceEncoder (T 1)) (sourceEncoder (T 2))
    (local_source_phi_ne_zero d T hT hb)
  all_goals simp only [sourceEncoder, map_sub, hkill, sub_zero]

end
end AlbertGeometry.IntrinsicGenerationStabilizersR01
