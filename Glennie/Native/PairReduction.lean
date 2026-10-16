/- Actual compact diagonal/complex pair reduction.
Every reduction map is a constructed native product- and trace-preserving equivalence.
No spectral, triality-transitivity, or pair-reduction conclusion is a hypothesis.
-/
module

public import Glennie.Diagonalization
public import Glennie.Native.PairNormalization
public import Glennie.Theorems.OctonionAutomorphisms

@[expose] public section

namespace Glennie
noncomputable section

set_option maxHeartbeats 2000000

@[simp] theorem octInComplex_scalar (r : ℝ) : OctInComplex (octScalar r) := by
  simp [OctInComplex, octScalar]

theorem octInComplex_standardLine (z : ℂ) : OctInComplex (octComplexLine octI z) := by
  simp [OctInComplex, octComplexLine, octI, quatI, octScalar, smul_eq_mul]

/-- A genuine diagonal related triple fixes every real scalar. -/
theorem diagonalOctTriple_scalar (g : OctRelatedTriple) (hg : DiagonalOctTriple g)
    (r : ℝ) : g.A (octScalar r) = octScalar r := by
  have hs : r • octScalar 1 = octScalar r := by simpa using octScalar_smul r 1
  rw [← hs, map_smul, hg.2.2]

/-- Every octonion, including real elements and zero, is transported into the
standard complex line by a genuine scalar-fixing octonion automorphism. -/
theorem exists_octAutomorphism_to_complex (v : Octonion) :
    ∃ g : OctRelatedTriple, DiagonalOctTriple g ∧ OctInComplex (g.C v) := by
  obtain ⟨I, hi, hn, z, hz⟩ := exists_octComplexLine v
  obtain ⟨g, hg, hI⟩ := exists_octAutomorphism_to_i I hi hn
  have hv : g.A v = octComplexLine octI z := by
    simp only [← hz, octComplexLine, map_add, map_smul, hg.2.2, hI]
  refine ⟨g, hg, ?_⟩
  rw [hg.2.1, hv]
  exact octInComplex_standardLine z

/-- Any actual related-triple Albert map preserves the entire diagonal subspace. -/
theorem relatedTriple_isDiagonal (g : OctRelatedTriple) (x : Albert)
    (hx : IsDiagonal x) : IsDiagonal (g.compactAutomorphism.equiv x) := by
  change g.A x.o01 = 0 ∧ g.C x.o02 = 0 ∧ g.B x.o12 = 0
  simp only [hx.1, hx.2.1, hx.2.2, map_zero, and_self]

/-- Unrestricted native compact pair reduction, including zero slots and repeated
spectra. Its dependencies are actual complete diagonalization and constructed maps. -/
theorem universal_pair_reduction : UniversalPairReduction := by
  intro x y
  obtain ⟨d, hdx⟩ := native_diagonalization x
  let y' := d.equiv y
  obtain ⟨t,a,b,ha,hb,h01,h12⟩ := octTwoSlotsReal y'.o01 y'.o12
  obtain ⟨k,hk,h02⟩ := exists_octAutomorphism_to_complex (t.C y'.o02)
  refine ⟨k.compactAutomorphism.comp (t.compactAutomorphism.comp d), ?_, ?_⟩
  · change IsDiagonal (k.compactAutomorphism.equiv
      (t.compactAutomorphism.equiv (d.equiv x)))
    exact relatedTriple_isDiagonal k _ (relatedTriple_isDiagonal t _ hdx)
  · change OctInComplex (k.A (t.A y'.o01)) ∧
      OctInComplex (k.C (t.C y'.o02)) ∧ OctInComplex (k.B (t.B y'.o12))
    rw [h01, h12, diagonalOctTriple_scalar k hk a, hk.1,
      diagonalOctTriple_scalar k hk b]
    exact ⟨octInComplex_scalar a, h02, octInComplex_scalar b⟩

end
end Glennie
