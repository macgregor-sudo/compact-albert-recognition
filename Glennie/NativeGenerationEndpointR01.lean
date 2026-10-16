/- Native unital generation endpoint.
The preceding coordinate stages supply generation directly.
No classification, stronger real-slot normal form, or conclusion axiom. -/
module
public import Glennie.NativeGenerationHiddenCompletionR01
public import Glennie.UnitShifts

@[expose] public section
namespace Glennie.NativeGenerationEndpointR01
noncomputable section
open Glennie.NativeGenerationComplexSectorR01
open Glennie.NativeGenerationHiddenCompletionR01

/-- Native unital generation in the reduced diagonal/complex position. -/
theorem eq_top_of_phi_ne_zero_diagonal_complex
    (K : Submodule ℝ Albert) (h1 : (1 : Albert) ∈ K)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (x y z : Albert) (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K)
    (hxd : IsDiagonal x) (hyc : InComplexSector y)
    (hphi : phi x y z ≠ 0) : K = ⊤ := by
  have hF := phi_of_diagonal_complex x y z hxd hyc
  have hab : x.d0 - x.d1 ≠ 0 := by
    intro h
    apply hphi
    rw [hF, h]
    ring
  have hbc : x.d1 - x.d2 ≠ 0 := by
    intro h
    apply hphi
    rw [hF, h]
    ring
  have hca : x.d2 - x.d0 ≠ 0 := by
    intro h
    apply hphi
    rw [hF, h]
    ring
  have ht : (complexPart y.o01 * complexPart y.o12 * star (complexPart y.o02)).im ≠ 0 := by
    intro h
    apply hphi
    rw [hF, h]
    ring
  have hd : (hiddenMatrix z).det ≠ 0 := by
    intro h
    apply hphi
    rw [hF, h]
    simp
  have hC : complexSector ≤ K := complexSector_le_of_regular_triangle K h1 hJ
    x.d0 x.d1 x.d2 y.d0 y.d1 y.d2
    (complexPart y.o01) (complexPart y.o02) (complexPart y.o12)
    (by rw [diagonalAlbert_eq x hxd]; exact hx)
    (by rw [complexAlbert_eq y hyc]; exact hy)
    hab hbc hca ht
  exact eq_top_of_complexSector_le_hidden_det K hJ hC z hz hd

/-- Definition-free full unital generation: every native product-closed real
submodule containing the unit and a nonzero-Phi triple is the entire Albert space. -/
theorem eq_top_of_phi_ne_zero
    (K : Submodule ℝ Albert) (h1 : (1 : Albert) ∈ K)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (x y z : Albert) (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K)
    (hphi : phi x y z ≠ 0) : K = ⊤ := by
  obtain ⟨g, hxd, hyc⟩ := universal_pair_reduction x y
  let L : Submodule ℝ Albert := K.map g.equiv.toLinearMap
  have hL1 : (1 : Albert) ∈ L := ⟨1, h1, g.map_unit⟩
  have hLJ : ∀ p ∈ L, ∀ q ∈ L, jordan p q ∈ L := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    exact ⟨jordan p q, hJ p hp q hq, g.map_jordan p q⟩
  have hL : L = ⊤ := eq_top_of_phi_ne_zero_diagonal_complex L hL1 hLJ
    (g.equiv x) (g.equiv y) (g.equiv z)
    ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩ hxd hyc
    (by rw [g.phi_map]; exact hphi)
  apply top_unique
  intro t ht
  have hgt : g.equiv t ∈ L := by rw [hL]; trivial
  rcases hgt with ⟨s, hs, he⟩
  have hst : s = t := g.equiv.injective he
  exact hst ▸ hs

end
end Glennie.NativeGenerationEndpointR01
