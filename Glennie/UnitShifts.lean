/- Direct native unit shifts before reverse shear.
The first-unit proof uses direct unrestricted diagonal-first reduction.
Hidden helpers use the SectorModel maps. -/
module
public import Glennie.Native.PairReduction
public import Glennie.SectorFactor
public import Glennie.SectorModel

@[expose] public section
namespace Glennie
noncomputable section

theorem diagonalAlbert_eq (x : Albert) (hx : IsDiagonal x) :
    diagonalAlbert x.d0 x.d1 x.d2 = x := by
  apply Albert.ext <;> simp [diagonalAlbert, hx.1, hx.2.1, hx.2.2]

theorem complexAlbert_eq (x : Albert) (hx : InComplexSector x) :
    complexAlbert x.d0 x.d1 x.d2 (complexPart x.o01)
      (complexPart x.o02) (complexPart x.o12) = x :=
  complexProjection_eq_self x hx

theorem phi_of_diagonal_complex (x y z : Albert) (hx : IsDiagonal x)
    (hy : InComplexSector y) :
    phi x y z = (2*(x.d0-x.d1)*(x.d1-x.d2)*(x.d2-x.d0)*
      (complexPart y.o01*complexPart y.o12*star (complexPart y.o02)).im)*
      (hiddenMatrix z).det.im := by
  conv_lhs => rw [← diagonalAlbert_eq x hx, ← complexAlbert_eq y hy]
  exact phi_diagonal_complex_factor _ _ _ _ _ _ _ _ _ _

/-- Reuse the complete native sector linear map. No coordinate
linearity proof or model-preservation assumption is duplicated here. -/
def hiddenMatrixLinear : Albert →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℂ :=
  sectorHiddenLinear

theorem hiddenMatrix_eq_zero (x : Albert) (hx : InComplexSector x) :
    hiddenMatrix x = 0 := by
  have h : complexAlbertLinear (complexCoordinatesLinear x) = x :=
    complexProjection_eq_self x hx
  rw [← h]
  exact hiddenMatrix_complexAlbert _

theorem diagonal_inComplex (x : Albert) (hx : IsDiagonal x) : InComplexSector x := by
  rw [← diagonalAlbert_eq x hx]
  simp [InComplexSector, OctInComplex, diagonalAlbert]

theorem phi_third_add_unit (x y z : Albert) (t : ℝ) :
    phi x y (z+t • (1 : Albert)) = phi x y z := by
  obtain ⟨g, hx, hy⟩ := universal_pair_reduction x y
  rw [← g.phi_map x y (z+t • (1 : Albert)), ← g.phi_map x y z,
    map_add, map_smul, g.map_unit]
  rw [phi_of_diagonal_complex _ _ _ hx hy, phi_of_diagonal_complex _ _ _ hx hy]
  have hm : hiddenMatrix (g.equiv z+t • (1 : Albert)) = hiddenMatrix (g.equiv z) := by
    change hiddenMatrixLinear (g.equiv z+t • (1 : Albert)) = hiddenMatrixLinear (g.equiv z)
    rw [map_add, map_smul]
    change hiddenMatrix (g.equiv z)+t • hiddenMatrix (1 : Albert) = hiddenMatrix (g.equiv z)
    have hu : InComplexSector (1 : Albert) := by
      simp [InComplexSector, OctInComplex, unit, octScalar]
    rw [hiddenMatrix_eq_zero _ hu, smul_zero, add_zero]
  rw [hm]

/-- Direct unit shift from one unrestricted diagonal-first pair reduction.
No first/third permutation or reverse shear is used. -/
theorem phi_first_add_unit (x y z : Albert) (t : ℝ) :
    phi (x+t • (1 : Albert)) y z = phi x y z := by
  obtain ⟨g,hx,hy⟩ := universal_pair_reduction x y
  rw [← g.phi_map (x+t • (1 : Albert)) y z, ← g.phi_map x y z,
    map_add,map_smul,g.map_unit]
  have hs : IsDiagonal (g.equiv x+t • (1 : Albert)) := by
    simp [IsDiagonal,hx.1,hx.2.1,hx.2.2]
  rw [phi_of_diagonal_complex _ _ _ hs hy,
    phi_of_diagonal_complex _ _ _ hx hy]
  simp only [Albert.add_d0,Albert.add_d1,Albert.add_d2,
    Albert.smul_d0,Albert.smul_d1,Albert.smul_d2,
    one_d0,one_d1,one_d2,mul_one]
  ring

theorem phi_second_add_unit (x y z : Albert) (t : ℝ) :
    phi x (y+t • (1 : Albert)) z = phi x y z := by
  rw [phi_swap_first_two, phi_first_add_unit, phi_swap_first_two, neg_neg]

theorem independent_unit_shifts : IndependentUnitShifts := by
  intro x y z a b c
  rw [phi_first_add_unit, phi_second_add_unit, phi_third_add_unit]

theorem phi_traceless (x y z : Albert) :
    phi (traceless x) (traceless y) (traceless z) = phi x y z := by
  simp only [traceless, sub_eq_add_neg, ← neg_smul,
    phi_first_add_unit, phi_second_add_unit, phi_third_add_unit]


end
end Glennie
