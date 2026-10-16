/- The actual nine-dimensional compact complex sector and its projection.
No spanning or equality conclusion is assumed in a structure field. -/
module
public import Glennie.Sector
public import Glennie.Hilbert
public import Glennie.Obligations
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section
namespace Glennie
noncomputable section

abbrev ComplexCoordinates := (ℝ × ℝ × ℝ) × (ℂ × ℂ × ℂ)

def complexAlbertLinear : ComplexCoordinates →ₗ[ℝ] Albert where
  toFun q := complexAlbert q.1.1 q.1.2.1 q.1.2.2 q.2.1 q.2.2.1 q.2.2.2
  map_add' x y := by
    ext <;> simp [complexAlbert, complexOct]
  map_smul' r x := by
    ext <;> simp [complexAlbert, complexOct, smul_eq_mul]

def complexCoordinatesLinear : Albert →ₗ[ℝ] ComplexCoordinates where
  toFun x := ((x.d0,x.d1,x.d2),
    (complexPart x.o01,complexPart x.o02,complexPart x.o12))
  map_add' x y := by
    ext <;> simp [complexPart]
    all_goals apply Complex.ext <;> simp
  map_smul' r x := by
    ext <;> simp [complexPart, smul_eq_mul]
    all_goals apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

theorem complexCoordinates_albert (q : ComplexCoordinates) :
    complexCoordinatesLinear (complexAlbertLinear q) = q := rfl

theorem complexAlbert_coordinates (x : Albert) :
    complexAlbertLinear (complexCoordinatesLinear x) = complexProjection x := rfl

theorem complexAlbertLinear_injective : Function.Injective complexAlbertLinear := by
  intro x y h
  have h' := congrArg complexCoordinatesLinear h
  simpa only [complexCoordinates_albert] using h'

def complexSector : Submodule ℝ Albert := LinearMap.range complexAlbertLinear

theorem complexSector_finrank : Module.finrank ℝ complexSector = 9 := by
  change Module.finrank ℝ (LinearMap.range complexAlbertLinear) = 9
  rw [← (LinearEquiv.ofInjective complexAlbertLinear complexAlbertLinear_injective).finrank_eq]
  simp [ComplexCoordinates, Complex.finrank_real_complex]

theorem complexProjection_mem (x : Albert) : complexProjection x ∈ complexSector :=
  ⟨complexCoordinatesLinear x, complexAlbert_coordinates x⟩

theorem complexProjection_eq_self (x : Albert) (hx : InComplexSector x) :
    complexProjection x = x := by
  rcases hx with ⟨⟨h01j,h01k,h01s⟩,⟨h02j,h02k,h02s⟩,⟨h12j,h12k,h12s⟩⟩
  ext <;> simp [complexProjection, complexPart, complexOct,
    h01j,h01k,h01s,h02j,h02k,h02s,h12j,h12k,h12s]

theorem complexSector_mem_iff (x : Albert) : x ∈ complexSector ↔ InComplexSector x := by
  constructor
  · rintro ⟨q, rfl⟩
    simp [complexAlbertLinear, complexAlbert, complexOct, InComplexSector, OctInComplex]
  · intro hx
    rw [← complexProjection_eq_self x hx]
    exact complexProjection_mem x

theorem complexSector_jordan (x y : Albert) (hx : InComplexSector x)
    (hy : InComplexSector y) : InComplexSector (jordan x y) := by
  rw [← complexProjection_eq_self x hx, ← complexProjection_eq_self y hy]
  simp [InComplexSector, OctInComplex, complexProjection, complexPart, complexOct,
    jordan_o01, jordan_o02, jordan_o12, octMul, octConj,
    Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

theorem nine_independent_span_complexSector (v : Fin 3 × Fin 3 → Albert)
    (hv : ∀ i, InComplexSector (v i)) (hi : LinearIndependent ℝ v) :
    Submodule.span ℝ (Set.range v) = complexSector := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (complexSector_mem_iff _).mpr (hv i)
  · rw [finrank_span_eq_card hi, complexSector_finrank]
    norm_num

theorem complexProjection_zero_of_perp (z : Albert)
    (hz : ∀ v ∈ complexSector, inner v z = 0) : complexProjection z = 0 := by
  apply (inner_self_eq_zero (complexProjection z)).mp
  have h := hz _ (complexProjection_mem z)
  have hp : inner (complexProjection z) z =
      inner (complexProjection z) (complexProjection z) := by
    calc
      _ = inner (complexProjection z)
          (complexProjection z + hiddenAlbert (hiddenMatrix z)) :=
            congrArg (inner (complexProjection z)) (complex_hidden_decomposition z).symm
      _ = _ := by rw [inner_add_right, complex_hidden_orthogonal, add_zero]
  exact hp.symm.trans h

theorem complexProjection_zero_of_nine_perp (v : Fin 3 × Fin 3 → Albert)
    (hv : ∀ i, InComplexSector (v i)) (hi : LinearIndependent ℝ v) (z : Albert)
    (hz : ∀ i, inner (v i) z = 0) : complexProjection z = 0 := by
  let f : Albert →ₗ[ℝ] ℝ :=
    { toFun := fun x => inner x z
      map_add' := fun x y => inner_add_left x y z
      map_smul' := fun r x => inner_smul_left r x z }
  have hle : Submodule.span ℝ (Set.range v) ≤ LinearMap.ker f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hz i
  apply complexProjection_zero_of_perp
  intro x hx
  apply hle
  rwa [nine_independent_span_complexSector v hv hi]

end
end Glennie
