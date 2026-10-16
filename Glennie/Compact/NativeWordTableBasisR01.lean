/- Actual native basis realized by the selected 27 Jordan words. -/
module
public import Glennie.Compact.NativeWordTableInverseR01
public import Mathlib.LinearAlgebra.Basis.Basic

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Module Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def synthesisCoordinates : (Fin 27 → ℝ) ≃ₗ[ℝ] (Fin 27 → ℝ) where
  __ := coordinateMatrix.mulVecLin
  invFun := inverseMatrix.mulVecLin
  left_inv c := by
    change inverseMatrix *ᵥ (coordinateMatrix *ᵥ c) = c
    rw [Matrix.mulVec_mulVec, left_inverse, Matrix.one_mulVec]
  right_inv c := by
    change coordinateMatrix *ᵥ (inverseMatrix *ᵥ c) = c
    rw [Matrix.mulVec_mulVec, right_inverse, Matrix.one_mulVec]

def wordCoordinates : Albert ≃ₗ[ℝ] (Fin 27 → ℝ) :=
  flatCoordinates.trans synthesisCoordinates.symm

def wordBasis : Basis (Fin 27) ℝ Albert := Basis.ofEquivFun wordCoordinates

theorem wordBasis_eq_nativeWords (i : Fin 27) : wordBasis i = nativeWords i := by
  rw [show wordBasis i = wordCoordinates.symm (Pi.single i 1) from
    congrFun (Basis.coe_ofEquivFun wordCoordinates) i]
  change decode (coordinateMatrix *ᵥ Pi.single i 1) = nativeWords i
  rw [Matrix.mulVec_single_one]
  exact (nativeWords_decode i).symm

theorem nativeWords_linearIndependent : LinearIndependent ℝ nativeWords := by
  have heq : (wordBasis : Fin 27 → Albert) = nativeWords :=
    funext wordBasis_eq_nativeWords
  rw [← heq]
  exact wordBasis.linearIndependent

theorem nativeWords_span : Submodule.span ℝ (Set.range nativeWords) = ⊤ := by
  have heq : (wordBasis : Fin 27 → Albert) = nativeWords :=
    funext wordBasis_eq_nativeWords
  rw [← heq]
  exact wordBasis.span_eq

end
end Glennie.Compact.NativeWordTableR01
