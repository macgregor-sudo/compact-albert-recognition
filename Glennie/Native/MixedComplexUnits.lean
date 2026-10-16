/- Complete complex-unit alternative for the small mixed residual.
All nine complex input units and all nine complex output entries are retained.
No residual Hermiticity, assumed coefficient identity, genericity or factor
conclusion is a field/premise. -/
module
public import Glennie.Theorems.SectorContraction
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Module

@[expose] public section
namespace Glennie
noncomputable section
namespace MixedComplexUnits
open scoped BigOperators

set_option maxHeartbeats 2000000

abbrev Mat := Matrix (Fin 3) (Fin 3) ℂ

def diagonalInput (a b c : ℂ) : Mat := Matrix.diagonal ![a,b,c]
def symmProduct (D H : Mat) : Mat := (1/2:ℂ) • (D*H+H*D)
def adjugateCommutator (D H : Mat) : Mat :=
  H.adjugate*D.adjugate-D.adjugate*H.adjugate
def complexCommutator (D H K : Mat) : Mat := D*H*K*H*D-H*D*K*D*H

def residual (D H K : Mat) : Mat :=
  SectorContraction.tracePolar (complexCommutator D H K) (symmProduct D H) -
    adjugateCommutator D H * symmProduct D H * K +
    K * symmProduct D H * adjugateCommutator D H

/-- Scalar normalization is generic in both matrices; no residual identity
or commutativity of matrices is assumed. Only the complex entry ring commutes. -/
private theorem tracePolar_smul_left (r : ℂ) (G B : Mat) :
    SectorContraction.tracePolar (r • G) B =
      r • SectorContraction.tracePolar G B := by
  ext i j
  simp only [SectorContraction.tracePolar, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_smul, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
  simp only [smul_eq_mul]
  ring

/-- Actual complex linearity, for arbitrary fixed complex D,H. Every K appears
without conjugation. This theorem asserts only linearity, not residual=0. -/
def residualComplexLinear (D H : Mat) : Mat →ₗ[ℂ] Mat where
  toFun := residual D H
  map_add' K L := by
    simp only [residual, complexCommutator, SectorContraction.tracePolar,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.trace_add, Matrix.trace_sub, mul_add, mul_sub,
      add_smul, sub_smul, smul_add, smul_sub]
    module
  map_smul' r K := by
    have hQ : complexCommutator D H (r • K) =
        r • complexCommutator D H K := by
      simp only [complexCommutator, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
    change residual D H (r • K) = r • residual D H K
    unfold residual
    rw [hQ, tracePolar_smul_left]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_sub]

/-- A genuine real-linear interface follows by restriction, without imposing
Hermiticity on the residual or on its input. -/
def residualRealLinear (D H : Mat) : Mat →ₗ[ℝ] Mat :=
  (residualComplexLinear D H).restrictScalars ℝ

/-- Explicit application bridges isolate the computational toFun from the
linearity proof fields and the restriction-of-scalars wrapper. -/
private theorem residualComplexLinear_apply (D H K : Mat) :
    residualComplexLinear D H K = residual D H K := rfl

private theorem residualRealLinear_apply (D H K : Mat) :
    residualRealLinear D H K = residual D H K := by
  simpa only [residualRealLinear, LinearMap.restrictScalars_apply] using
    residualComplexLinear_apply D H K

def matrixUnit (i j : Fin 3) : Mat := Matrix.single i j 1

/-- Full arbitrary-matrix reconstruction, including imaginary diagonal and all
lower entries. There is no Hermitian coordinate omission. -/
theorem reconstruct (K : Mat) :
    K = ∑ i : Fin 3, ∑ j : Fin 3, K i j • matrixUnit i j := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [matrixUnit, Fin.sum_univ_three, Matrix.single_apply, smul_eq_mul]

/-- Exact real-linear expansion of the same complex reconstruction. It is useful
when an external consumer explicitly works over the native real carrier. -/
theorem residual_real_reconstruction (D H K : Mat) :
    residual D H K = ∑ i : Fin 3, ∑ j : Fin 3,
      ((K i j).re • residual D H (matrixUnit i j) +
      (K i j).im • residual D H (Complex.I • matrixUnit i j)) := by
  change residualRealLinear D H K = _
  have hc (i j : Fin 3) :
      K i j • matrixUnit i j =
        (K i j).re • matrixUnit i j +
        (K i j).im • (Complex.I • matrixUnit i j) := by
    ext a b
    by_cases h : i = a ∧ j = b
    · apply Complex.ext <;>
        simp [matrixUnit, Matrix.single_apply, h, Complex.smul_re,
          Complex.smul_im, smul_eq_mul, Complex.mul_re, Complex.mul_im]
    · apply Complex.ext <;>
        simp [matrixUnit, Matrix.single_apply, h, Complex.smul_re,
          Complex.smul_im, smul_eq_mul, Complex.mul_re, Complex.mul_im]
  conv_lhs => rw [reconstruct K]
  simp only [hc, map_sum, map_add, map_smul]
  simp only [residualRealLinear_apply]

/-- Expand the diagonal adjugate through the explicit three-by-three formula
before default simp can replace it by erased-Finset cofactor products. -/
private theorem diagonalInput_adjugate (a b c : ℂ) :
    (diagonalInput a b c).adjugate = Matrix.diagonal ![b*c,a*c,a*b] := by
  rw [Matrix.adjugate_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalInput, Matrix.diagonal_apply]
  all_goals ring

/- This macro is a fixed nine-entry source proof.
D is diagonal but H is ANY complex3x3 matrix; no conjugate of H or K is present.
Each certificate has nine complex ring goals. No Complex.ext is needed because
the identity is an unstarred polynomial over the commutative ring Complex. -/
local macro "solve_complex_unit" : tactic =>
  `(tactic|
    (ext a b
     fin_cases a <;> fin_cases b
     all_goals simp only [residual, complexCommutator, adjugateCommutator,
       symmProduct, SectorContraction.tracePolar]
     all_goals simp only [diagonalInput_adjugate]
     all_goals simp only [Matrix.adjugate_fin_three]
     all_goals simp [diagonalInput, matrixUnit, Matrix.diagonal_apply,
       Matrix.single_apply, Matrix.mul_apply, Matrix.vecMul_apply_eq_sum,
       Matrix.trace, Matrix.diag, Matrix.one_apply, Fin.sum_univ_three,
       smul_eq_mul]
     all_goals ring))

theorem unit00 (a b c : ℂ) (H : Mat) :
    residual (diagonalInput a b c) H (matrixUnit 0 0) = 0 := by solve_complex_unit

theorem unit01 (a b c : ℂ) (H : Mat) :
    residual (diagonalInput a b c) H (matrixUnit 0 1) = 0 := by solve_complex_unit

theorem unit02 (a b c : ℂ) (H : Mat) :
    residual (diagonalInput a b c) H (matrixUnit 0 2) = 0 := by solve_complex_unit

theorem unit10 (a b c : ℂ) (H : Mat) :
    residual (diagonalInput a b c) H (matrixUnit 1 0) = 0 := by solve_complex_unit

theorem unit11 (a b c : ℂ) (H : Mat) :
    residual (diagonalInput a b c) H (matrixUnit 1 1) = 0 := by solve_complex_unit

theorem unit12 (a b c : ℂ) (H : Mat) :
    residual (diagonalInput a b c) H (matrixUnit 1 2) = 0 := by solve_complex_unit

theorem unit20 (a b c : ℂ) (H : Mat) :
    residual (diagonalInput a b c) H (matrixUnit 2 0) = 0 := by solve_complex_unit

theorem unit21 (a b c : ℂ) (H : Mat) :
    residual (diagonalInput a b c) H (matrixUnit 2 1) = 0 := by solve_complex_unit

theorem unit22 (a b c : ℂ) (H : Mat) :
    residual (diagonalInput a b c) H (matrixUnit 2 2) = 0 := by solve_complex_unit

theorem residual_unit_zero (a b c : ℂ) (H : Mat) (i j : Fin 3) :
    residual (diagonalInput a b c) H (matrixUnit i j) = 0 := by
  fin_cases i <;> fin_cases j
  · exact unit00 a b c H
  · exact unit01 a b c H
  · exact unit02 a b c H
  · exact unit10 a b c H
  · exact unit11 a b c H
  · exact unit12 a b c H
  · exact unit20 a b c H
  · exact unit21 a b c H
  · exact unit22 a b c H

/-- Unconditional assembly uses actual complex linearity, exact reconstruction
and EVERY proved unit certificate. No missing residual premise is assumed. -/
theorem residual_zero (a b c : ℂ) (H K : Mat) :
    residual (diagonalInput a b c) H K = 0 := by
  change residualComplexLinear (diagonalInput a b c) H K = 0
  rw [reconstruct K, map_sum]
  simp only [map_sum, map_smul]
  have hz (i j : Fin 3) :
      residualComplexLinear (diagonalInput a b c) H (matrixUnit i j) = 0 := by
    rw [residualComplexLinear_apply]
    exact residual_unit_zero a b c H i j
  simp only [hz, smul_zero, Finset.sum_const_zero]

theorem mixed_identity (a b c : ℂ) (H K : Mat) :
    SectorContraction.tracePolar
      (complexCommutator (diagonalInput a b c) H K)
      (symmProduct (diagonalInput a b c) H) =
      adjugateCommutator (diagonalInput a b c) H *
        symmProduct (diagonalInput a b c) H * K -
      K * symmProduct (diagonalInput a b c) H *
        adjugateCommutator (diagonalInput a b c) H := by
  have hz := residual_zero a b c H K
  calc
    _ = residual (diagonalInput a b c) H K +
        adjugateCommutator (diagonalInput a b c) H *
          symmProduct (diagonalInput a b c) H * K -
        K * symmProduct (diagonalInput a b c) H *
          adjugateCommutator (diagonalInput a b c) H := by
      unfold residual
      module
    _ = _ := by rw [hz, zero_add]

/-- Actual native diagonal binding; no sector convention is relabelled. -/
theorem diagonalInput_native (a b c : ℝ) :
    diagonalInput (a:ℂ) (b:ℂ) (c:ℂ) =
      sectorComplexMatrix (diagonalAlbert a b c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [diagonalInput, Matrix.diagonal_apply, sectorComplexMatrix,
      complexHermitianMatrix, complexCoordinatesLinear, diagonalAlbert,
      complexPart]

/-- Native Hermitian matrices are literal specializations of the stronger
unstarred identity. Their Hermiticity is supplied by sectorComplexMatrix,
not used to remove any coefficient check. This asserts no actual Phi slice. -/
theorem native_mixed_identity (a b c : ℝ) (y z : Albert) :
    SectorContraction.tracePolar
      (complexCommutator (sectorComplexMatrix (diagonalAlbert a b c))
        (sectorComplexMatrix y) (sectorComplexMatrix z))
      (symmProduct (sectorComplexMatrix (diagonalAlbert a b c)) (sectorComplexMatrix y)) =
      adjugateCommutator (sectorComplexMatrix (diagonalAlbert a b c))
          (sectorComplexMatrix y) *
        symmProduct (sectorComplexMatrix (diagonalAlbert a b c)) (sectorComplexMatrix y) *
        sectorComplexMatrix z -
      sectorComplexMatrix z *
        symmProduct (sectorComplexMatrix (diagonalAlbert a b c)) (sectorComplexMatrix y) *
        adjugateCommutator (sectorComplexMatrix (diagonalAlbert a b c))
          (sectorComplexMatrix y) := by
  simpa only [diagonalInput_native] using
    mixed_identity (a:ℂ) (b:ℂ) (c:ℂ) (sectorComplexMatrix y) (sectorComplexMatrix z)

end MixedComplexUnits
end
end Glennie
