/- These leaves involve only the diagonal/complex coefficient, not the full
27-coordinate degree-nine Phi contraction. All operations are literal complex
matrices in the native sector gauge; no inverse/genericity premise.
-/
module
public import Glennie.SectorModel

@[expose] public section
namespace Glennie.SectorFactorWeight
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℂ

def diagonalMatrix (a b c : ℝ) : Mat3 :=
  complexHermitianMatrix ((a,b,c),(0,0,0))

def hermitianMatrix (d e f : ℝ) (u v w : ℂ) : Mat3 :=
  complexHermitianMatrix ((d,e,f),(u,v,w))

def argumentMatrix (D H : Mat3) : Mat3 := (1/2:ℂ) • (D*H+H*D)

def adjugateCommutator (D H : Mat3) : Mat3 := H.adjugate*D.adjugate-D.adjugate*H.adjugate

/-- A sparse three-entry determinant coefficient, including repeated spectra. -/
theorem diagonal_commutator_det (a b c d e f : ℝ) (u v w : ℂ) :
    ((diagonalMatrix a b c * hermitianMatrix d e f u v w -
      hermitianMatrix d e f u v w * diagonalMatrix a b c).det) =
      ⟨0,2*(a-b)*(b-c)*(c-a)*(u*w*star v).im⟩ := by
  apply Complex.ext
  all_goals simp [diagonalMatrix, hermitianMatrix, complexHermitianMatrix,
    Matrix.det_fin_three, Matrix.mul_apply, Fin.sum_univ_three,
    Complex.mul_re, Complex.mul_im]
  all_goals ring

/-- Small coefficient leaf for the hidden determinant contraction.
The separate structural alternative is trace(S*B)=-det(DH-HD)/2; the direct
degree-six producer below does not assume that trace identity. -/
theorem adjugate_argument_trace (a b c d e f : ℝ) (u v w : ℂ) :
    (adjugateCommutator (diagonalMatrix a b c) (hermitianMatrix d e f u v w) *
      argumentMatrix (diagonalMatrix a b c) (hermitianMatrix d e f u v w)).trace =
      ⟨0,-(a-b)*(b-c)*(c-a)*(u*w*star v).im⟩ := by
  apply Complex.ext
  all_goals simp [adjugateCommutator, argumentMatrix, diagonalMatrix,
    hermitianMatrix, complexHermitianMatrix, Matrix.adjugate_fin_three,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three,
    smul_eq_mul, Complex.mul_re, Complex.mul_im]
  all_goals ring

/-- Raw hidden metric factor two is retained at the scalar finishing step. -/
theorem determinant_pairing_scalar (delta : ℂ) (t : ℝ) :
    2 * (-(star delta) * (⟨0,-t⟩ : ℂ)).re = 2*t*delta.im := by
  simp [Complex.mul_re]
  ring

end
end Glennie.SectorFactorWeight
