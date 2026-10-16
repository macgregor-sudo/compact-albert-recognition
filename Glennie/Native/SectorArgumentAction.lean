/- Complementary actual native U action from the SectorModel product.
No cubic adjoint, norm reconstruction, invertibility, book-U rescaling, or scalar
Phi identity is assumed. -/
module
public import Glennie.SectorModel

@[expose] public section
namespace Glennie
noncomputable section

namespace SectorArgumentAction

set_option maxHeartbeats 2000000

abbrev Mat := Matrix (Fin 3) (Fin 3) ℂ

/-- Ordinary (unstarred) polarized matrix adjugate in trace-polynomial form.
This differs from sectorPolarAdjugate, which includes a conjugate transpose. -/
def gamma (G B : Mat) : Mat :=
  G*B+B*G-B.trace • G-G.trace • B+
    (G.trace*B.trace-(G*B).trace) • (1:Mat)

/-- Nine quadratic complex entry identities, for arbitrary complex matrices. -/
theorem gamma_eq_polarAdjugate (G B : Mat) :
    gamma G B = (G+B).adjugate-G.adjugate-B.adjugate := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma, Matrix.adjugate_fin_three, Matrix.mul_apply, Matrix.trace,
      Matrix.diag, Matrix.one_apply, Fin.sum_univ_three, smul_eq_mul] <;> ring

/-- Use bilinearity before substituting the degree-two inner Jordan hidden
block. This removes artificial quartic terms introduced by expanding cofactors
of M+N and then cancelling the N-only cofactors. -/
theorem polarAdjugate_eq_gamma_conjTranspose (M N : Mat) :
    sectorPolarAdjugate M N = (gamma M N).conjTranspose := by
  rw [gamma_eq_polarAdjugate]
  simp only [sectorPolarAdjugate, sectorAdjointAdjugate,
    Matrix.conjTranspose_sub]

@[simp] theorem polarAdjugate_zero_right (M : Mat) :
    sectorPolarAdjugate M 0 = 0 := by
  simp [sectorPolarAdjugate, sectorAdjointAdjugate, Matrix.adjugate_zero]

theorem productComplex_complex_right (K M B : Mat) :
    sectorProductComplex K M B 0 = (1/2:ℂ) • (K*B+B*K) := by
  simp [sectorProductComplex]

theorem productHidden_complex_right (K M B : Mat) :
    sectorProductHidden K M B 0 =
      (1/2:ℂ) • (M*(B.trace • (1:Mat)-B)) := by
  simp [sectorProductHidden, polarAdjugate_zero_right]

/-- For arbitrary native z=(K,M) and pure-complex b=(B,0), the complex block
of the actual native U_z b is K*B*K+gamma(M.conjTranspose*M,B).
The proof expands only the matrix product twice, then checks cubic
entries in its actual Hermitian coordinate carrier. It does not unfold native
jordan coordinates, octMul, or any global Phi. -/
theorem complex_U_argument (z b : Albert) (hb : hiddenMatrix b = 0) :
    sectorComplexMatrix (U z b) =
      sectorComplexMatrix z * sectorComplexMatrix b * sectorComplexMatrix z +
        gamma ((hiddenMatrix z).conjTranspose * hiddenMatrix z)
          (sectorComplexMatrix b) := by
  change sectorComplexLinear ((2:ℝ) • jordan z (jordan z b) -
    jordan (jordan z z) b) = _
  rw [map_sub, map_smul]
  change (2:ℝ) • sectorComplexMatrix (jordan z (jordan z b)) -
    sectorComplexMatrix (jordan (jordan z z) b) = _
  simp only [sectorComplexMatrix_jordan, hiddenMatrix_jordan, hb,
    productComplex_complex_right, productHidden_complex_right]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext
  all_goals simp [sectorProductComplex, sectorProductHidden,
    polarAdjugate_eq_gamma_conjTranspose, sectorAdjointAdjugate, gamma, sectorComplexMatrix, complexHermitianMatrix,
    complexCoordinatesLinear, complexPart, Matrix.adjugate_fin_three,
    Matrix.mul_apply, Matrix.vecMul_apply_eq_sum, Matrix.conjTranspose_apply, Matrix.trace, Matrix.diag,
    Matrix.one_apply, Fin.sum_univ_three, smul_eq_mul,
    Complex.mul_re, Complex.mul_im]
  all_goals ring

/-- The hidden action retains K*B in that order and has coefficient one on
adj(M).conjTranspose*B. Singular M and every native complex component K are
included. The native U is halved-Jordan U throughout. -/
theorem hidden_U_argument (z b : Albert) (hb : hiddenMatrix b = 0) :
    hiddenMatrix (U z b) =
      hiddenMatrix z *
        ((sectorComplexMatrix z * sectorComplexMatrix b).trace • (1:Mat) -
          sectorComplexMatrix z * sectorComplexMatrix b) +
      sectorAdjointAdjugate (hiddenMatrix z) * sectorComplexMatrix b := by
  change sectorHiddenLinear ((2:ℝ) • jordan z (jordan z b) -
    jordan (jordan z z) b) = _
  rw [map_sub, map_smul]
  change (2:ℝ) • hiddenMatrix (jordan z (jordan z b)) -
    hiddenMatrix (jordan (jordan z z) b) = _
  simp only [hiddenMatrix_jordan, sectorComplexMatrix_jordan, hb,
    productHidden_complex_right, productComplex_complex_right]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext
  all_goals simp [sectorProductComplex, sectorProductHidden,
    polarAdjugate_eq_gamma_conjTranspose, sectorAdjointAdjugate, gamma,
    sectorComplexMatrix, complexHermitianMatrix,
    complexCoordinatesLinear, complexPart, Matrix.adjugate_fin_three,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.trace, Matrix.diag,
    Matrix.one_apply, Fin.sum_univ_three, smul_eq_mul,
    Complex.mul_re, Complex.mul_im]
  all_goals ring

end SectorArgumentAction
end
end Glennie
