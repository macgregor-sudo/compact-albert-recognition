/- Small assembly bridges from actual native sector APIs.
No tracelessness, invertibility, scalar factor, covariance or endpoint premise. -/
module
public import Glennie.Native.SectorAction
public import Glennie.Native.SectorArgumentAction
public import Glennie.Theorems.SectorContraction

@[expose] public section
namespace Glennie.SectorAssemblyBridges
noncomputable section

abbrev Mat := Matrix (Fin 3) (Fin 3) ℂ

/-- Normalize the native octonion zero before transporting diagonal inputs.
Only this private proof unfolds complexOct; the two adapters use its equation. -/
private theorem complexOct_zero : complexOct (0:ℂ) = (0:Octonion) := by
  apply Prod.ext <;> apply Quaternion.ext <;> simp [complexOct]

/-- The two literal definitions differ only by commutative scalar order. -/
theorem gamma_eq_tracePolar (G B : Mat) :
    SectorArgumentAction.gamma G B = SectorContraction.tracePolar G B := by
  unfold SectorArgumentAction.gamma SectorContraction.tracePolar
  rw [mul_comm G.trace B.trace]

/-- The actual native product supplies the pure-complex argument for U_z. -/
theorem jordan_hidden_zero (x y : Albert)
    (hx : hiddenMatrix x = 0) (hy : hiddenMatrix y = 0) :
    hiddenMatrix (jordan x y) = 0 := by
  rw [hiddenMatrix_jordan, hx, SectorAction.productHidden_complex_left, hy]
  simp

theorem jordan_complex_matrix (x y : Albert) (hx : hiddenMatrix x = 0) :
    sectorComplexMatrix (jordan x y) =
      (1/2:ℂ) • (sectorComplexMatrix x * sectorComplexMatrix y +
        sectorComplexMatrix y * sectorComplexMatrix x) := by
  rw [sectorComplexMatrix_jordan, hx, SectorAction.productComplex_complex_left]

theorem hidden_diagonal (a b c : ℝ) :
    hiddenMatrix (diagonalAlbert a b c) = 0 := by
  simpa [complexAlbertLinear, complexAlbert, diagonalAlbert, complexOct_zero] using
    hiddenMatrix_complexAlbert ((a,b,c),(0,0,0))

theorem hidden_complex (d e f : ℝ) (u v w : ℂ) :
    hiddenMatrix (complexAlbert d e f u v w) = 0 := by
  change hiddenMatrix (complexAlbertLinear ((d,e,f),(u,v,w))) = 0
  exact hiddenMatrix_complexAlbert ((d,e,f),(u,v,w))

theorem complex_matrix_binding (d e f : ℝ) (u v w : ℂ) :
    sectorComplexMatrix (complexAlbert d e f u v w) =
      complexHermitianMatrix ((d,e,f),(u,v,w)) := by
  change complexHermitianMatrix
    (complexCoordinatesLinear (complexAlbertLinear ((d,e,f),(u,v,w)))) = _
  rw [complexCoordinates_albert]

theorem diagonal_matrix_binding (a b c : ℝ) :
    sectorComplexMatrix (diagonalAlbert a b c) =
      complexHermitianMatrix ((a,b,c),(0,0,0)) := by
  simpa [complexAlbert, diagonalAlbert, complexOct_zero] using
    complex_matrix_binding a b c 0 0 0

/-- Native Hermitian adjugates give the forward anti-Hermitian commutator. -/
theorem adjugate_commutator_antiHermitian (D H : Mat)
    (hD : D.IsHermitian) (hH : H.IsHermitian) :
    (H.adjugate * D.adjugate - D.adjugate * H.adjugate).conjTranspose =
      -(H.adjugate * D.adjugate - D.adjugate * H.adjugate) := by
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    hH.adjugate.eq, hD.adjugate.eq, neg_sub]

theorem native_adjugate_commutator_antiHermitian (x y : Albert) :
    ((sectorComplexMatrix y).adjugate * (sectorComplexMatrix x).adjugate -
      (sectorComplexMatrix x).adjugate * (sectorComplexMatrix y).adjugate).conjTranspose =
      -((sectorComplexMatrix y).adjugate * (sectorComplexMatrix x).adjugate -
        (sectorComplexMatrix x).adjugate * (sectorComplexMatrix y).adjugate) :=
  adjugate_commutator_antiHermitian _ _
    (sectorComplexMatrix_isHermitian x) (sectorComplexMatrix_isHermitian y)

/-- Cyclic trace, rather than product Hermiticity, proves this scalar is real. -/
theorem trace_mul_im_zero (K B : Mat)
    (hK : K.IsHermitian) (hB : B.IsHermitian) : (K*B).trace.im = 0 := by
  have hs : star (K*B).trace = (K*B).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hB.eq, hK.eq]
    exact Matrix.trace_mul_comm B K
  have hi : -(K*B).trace.im = (K*B).trace.im := by
    simpa using congrArg Complex.im hs
  linarith

theorem native_argument_trace_im_zero (z x y : Albert) :
    (sectorComplexMatrix z * sectorComplexMatrix (jordan x y)).trace.im = 0 :=
  trace_mul_im_zero _ _ (sectorComplexMatrix_isHermitian z)
    (sectorComplexMatrix_isHermitian (jordan x y))

theorem hidden_gram_isHermitian (M : Mat) :
    (M.conjTranspose*M).IsHermitian :=
  Matrix.isHermitian_conjTranspose_mul_self M

/-- Pure-complex cancellation for arbitrary matrices, retaining all traces.
The only nontrivial scalar cancellation is the existing cyclic-trace lemma. -/
theorem pure_complex_trace (D H K : Mat) :
    ((D*H*K*H*D-H*D*K*D*H) *
      (K*((1/2:ℂ) • (D*H+H*D))*K)).trace = 0 := by
  have hQ : (D*H*K*H*D-H*D*K*D*H)*K =
      (D*H*K)*(H*D*K)-(H*D*K)*(D*H*K) := by
    simp only [Matrix.sub_mul, Matrix.mul_assoc]
  have hB : ((1/2:ℂ) • (D*H+H*D))*K =
      (1/2:ℂ) • (D*H*K+H*D*K) := by
    simp only [Matrix.smul_mul, Matrix.add_mul]
  calc
    _ = (((D*H*K*H*D-H*D*K*D*H)*K) *
        (((1/2:ℂ) • (D*H+H*D))*K)).trace := by
      simp only [Matrix.mul_assoc]
    _ = (1/2:ℂ) *
        (((D*H*K)*(H*D*K)-(H*D*K)*(D*H*K)) *
          (D*H*K+H*D*K)).trace := by
      rw [hQ, hB]
      simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    _ = 0 := by
      rw [SectorContraction.trace_comm_mul_sum]
      simp

end
end Glennie.SectorAssemblyBridges
