/- Unrestricted native factor.
All intermediate conclusions are proved from named action, matrix and trace bodies;
no missing factor/cancellation field or hypothesis. -/
module
public import Glennie.Native.SectorAction
public import Glennie.Native.SectorArgumentAction
public import Glennie.Theorems.SectorContraction
public import Glennie.Native.MixedComplexUnits
public import Glennie.SectorFactorWeight
public import Glennie.Native.SectorAssemblyBridges
public import Glennie.Native.SectorMixedTrace

@[expose] public section
namespace Glennie
noncomputable section

set_option maxHeartbeats 2000000

theorem phi_diagonal_complex_factor (a b c d e f : ℝ) (u v w : ℂ) (z : Albert) :
    phi (diagonalAlbert a b c) (complexAlbert d e f u v w) z =
      (2*(a-b)*(b-c)*(c-a)*(u*w*star v).im) * (hiddenMatrix z).det.im := by
  let x := diagonalAlbert a b c
  let y := complexAlbert d e f u v w
  let D := sectorComplexMatrix x
  let H := sectorComplexMatrix y
  let K := sectorComplexMatrix z
  let M := hiddenMatrix z
  let B := sectorComplexMatrix (jordan x y)
  let G := M.conjTranspose*M
  let S := H.adjugate*D.adjugate-D.adjugate*H.adjugate
  let Q := D*H*K*H*D-H*D*K*D*H
  let t := (a-b)*(b-c)*(c-a)*(u*w*star v).im
  have hx : hiddenMatrix x = 0 := SectorAssemblyBridges.hidden_diagonal a b c
  have hy : hiddenMatrix y = 0 := SectorAssemblyBridges.hidden_complex d e f u v w
  have hb : hiddenMatrix (jordan x y) = 0 :=
    SectorAssemblyBridges.jordan_hidden_zero x y hx hy
  have hB : B = (1/2:ℂ) • (D*H+H*D) :=
    SectorAssemblyBridges.jordan_complex_matrix x y hx
  have hS : S.conjTranspose = -S :=
    SectorAssemblyBridges.native_adjugate_commutator_antiHermitian x y
  have hK : K.IsHermitian := sectorComplexMatrix_isHermitian z
  have hBH : B.IsHermitian := sectorComplexMatrix_isHermitian (jordan x y)
  have hCommC : sectorComplexMatrix (U x (U y z)-U y (U x z)) = Q :=
    SectorAction.complex_commutator x y z hx hy
  have hCommM : hiddenMatrix (U x (U y z)-U y (U x z)) = M*S :=
    SectorAction.hidden_commutator x y z hx hy
  have hUC : sectorComplexMatrix (U z (jordan x y)) =
      K*B*K+SectorContraction.tracePolar G B := by
    rw [SectorArgumentAction.complex_U_argument z (jordan x y) hb]
    change K*B*K+SectorArgumentAction.gamma G B = _
    rw [SectorAssemblyBridges.gamma_eq_tracePolar]
  have hUH : hiddenMatrix (U z (jordan x y)) =
      M*((K*B).trace • (1:Matrix (Fin 3) (Fin 3) ℂ)-K*B)+
        sectorAdjointAdjugate M*B :=
    SectorArgumentAction.hidden_U_argument z (jordan x y) hb
  have hMetric : phi x y z =
      (Q*(K*B*K)).trace.re +
      (Q*SectorContraction.tracePolar G B).trace.re +
      2*((M*S).conjTranspose*
        (M*((K*B).trace • (1:Matrix (Fin 3) (Fin 3) ℂ)-K*B))).trace.re +
      2*((M*S).conjTranspose*(sectorAdjointAdjugate M*B)).trace.re := by
    rw [phi, inner_sector_model, hCommC, hCommM, hUC, hUH]
    simp only [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
    ring
  have hPure : (Q*(K*B*K)).trace.re = 0 := by
    rw [hB]
    simpa only [Complex.zero_re] using
      congrArg Complex.re (SectorAssemblyBridges.pure_complex_trace D H K)
  have hMixedMatrix : SectorContraction.tracePolar Q B = S*B*K-K*B*S := by
    rw [hB]
    simpa only [MixedComplexUnits.complexCommutator, MixedComplexUnits.symmProduct,
      MixedComplexUnits.adjugateCommutator] using
        MixedComplexUnits.native_mixed_identity a b c y z
  have hMixed : (Q*SectorContraction.tracePolar G B).trace.re +
      2*((M*S).conjTranspose*
        (M*((K*B).trace • (1:Matrix (Fin 3) (Fin 3) ℂ)-K*B))).trace.re = 0 := by
    rw [SectorContraction.trace_polar_transfer Q G B, hMixedMatrix]
    exact SectorMixedTrace.mixed_trace_cancel M S K B hS hK hBH
  have hD : D = SectorFactorWeight.diagonalMatrix a b c :=
    SectorAssemblyBridges.diagonal_matrix_binding a b c
  have hH : H = SectorFactorWeight.hermitianMatrix d e f u v w :=
    SectorAssemblyBridges.complex_matrix_binding d e f u v w
  have hSB : (S*B).trace = (⟨0,-t⟩:ℂ) := by
    rw [hB]
    change (SectorFactorWeight.adjugateCommutator D H *
      SectorFactorWeight.argumentMatrix D H).trace = (⟨0,-t⟩:ℂ)
    rw [hD, hH]
    simpa only [t, neg_mul] using
      SectorFactorWeight.adjugate_argument_trace a b c d e f u v w
  have hCubic :
      2*((M*S).conjTranspose*(sectorAdjointAdjugate M*B)).trace.re =
        2*t*M.det.im := by
    calc
      _ = -2*(star M.det*(S*B).trace).re :=
        SectorContraction.hidden_cubic_real M S B hS
      _ = 2*(-(star M.det)*(⟨0,-t⟩:ℂ)).re := by
        rw [hSB]
        simp only [neg_mul, Complex.neg_re]
        ring
      _ = _ := SectorFactorWeight.determinant_pairing_scalar M.det t
  change phi x y z = (2*(a-b)*(b-c)*(c-a)*(u*w*star v).im)*M.det.im
  calc
    _ = 2*t*M.det.im := by
      rw [hMetric, hPure]
      linarith [hMixed, hCubic]
    _ = _ := by
      dsimp only [t]
      ring

end
end Glennie
