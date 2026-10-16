/- Structured native sector action using the raw trace and hidden column gauge.
No cubic-norm reconstruction, book U identity, or desired scalar factor is imported
or assumed. -/
module
public import Glennie.SectorModel

@[expose] public section
namespace Glennie
noncomputable section

namespace SectorAction

set_option maxHeartbeats 2000000

abbrev Mat := Matrix (Fin 3) (Fin 3) ℂ

/-- The Newton expression in the hidden right action is the literal adjugate.
Nine quadratic complex entry goals; no native octonion expansion. -/
theorem newtonAdjugate (H : Mat) :
    (1/2:ℂ) • ((H.trace • (1:Mat)-H)*(H.trace • (1:Mat)-H) -
      ((H*H).trace • (1:Mat)-H*H)) = H.adjugate := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_three, Matrix.mul_apply, Matrix.trace,
      Matrix.diag, Matrix.one_apply, Fin.sum_univ_three, smul_eq_mul] <;> ring

@[simp] theorem polarAdjugate_zero_left (N : Mat) :
    sectorPolarAdjugate 0 N = 0 := by
  simp [sectorPolarAdjugate, sectorAdjointAdjugate, Matrix.adjugate_zero]

/-- Complex-left Jordan multiplication has no contribution from the hidden
right argument to its complex component. -/
theorem productComplex_complex_left (H K M : Mat) :
    sectorProductComplex H 0 K M = (1/2:ℂ) • (H*K+K*H) := by
  simp [sectorProductComplex]

/-- The hidden block is a right matrix action, including the trace term. -/
theorem productHidden_complex_left (H K M : Mat) :
    sectorProductHidden H 0 K M =
      (1/2:ℂ) • (M*(H.trace • (1:Mat)-H)) := by
  simp [sectorProductHidden, polarAdjugate_zero_left]

/-- Actual native U on the complex block, derived only through the product map. Nine cubic complex entry goals, split into real and imaginary. -/
theorem complex_U (y z : Albert) (hy : hiddenMatrix y = 0) :
    sectorComplexMatrix (U y z) =
      sectorComplexMatrix y * sectorComplexMatrix z * sectorComplexMatrix y := by
  have hs : hiddenMatrix (jordan y y) = 0 := by
    rw [hiddenMatrix_jordan, hy, productHidden_complex_left]
    simp
  change sectorComplexLinear ((2:ℝ) • jordan y (jordan y z) -
    jordan (jordan y y) z) = _
  rw [map_sub, map_smul]
  change (2:ℝ) • sectorComplexMatrix (jordan y (jordan y z)) -
    sectorComplexMatrix (jordan (jordan y y) z) = _
  simp only [hs, sectorComplexMatrix_jordan, hy, productComplex_complex_left]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_three, smul_eq_mul,
    Complex.mul_re, Complex.mul_im]
  all_goals ring

/-- Actual native U on the hidden block. The quadratic Newton multiplier is
adj(H), and the output is M*adj(H), without conjugating this adjugate. -/
theorem hidden_U (y z : Albert) (hy : hiddenMatrix y = 0) :
    hiddenMatrix (U y z) = hiddenMatrix z * (sectorComplexMatrix y).adjugate := by
  have hs : hiddenMatrix (jordan y y) = 0 := by
    rw [hiddenMatrix_jordan, hy, productHidden_complex_left]
    simp
  change sectorHiddenLinear ((2:ℝ) • jordan y (jordan y z) -
    jordan (jordan y y) z) = _
  rw [map_sub, map_smul]
  change (2:ℝ) • hiddenMatrix (jordan y (jordan y z)) -
    hiddenMatrix (jordan (jordan y y) z) = _
  simp only [hs, hiddenMatrix_jordan, sectorComplexMatrix_jordan, hy,
    productHidden_complex_left, productComplex_complex_left]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext
  all_goals simp [Matrix.adjugate_fin_three, Matrix.mul_apply, Matrix.trace,
    Matrix.diag, Matrix.one_apply, Fin.sum_univ_three, smul_eq_mul,
    Complex.mul_re, Complex.mul_im]
  all_goals ring

/-- Both bases have vanishing hidden component; no restriction on z. -/
theorem hidden_commutator (x y z : Albert)
    (hx : hiddenMatrix x = 0) (hy : hiddenMatrix y = 0) :
    hiddenMatrix (U x (U y z) - U y (U x z)) =
      hiddenMatrix z * ((sectorComplexMatrix y).adjugate *
        (sectorComplexMatrix x).adjugate - (sectorComplexMatrix x).adjugate *
        (sectorComplexMatrix y).adjugate) := by
  change sectorHiddenLinear (U x (U y z) - U y (U x z)) = _
  rw [map_sub]
  change hiddenMatrix (U x (U y z)) - hiddenMatrix (U y (U x z)) = _
  rw [hidden_U x (U y z) hx, hidden_U y z hy,
    hidden_U y (U x z) hy, hidden_U x z hx]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_sub]

/-- The complementary complex commutator retains K explicitly. -/
theorem complex_commutator (x y z : Albert)
    (hx : hiddenMatrix x = 0) (hy : hiddenMatrix y = 0) :
    sectorComplexMatrix (U x (U y z) - U y (U x z)) =
      sectorComplexMatrix x * sectorComplexMatrix y * sectorComplexMatrix z *
        sectorComplexMatrix y * sectorComplexMatrix x -
      sectorComplexMatrix y * sectorComplexMatrix x * sectorComplexMatrix z *
        sectorComplexMatrix x * sectorComplexMatrix y := by
  change sectorComplexLinear (U x (U y z) - U y (U x z)) = _
  rw [map_sub]
  change sectorComplexMatrix (U x (U y z)) -
    sectorComplexMatrix (U y (U x z)) = _
  rw [complex_U x (U y z) hx, complex_U y z hy,
    complex_U y (U x z) hy, complex_U x z hx]
  simp only [Matrix.mul_assoc]

end SectorAction
end
end Glennie
