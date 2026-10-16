/- Native metric adapters for the sharp compact sector estimate. -/
module
public import Glennie.Sector
public import Glennie.Hilbert
public import Glennie.Theorems.MatrixDetEstimate

@[expose] public section
namespace Glennie
noncomputable section

theorem diagonalAlbert_inner (a b c : ℝ) :
    inner (diagonalAlbert a b c) (diagonalAlbert a b c) = a^2+b^2+c^2 := by
  simp [inner_coordinates, diagonalAlbert, octDot_coordinates, octNormSq, Quaternion.normSq_def']
  ring

theorem complexAlbert_inner (a b c : ℝ) (u v w : ℂ) :
    inner (complexAlbert a b c u v w) (complexAlbert a b c u v w) =
      a^2+b^2+c^2+2*(Complex.normSq u+Complex.normSq v+Complex.normSq w) := by
  simp [inner_coordinates, complexAlbert, complexOct, octDot_coordinates,
    octNormSq, Quaternion.normSq_def', Complex.normSq_apply]
  ring

theorem sectorFrobeniusSq_eq (M : Matrix (Fin 3) (Fin 3) ℂ) :
    sectorFrobeniusSq M = MatrixDetEstimate.frobeniusSq M := by
  simp [sectorFrobeniusSq, MatrixDetEstimate.frobeniusSq,
    MatrixDetEstimate.columnGram, Matrix.trace, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_three,
    Complex.normSq_apply, Complex.mul_re]
  ring

theorem inner_hidden_decomposition (z : Albert) :
    inner z z = inner (complexProjection z) (complexProjection z)+
      2*sectorFrobeniusSq (hiddenMatrix z) := by
  calc
    _ = inner (complexProjection z+hiddenAlbert (hiddenMatrix z))
        (complexProjection z+hiddenAlbert (hiddenMatrix z)) := by
      rw [complex_hidden_decomposition]
    _ = _ := by
      rw [inner_add_left, inner_add_right, inner_add_right,
        complex_hidden_orthogonal, inner_comm (hiddenAlbert _) (complexProjection _),
        complex_hidden_orthogonal, hiddenAlbert_norm]
      simp [sectorFrobeniusSq]

theorem hidden_energy_le (z : Albert) :
    2*sectorFrobeniusSq (hiddenMatrix z) ≤ inner z z := by
  rw [inner_hidden_decomposition]
  linarith [inner_self_nonneg (complexProjection z)]

theorem complex_coefficient_bound (a b c : ℝ) (u v w : ℂ) :
    216*(u*w*star v).im^2 ≤ inner (complexAlbert a b c u v w)
      (complexAlbert a b c u v w)^3 := by
  have him : (u*w*star v).im^2 ≤ Complex.normSq u*Complex.normSq v*Complex.normSq w := by
    have h := sq_nonneg (u*w*star v).re
    have hid : Complex.normSq (u*w*star v) =
        Complex.normSq u*Complex.normSq v*Complex.normSq w := by
      simp only [map_mul, Complex.star_def, Complex.normSq_conj]
      ring
    rw [Complex.normSq_apply] at hid
    nlinarith
  have ham := ScalarEstimates.amgm_three (Complex.normSq u) (Complex.normSq v)
    (Complex.normSq w) (Complex.normSq_nonneg u) (Complex.normSq_nonneg v)
    (Complex.normSq_nonneg w)
  have hsum : 2*(Complex.normSq u+Complex.normSq v+Complex.normSq w) ≤
      inner (complexAlbert a b c u v w) (complexAlbert a b c u v w) := by
    rw [complexAlbert_inner]
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  have hs0 : 0 ≤ 2*(Complex.normSq u+Complex.normSq v+Complex.normSq w) := by
    exact mul_nonneg (by norm_num)
      (add_nonneg (add_nonneg (Complex.normSq_nonneg u) (Complex.normSq_nonneg v))
        (Complex.normSq_nonneg w))
  have hc := pow_le_pow_left₀ hs0 hsum 3
  nlinarith

theorem hidden_determinant_bound (z : Albert) :
    216*(hiddenMatrix z).det.im^2 ≤ (inner z z)^3 := by
  have hd := MatrixDetEstimate.normSq_det_le (hiddenMatrix z)
  have hi := MatrixDetEstimate.im_det_sq_le_normSq (hiddenMatrix z)
  rw [← sectorFrobeniusSq_eq] at hd
  have hs0 : 0 ≤ 2*sectorFrobeniusSq (hiddenMatrix z) := by
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      Complex.normSq_nonneg ((hiddenMatrix z) i j)
  have hc := pow_le_pow_left₀ hs0 (hidden_energy_le z) 3
  nlinarith

end
end Glennie
