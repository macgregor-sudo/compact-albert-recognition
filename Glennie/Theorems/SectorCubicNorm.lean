module

public import Glennie.Sector
public import Glennie.Theorems.CubicNorm

/- The hidden-column gauge has positive cubic determinant sign.
This polynomial identity includes singular matrices and has no inverse premise. -/

public section
namespace Glennie
noncomputable section

set_option maxHeartbeats 2000000 in
theorem hiddenAlbert_cubicNorm (M : Matrix (Fin 3) (Fin 3) ℂ) :
    newtonCubicNorm (hiddenAlbert M) = 2 * M.det.re := by
  rw [newtonCubicNorm_coordinates]
  simp [hiddenAlbert, hiddenOct, octMul, octConj, octRe,
    Matrix.det_fin_three, Complex.mul_re, Complex.mul_im,
    Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul]
  ring

end
end Glennie
