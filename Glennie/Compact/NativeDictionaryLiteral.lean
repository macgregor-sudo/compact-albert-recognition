/- Literal metric, cubic, basis table and flat coordinates for the dictionary.
  * The metric in summation and matrix forms.
  * The cubic in complex form det H - tr(H M^dagger M) + det M + conj(det M),
    whose imaginary part vanishes identically.
  * The 27-entry basis table, derived index by index as extDecode of coordinate
    unit vectors.
  * Flat base vectors x, y(theta), z(theta) as decodes of explicit coordinate
    vectors, with s standing for theta^-1 (no inverse is cast to C).
No flatness, frame admission, Phi value or rank statement is made here. -/
module

public import Glennie.Compact.NativeDictionaryProduct

@[expose] public section

namespace Glennie.Compact.NativeDictionary

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-! ## Metric and cubic in the literal forms -/

theorem extMetric_eq_sum (a b : Fin 26 → ℝ) :
    extMetric a b = ∑ i, extG i * a i * b i := by
  simp [extMetric, extG, Fin.sum_univ_succ] <;> ring

/-- The assertion (tr H^2 + 2 tr M^dagger M) / 3 = g, as 3 g(a, a). -/
theorem extMetric_matrix (a : Fin 26 → ℝ) :
    3 * extMetric a a = ((extH a * extH a).trace).re +
      2 * (((extM a).conjTranspose * extM a).trace).re := by
  have h := inner_sector_model (extDecode0 a) (extDecode0 a)
  rw [sectorComplexMatrix_extDecode0, hiddenMatrix_extDecode0, inner_extDecode0] at h
  exact h

/-- The complex expression for C is real and equals `extCubic`. -/
theorem extCubic_literal (a : Fin 26 → ℝ) :
    ((extCubic a : ℝ) : ℂ) =
      (extH a).det - (extH a * (extM a).conjTranspose * extM a).trace +
        (extM a).det + star (extM a).det := by
  apply Complex.ext
  · simp [extCubic] <;> ring
  · -- Same two stages as `extCubic_eq_newtonCubicNorm`: expand while folded, then
    -- evaluate entries, so no `vecMul` term can appear.
    simp only [Matrix.det_fin_three, Matrix.trace_fin_three, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_three]
    simp [extH, extM, Complex.mul_re, Complex.mul_im] <;> ring

/-! ## The basis table, re-derived -/

/-- Full coordinate unit vector. -/
def extUnit (n : Fin 27) : Fin 27 → ℝ := fun i => if i = n then 1 else 0

/-- The row-major
hidden matrix unit w E_rc in the column gauge. -/
def archivalHiddenBasis (r c : Fin 3) (w : ℂ) : Albert :=
  hiddenAlbert (fun i j => if i = r ∧ j = c then w else 0)

/-- Full index 0 (unit). -/
theorem extDecode_extUnit_0 : extDecode (extUnit 0) = 1 := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 1 (t). -/
theorem extDecode_extUnit_1 : extDecode (extUnit 1) = diagonalAlbert 1 (-1) 0 := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 2 (s). -/
theorem extDecode_extUnit_2 : extDecode (extUnit 2) = diagonalAlbert 1 1 (-2) := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 3 (a01). -/
theorem extDecode_extUnit_3 : extDecode (extUnit 3) = complexAlbert 0 0 0 1 0 0 := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 4 (b01). -/
theorem extDecode_extUnit_4 : extDecode (extUnit 4) = complexAlbert 0 0 0 Complex.I 0 0 := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 5 (a02). -/
theorem extDecode_extUnit_5 : extDecode (extUnit 5) = complexAlbert 0 0 0 0 1 0 := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 6 (b02). -/
theorem extDecode_extUnit_6 : extDecode (extUnit 6) = complexAlbert 0 0 0 0 Complex.I 0 := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 7 (a12). -/
theorem extDecode_extUnit_7 : extDecode (extUnit 7) = complexAlbert 0 0 0 0 0 1 := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 8 (b12). -/
theorem extDecode_extUnit_8 : extDecode (extUnit 8) = complexAlbert 0 0 0 0 0 Complex.I := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 9 (u00). -/
theorem extDecode_extUnit_9 : extDecode (extUnit 9) = archivalHiddenBasis 0 0 1 := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 10 (v00). -/
theorem extDecode_extUnit_10 : extDecode (extUnit 10) = archivalHiddenBasis 0 0 Complex.I := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 11 (u01). -/
theorem extDecode_extUnit_11 : extDecode (extUnit 11) = archivalHiddenBasis 0 1 1 := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 12 (v01). -/
theorem extDecode_extUnit_12 : extDecode (extUnit 12) = archivalHiddenBasis 0 1 Complex.I := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 13 (u02). -/
theorem extDecode_extUnit_13 : extDecode (extUnit 13) = archivalHiddenBasis 0 2 1 := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 14 (v02). -/
theorem extDecode_extUnit_14 : extDecode (extUnit 14) = archivalHiddenBasis 0 2 Complex.I := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 15 (u10). -/
theorem extDecode_extUnit_15 : extDecode (extUnit 15) = archivalHiddenBasis 1 0 1 := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 16 (v10). -/
theorem extDecode_extUnit_16 : extDecode (extUnit 16) = archivalHiddenBasis 1 0 Complex.I := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 17 (u11). -/
theorem extDecode_extUnit_17 : extDecode (extUnit 17) = archivalHiddenBasis 1 1 1 := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 18 (v11). -/
theorem extDecode_extUnit_18 : extDecode (extUnit 18) = archivalHiddenBasis 1 1 Complex.I := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 19 (u12). -/
theorem extDecode_extUnit_19 : extDecode (extUnit 19) = archivalHiddenBasis 1 2 1 := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 20 (v12). -/
theorem extDecode_extUnit_20 : extDecode (extUnit 20) = archivalHiddenBasis 1 2 Complex.I := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 21 (u20). -/
theorem extDecode_extUnit_21 : extDecode (extUnit 21) = archivalHiddenBasis 2 0 1 := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 22 (v20). -/
theorem extDecode_extUnit_22 : extDecode (extUnit 22) = archivalHiddenBasis 2 0 Complex.I := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 23 (u21). -/
theorem extDecode_extUnit_23 : extDecode (extUnit 23) = archivalHiddenBasis 2 1 1 := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 24 (v21). -/
theorem extDecode_extUnit_24 : extDecode (extUnit 24) = archivalHiddenBasis 2 1 Complex.I := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 25 (u22). -/
theorem extDecode_extUnit_25 : extDecode (extUnit 25) = archivalHiddenBasis 2 2 1 := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 26 (v22). -/
theorem extDecode_extUnit_26 : extDecode (extUnit 26) = archivalHiddenBasis 2 2 Complex.I := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-! ## The flat base, as explicit coordinates (s stands for theta^-1) -/

def flatXCoords : Fin 27 → ℝ := (1 / 2 : ℝ) • extUnit 1 + (1 / 2 : ℝ) • extUnit 2

def flatYCoords (s : ℝ) : Fin 27 → ℝ := s • extUnit 3 - s • extUnit 6 + s • extUnit 7

def flatZCoords (s : ℝ) : Fin 27 → ℝ := s • extUnit 10 - s • extUnit 17 - s • extUnit 25

/-- The flat x is (1/2) times basis vector 1 plus (1/2) times basis vector 2,
where basis vector m is `extDecode (extUnit m)`. -/
theorem archivalBaseX_coords :
    (1 / 2 : ℝ) • diagonalAlbert 1 (-1) 0 + (1 / 2 : ℝ) • diagonalAlbert 1 1 (-2) =
      extDecode flatXCoords := by
  rw [← extDecode_extUnit_1, ← extDecode_extUnit_2, flatXCoords, extDecode_add,
    extDecode_smul, extDecode_smul]

theorem extDecode_flatX : extDecode flatXCoords = diagonalAlbert 1 0 (-1) := by
  ext <;> simp [extDecode, flatXCoords, extUnit, diagonalAlbert] <;> ring

/-- The flat y coordinates, with s = theta^-1. -/
theorem extDecode_flatY (s : ℝ) :
    extDecode (flatYCoords s) =
      complexAlbert 0 0 0 (s : ℂ) (-Complex.I * (s : ℂ)) (s : ℂ) := by
  ext <;> simp [extDecode, flatYCoords, extUnit, complexAlbert, complexOct] <;> ring

/-- The flat z coordinates, with s = theta^-1. -/
theorem extDecode_flatZ (s : ℝ) :
    extDecode (flatZCoords s) =
      s • hiddenAlbert !![Complex.I, 0, 0; 0, -1, 0; 0, 0, -1] := by
  ext <;> simp [extDecode, flatZCoords, extUnit, hiddenAlbert, hiddenOct] <;> ring

end
end Glennie.Compact.NativeDictionary
