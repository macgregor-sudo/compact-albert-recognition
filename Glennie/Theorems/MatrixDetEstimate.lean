module

public import Glennie.Theorems.ScalarEstimates
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Tactic.FinCases

/- Universal complex 3-by-3 determinant estimate, including singular matrices. -/

@[expose] public section

namespace Glennie.MatrixDetEstimate
noncomputable section

open Matrix

def columnGram (M : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  M.conjTranspose * M

def frobeniusSq (M : Matrix (Fin 3) (Fin 3) ℂ) : ℝ := (columnGram M).trace.re

theorem determinant_gram_real (M : Matrix (Fin 3) (Fin 3) ℂ) :
    (columnGram M).det.re = Complex.normSq M.det := by
  rw [columnGram, Matrix.det_mul, Matrix.det_conjTranspose]
  simp [Complex.mul_re, Complex.normSq_apply]

theorem normSq_det_le (M : Matrix (Fin 3) (Fin 3) ℂ) :
    27 * Complex.normSq M.det ≤ frobeniusSq M ^ 3 := by
  let hG := Matrix.isHermitian_conjTranspose_mul_self M
  have hdet : Complex.normSq M.det =
      hG.eigenvalues 0 * hG.eigenvalues 1 * hG.eigenvalues 2 := by
    rw [← determinant_gram_real M]
    change ((M.conjTranspose * M).det).re = _
    rw [hG.det_eq_prod_eigenvalues]
    simp [Fin.prod_univ_three]
  have htrace : frobeniusSq M =
      hG.eigenvalues 0 + hG.eigenvalues 1 + hG.eigenvalues 2 := by
    unfold frobeniusSq columnGram
    rw [hG.trace_eq_sum_eigenvalues]
    simp [Fin.sum_univ_three]
  rw [hdet, htrace]
  exact ScalarEstimates.amgm_three _ _ _
    (Matrix.eigenvalues_conjTranspose_mul_self_nonneg M 0)
    (Matrix.eigenvalues_conjTranspose_mul_self_nonneg M 1)
    (Matrix.eigenvalues_conjTranspose_mul_self_nonneg M 2)

theorem normSq_det_eq_iff_eigenvalues (M : Matrix (Fin 3) (Fin 3) ℂ) :
    27 * Complex.normSq M.det = frobeniusSq M ^ 3 ↔
      (Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues 0 =
        (Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues 1 ∧
      (Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues 1 =
        (Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues 2 := by
  let hG := Matrix.isHermitian_conjTranspose_mul_self M
  have hdet : Complex.normSq M.det =
      hG.eigenvalues 0 * hG.eigenvalues 1 * hG.eigenvalues 2 := by
    rw [← determinant_gram_real M]
    change ((M.conjTranspose * M).det).re = _
    rw [hG.det_eq_prod_eigenvalues]
    simp [Fin.prod_univ_three]
  have htrace : frobeniusSq M =
      hG.eigenvalues 0 + hG.eigenvalues 1 + hG.eigenvalues 2 := by
    unfold frobeniusSq columnGram
    rw [hG.trace_eq_sum_eigenvalues]
    simp [Fin.sum_univ_three]
  rw [hdet, htrace]
  exact ScalarEstimates.amgm_three_eq_iff _ _ _
    (Matrix.eigenvalues_conjTranspose_mul_self_nonneg M 0)
    (Matrix.eigenvalues_conjTranspose_mul_self_nonneg M 1)
    (Matrix.eigenvalues_conjTranspose_mul_self_nonneg M 2)

/-- Equality forces the entire Gram matrix scalar, without an invertibility hypothesis. -/
theorem normSq_det_equality_gram (M : Matrix (Fin 3) (Fin 3) ℂ)
    (heq : 27 * Complex.normSq M.det = frobeniusSq M ^ 3) :
    columnGram M = Matrix.diagonal (fun _ => (frobeniusSq M / 3 : ℂ)) := by
  let hG := Matrix.isHermitian_conjTranspose_mul_self M
  obtain ⟨h01, h12⟩ := (normSq_det_eq_iff_eigenvalues M).mp heq
  have htrace : frobeniusSq M =
      hG.eigenvalues 0 + hG.eigenvalues 1 + hG.eigenvalues 2 := by
    unfold frobeniusSq columnGram
    rw [hG.trace_eq_sum_eigenvalues]
    simp [Fin.sum_univ_three]
  have hfun : hG.eigenvalues = fun _ => frobeniusSq M / 3 := by
    funext i
    fin_cases i <;> dsimp <;> linarith
  change M.conjTranspose * M = _
  rw [hG.spectral_theorem, hfun]
  simp only [Function.comp_def, Unitary.conjStarAlgAut_apply]
  simp only [← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, Unitary.mul_star_self, OneMemClass.coe_one]
  norm_cast
  simp only [Unitary.mul_star_self, OneMemClass.coe_one]
  exact algebraMap_smul ℂ (frobeniusSq M/3) (1 : Matrix (Fin 3) (Fin 3) ℂ)

theorem normSq_det_eq_iff (M : Matrix (Fin 3) (Fin 3) ℂ) :
    27 * Complex.normSq M.det = frobeniusSq M ^ 3 ↔
      columnGram M = Matrix.diagonal (fun _ => (frobeniusSq M / 3 : ℂ)) := by
  constructor
  · exact normSq_det_equality_gram M
  · intro hG
    have hd := determinant_gram_real M
    rw [hG, Matrix.det_diagonal] at hd
    simp [Fin.prod_univ_three] at hd
    norm_cast at hd
    rw [← hd]
    ring

theorem im_det_sq_le_normSq (M : Matrix (Fin 3) (Fin 3) ℂ) :
    M.det.im ^ 2 ≤ Complex.normSq M.det := by
  simp [Complex.normSq_apply]
  nlinarith [sq_nonneg M.det.re]

theorem im_det_eq_normSq_iff (M : Matrix (Fin 3) (Fin 3) ℂ) :
    M.det.im ^ 2 = Complex.normSq M.det ↔ M.det.re = 0 := by
  simp only [Complex.normSq_apply]
  constructor
  · intro h
    nlinarith [sq_nonneg M.det.re]
  · intro h
    simp [h, pow_two]

end
end Glennie.MatrixDetEstimate
