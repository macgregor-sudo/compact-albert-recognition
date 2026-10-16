/- Determinant-to-real-span bridge for hidden octonion columns. -/
module
public import Glennie.NativeGenerationHiddenActionsR01

@[expose] public section
namespace Glennie.NativeGenerationHiddenSpanR01
noncomputable section
open Glennie.NativeGenerationCoordinatesR01
open Glennie.NativeGenerationHiddenActionsR01

/-- Explicit real coefficient expansion; no complex module on octonions. -/
theorem hiddenOct_mulVec_real (M : Matrix (Fin 3) (Fin 3) ℂ)
    (c : Fin 3 → ℂ) :
    hiddenOct (M.mulVec c) =
      ∑ j : Fin 3,
        ((c j).re • hiddenOct (fun i => M i j) +
          (c j).im • octMul (complexOct Complex.I) (hiddenOct (fun i => M i j))) := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [hiddenOct, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      complexOct, octMul, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul,
      Complex.mul_re, Complex.mul_im, smul_eq_mul]
  all_goals ring

/-- Three invertible complex columns with their native left-i images span
all residual octonions inside one common real Peirce slot. -/
theorem hidden_slot02_mem_of_columns
    (K : Submodule ℝ Albert) (M : Matrix (Fin 3) (Fin 3) ℂ)
    (hdet : M.det ≠ 0)
    (hw : ∀ j, E02 (hiddenOct (fun i => M i j)) ∈ K)
    (hi : ∀ j, E02 (octMul (complexOct Complex.I)
      (hiddenOct (fun i => M i j))) ∈ K)
    (v : Fin 3 → ℂ) : E02 (hiddenOct v) ∈ K := by
  obtain ⟨c, hc⟩ := exists_hidden_coefficients M hdet v
  rw [← hc, hiddenOct_mulVec_real, map_sum]
  apply K.sum_mem
  intro j hj
  rw [map_add, map_smul, map_smul]
  exact K.add_mem (K.smul_mem _ (hw j)) (K.smul_mem _ (hi j))

end
end Glennie.NativeGenerationHiddenSpanR01
