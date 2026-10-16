/- Hidden completion from complex-sector membership and an invertible hidden matrix. -/
module
public import Glennie.NativeGenerationHiddenSpanR01

@[expose] public section
namespace Glennie.NativeGenerationHiddenCompletionR01
noncomputable section
open Glennie.NativeGenerationCoordinatesR01
open Glennie.NativeGenerationPeirceTriangleR01
open Glennie.NativeGenerationHiddenActionsR01
open Glennie.NativeGenerationHiddenSpanR01

private theorem complexOct_one_completion : complexOct 1 = octScalar 1 := by
  apply Prod.ext <;> apply Quaternion.ext <;> simp [complexOct, octScalar]

theorem hiddenOct_hiddenMatrix0 (z : Albert) :
    hiddenOct (fun i => hiddenMatrix z i 0) = -residual z.o12 := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [hiddenOct, hiddenMatrix, hiddenColumn, NativeGenerationHiddenActionsR01.residual, complexOct, complexPart]

theorem hiddenOct_hiddenMatrix1 (z : Albert) :
    hiddenOct (fun i => hiddenMatrix z i 1) = residual z.o02 := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [hiddenOct, hiddenMatrix, hiddenColumn, NativeGenerationHiddenActionsR01.residual, complexOct, complexPart]

theorem hiddenOct_hiddenMatrix2 (z : Albert) :
    hiddenOct (fun i => hiddenMatrix z i 2) = -residual z.o01 := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [hiddenOct, hiddenMatrix, hiddenColumn, NativeGenerationHiddenActionsR01.residual, complexOct, complexPart]

theorem raw_decomposition (z : Albert) :
    z = z.d0 • diagonalAlbert 1 0 0 + z.d1 • diagonalAlbert 0 1 0 +
      z.d2 • diagonalAlbert 0 0 1 + E01 z.o01 + E02 z.o02 + E12 z.o12 := by
  ext <;> simp [diagonalAlbert, E01, E02, E12]

/-- The missing hidden propagation bridge, reduced to explicit coordinate
operations and ordinary complex nonsingular matrix inversion. -/
theorem eq_top_of_complexSector_le_hidden_det
    (K : Submodule ℝ Albert)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (hC : complexSector ≤ K)
    (z : Albert) (hz : z ∈ K) (hdet : (hiddenMatrix z).det ≠ 0) : K = ⊤ := by
  have he0 : diagonalAlbert 1 0 0 ∈ K := complexAlbert_mem K hC 1 0 0 0 0 0
  have he1 : diagonalAlbert 0 1 0 ∈ K := complexAlbert_mem K hC 0 1 0 0 0 0
  have he2 : diagonalAlbert 0 0 1 ∈ K := complexAlbert_mem K hC 0 0 1 0 0 0
  have hz01 : E01 z.o01 ∈ K := peirce01_mem K hJ he0 he1 z hz
  have hz02 : E02 z.o02 ∈ K := peirce02_mem K hJ he0 he2 z hz
  have hz12 : E12 z.o12 ∈ K := peirce12_mem K hJ he1 he2 z hz
  have hw : ∀ j : Fin 3, E02 (hiddenOct (fun i => hiddenMatrix z i j)) ∈ K := by
    intro j
    fin_cases j
    · change E02 (hiddenOct (fun i => hiddenMatrix z i 0)) ∈ K
      rw [hiddenOct_hiddenMatrix0, map_neg]
      exact K.neg_mem (transfer12_to02_mem K hJ hC _ (residual_slot12_mem K hC _ hz12))
    · change E02 (hiddenOct (fun i => hiddenMatrix z i 1)) ∈ K
      rw [hiddenOct_hiddenMatrix1]
      exact residual_slot02_mem K hC _ hz02
    · change E02 (hiddenOct (fun i => hiddenMatrix z i 2)) ∈ K
      rw [hiddenOct_hiddenMatrix2, map_neg]
      exact K.neg_mem (transfer01_to02_mem K hJ hC _ (residual_slot01_mem K hC _ hz01))
  have hi : ∀ j : Fin 3, E02 (octMul (complexOct Complex.I)
      (hiddenOct (fun i => hiddenMatrix z i j))) ∈ K :=
    fun j => common02_left_i_mem K hJ hC _ (hw j)
  have hall02 : ∀ q : Octonion, E02 q ∈ K := by
    intro q
    rw [← oct_complex_hidden_decomposition q, map_add]
    exact K.add_mem (complex_slot02_mem K hC _) (hidden_slot02_mem_of_columns K
      (hiddenMatrix z) hdet hw hi (hiddenColumn q))
  have hall01 : ∀ q : Octonion, E01 q ∈ K := by
    intro q
    have he := cross02_12 q (octScalar 1)
    simp only [octConj_scalar, octMul_scalar_right, one_smul] at he
    rw [← he]
    exact K.smul_mem 2 (hJ _ (hall02 q) _
      (by simpa only [complexOct_one_completion] using complex_slot12_mem K hC 1))
  have hall12 : ∀ q : Octonion, E12 q ∈ K := by
    intro q
    have he := cross01_02 (octScalar 1) q
    simp only [octConj_scalar, octMul_scalar_left, one_smul] at he
    rw [← he]
    exact K.smul_mem 2 (hJ _
      (by simpa only [complexOct_one_completion] using complex_slot01_mem K hC 1) _ (hall02 q))
  apply top_unique
  intro t ht
  rw [raw_decomposition t]
  exact K.add_mem
    (K.add_mem
      (K.add_mem
        (K.add_mem (K.add_mem (K.smul_mem _ he0) (K.smul_mem _ he1))
          (K.smul_mem _ he2))
        (hall01 _))
      (hall02 _))
    (hall12 _)

end
end Glennie.NativeGenerationHiddenCompletionR01
