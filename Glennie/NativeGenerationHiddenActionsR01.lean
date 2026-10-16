/- Hidden-action stage toward native unital generation.
No hidden spanning or full generation conclusion is assumed. -/
module
public import Glennie.NativeGenerationComplexSectorR01
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section
namespace Glennie.NativeGenerationHiddenActionsR01
noncomputable section
open Glennie.NativeGenerationCoordinatesR01
open Glennie.NativeGenerationPeirceTriangleR01

private theorem complexOct_one : complexOct 1 = octScalar 1 := by
  apply Prod.ext <;> apply Quaternion.ext <;> simp [complexOct, octScalar]

def E01 : Octonion →ₗ[ℝ] Albert where
  toFun q := ⟨0, 0, 0, q, 0, 0⟩
  map_add' q r := by ext <;> simp
  map_smul' t q := by ext <;> simp

def E02 : Octonion →ₗ[ℝ] Albert where
  toFun q := ⟨0, 0, 0, 0, q, 0⟩
  map_add' q r := by ext <;> simp
  map_smul' t q := by ext <;> simp

def E12 : Octonion →ₗ[ℝ] Albert where
  toFun q := ⟨0, 0, 0, 0, 0, q⟩
  map_add' q r := by ext <;> simp
  map_smul' t q := by ext <;> simp

theorem cross01_12 (q r : Octonion) :
    (2 : ℝ) • jordan (E01 q) (E12 r) = E02 (octMul q r) := by
  ext <;> simp [E01, E02, E12, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul,
    octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul, smul_eq_mul]
  all_goals ring
  all_goals norm_num [octNormSq, Quaternion.normSq_def']

theorem cross01_02 (q r : Octonion) :
    (2 : ℝ) • jordan (E01 q) (E02 r) = E12 (octMul (octConj q) r) := by
  ext <;> simp [E01, E02, E12, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul,
    octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul, smul_eq_mul]
  all_goals ring
  all_goals norm_num [octNormSq, Quaternion.normSq_def']

theorem cross02_12 (q r : Octonion) :
    (2 : ℝ) • jordan (E02 q) (E12 r) = E01 (octMul q (octConj r)) := by
  ext <;> simp [E01, E02, E12, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul,
    octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul, smul_eq_mul]
  all_goals ring
  all_goals norm_num [octNormSq, Quaternion.normSq_def']

theorem common02_left_i (q : Octonion) :
    (4 : ℝ) • jordan (E01 (complexOct Complex.I))
      (jordan (E01 (octScalar 1)) (E02 q)) =
      E02 (octMul (complexOct Complex.I) q) := by
  ext <;> simp [E01, E02, E12, complexOct, octScalar,
    jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
    octDot_coordinates, octMul, octConj, Quaternion.re_mul,
    Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, smul_eq_mul]
  all_goals ring
  all_goals norm_num [octNormSq, Quaternion.normSq_def']

theorem complexAlbert_mem (K : Submodule ℝ Albert) (hC : complexSector ≤ K)
    (a b c : ℝ) (u v w : ℂ) : complexAlbert a b c u v w ∈ K :=
  hC ⟨((a, b, c), (u, v, w)), rfl⟩

theorem complex_slot01_mem (K : Submodule ℝ Albert)
    (hC : complexSector ≤ K) (u : ℂ) : E01 (complexOct u) ∈ K := by
  change complexAlbert 0 0 0 u 0 0 ∈ K
  exact complexAlbert_mem K hC _ _ _ _ _ _

theorem complex_slot02_mem (K : Submodule ℝ Albert)
    (hC : complexSector ≤ K) (u : ℂ) : E02 (complexOct u) ∈ K := by
  change complexAlbert 0 0 0 0 u 0 ∈ K
  exact complexAlbert_mem K hC _ _ _ _ _ _

theorem complex_slot12_mem (K : Submodule ℝ Albert)
    (hC : complexSector ≤ K) (u : ℂ) : E12 (complexOct u) ∈ K := by
  change complexAlbert 0 0 0 0 0 u ∈ K
  exact complexAlbert_mem K hC _ _ _ _ _ _

def residual (q : Octonion) : Octonion := q - complexOct (complexPart q)

theorem residual_eq_hiddenOct (q : Octonion) :
    residual q = hiddenOct (hiddenColumn q) := by
  have h := oct_complex_hidden_decomposition q
  dsimp [residual]
  exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using h.symm)

theorem hiddenColumn_residual (q : Octonion) :
    hiddenColumn (residual q) = hiddenColumn q := by
  rw [residual_eq_hiddenOct, hiddenColumn_hiddenOct]

theorem residual_slot01_mem (K : Submodule ℝ Albert)
    (hC : complexSector ≤ K) (q : Octonion) (hq : E01 q ∈ K) :
    E01 (residual q) ∈ K := by
  dsimp [residual]
  rw [map_sub]
  exact K.sub_mem hq (complex_slot01_mem K hC (complexPart q))

theorem residual_slot02_mem (K : Submodule ℝ Albert)
    (hC : complexSector ≤ K) (q : Octonion) (hq : E02 q ∈ K) :
    E02 (residual q) ∈ K := by
  dsimp [residual]
  rw [map_sub]
  exact K.sub_mem hq (complex_slot02_mem K hC (complexPart q))

theorem residual_slot12_mem (K : Submodule ℝ Albert)
    (hC : complexSector ≤ K) (q : Octonion) (hq : E12 q ∈ K) :
    E12 (residual q) ∈ K := by
  dsimp [residual]
  rw [map_sub]
  exact K.sub_mem hq (complex_slot12_mem K hC (complexPart q))

theorem common02_left_i_mem (K : Submodule ℝ Albert)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (hC : complexSector ≤ K) (q : Octonion) (hq : E02 q ∈ K) :
    E02 (octMul (complexOct Complex.I) q) ∈ K := by
  rw [← common02_left_i]
  exact K.smul_mem 4 (hJ _ (complex_slot01_mem K hC Complex.I) _
    (hJ _ (by simpa only [complexOct_one] using complex_slot01_mem K hC 1) _ hq))

/-- Transfers use the 02 slot; neither transfer conjugates the residual. -/
theorem transfer12_to02_mem (K : Submodule ℝ Albert)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (hC : complexSector ≤ K) (q : Octonion) (hq : E12 q ∈ K) :
    E02 q ∈ K := by
  have he := cross01_12 (octScalar 1) q
  simp only [octMul_scalar_left, one_smul] at he
  rw [← he]
  exact K.smul_mem 2 (hJ _
    (by simpa only [complexOct_one] using complex_slot01_mem K hC 1) _ hq)

theorem transfer01_to02_mem (K : Submodule ℝ Albert)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (hC : complexSector ≤ K) (q : Octonion) (hq : E01 q ∈ K) :
    E02 q ∈ K := by
  have he := cross01_12 q (octScalar 1)
  simp only [octMul_scalar_right, one_smul] at he
  rw [← he]
  exact K.smul_mem 2 (hJ _ hq _
    (by simpa only [complexOct_one] using complex_slot12_mem K hC 1))

/-- The exact finite complex matrix interface for the next real-span stage. -/
theorem exists_hidden_coefficients (M : Matrix (Fin 3) (Fin 3) ℂ)
    (hdet : M.det ≠ 0) (v : Fin 3 → ℂ) : ∃ c, M.mulVec c = v := by
  refine ⟨M⁻¹.mulVec v, ?_⟩
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]

end
end Glennie.NativeGenerationHiddenActionsR01
