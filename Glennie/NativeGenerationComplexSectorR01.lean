/- Third stage toward native unital generation.
This module establishes complex-sector containment, not full Albert generation. -/
module
public import Glennie.NativeGenerationPeirceTriangleR01
public import Glennie.SectorSubspace

@[expose] public section
namespace Glennie.NativeGenerationComplexSectorR01
noncomputable section
open Glennie.NativeGenerationCoordinatesR01
open Glennie.NativeGenerationPeirceTriangleR01

private theorem complexOct_zero : complexOct (0 : ℂ) = (0 : Octonion) := by
  apply Prod.ext <;> apply Quaternion.ext <;> simp [complexOct]

def slot01 : ℂ →ₗ[ℝ] Albert where
  toFun u := complexAlbert 0 0 0 u 0 0
  map_add' u v := by
    ext <;> simp [complexAlbert, complexOct]
  map_smul' r u := by
    ext <;> simp [complexAlbert, complexOct, smul_eq_mul]

def slot02 : ℂ →ₗ[ℝ] Albert where
  toFun u := complexAlbert 0 0 0 0 u 0
  map_add' u v := by
    ext <;> simp [complexAlbert, complexOct]
  map_smul' r u := by
    ext <;> simp [complexAlbert, complexOct, smul_eq_mul]

def slot12 : ℂ →ₗ[ℝ] Albert where
  toFun u := complexAlbert 0 0 0 0 0 u
  map_add' u v := by
    ext <;> simp [complexAlbert, complexOct]
  map_smul' r u := by
    ext <;> simp [complexAlbert, complexOct, smul_eq_mul]

theorem cross_slot01_12 (u v w : ℂ) :
    (2 : ℝ) • jordan (slot01 u) (slot12 w) = slot02 (u * w) := by
  ext <;> simp [slot01, slot02, slot12, complexAlbert, complexOct,
    jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
    octDot_coordinates, octMul, octConj, Quaternion.re_mul,
    Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    Complex.mul_re, Complex.mul_im, smul_eq_mul]
  all_goals ring
  all_goals norm_num [octNormSq, Quaternion.normSq_def']

theorem cross_slot01_02 (u v w : ℂ) :
    (2 : ℝ) • jordan (slot01 u) (slot02 v) = slot12 (star u * v) := by
  ext <;> simp [slot01, slot02, slot12, complexAlbert, complexOct,
    jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
    octDot_coordinates, octMul, octConj, Quaternion.re_mul,
    Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    Complex.mul_re, Complex.mul_im, smul_eq_mul]
  all_goals ring
  all_goals norm_num [octNormSq, Quaternion.normSq_def']

theorem cross_slot02_12 (u v w : ℂ) :
    (2 : ℝ) • jordan (slot02 v) (slot12 w) = slot01 (v * star w) := by
  ext <;> simp [slot01, slot02, slot12, complexAlbert, complexOct,
    jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
    octDot_coordinates, octMul, octConj, Quaternion.re_mul,
    Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    Complex.mul_re, Complex.mul_im, smul_eq_mul]
  all_goals ring
  all_goals norm_num [octNormSq, Quaternion.normSq_def']

theorem complexAlbert_decomposition (a b c : ℝ) (u v w : ℂ) :
    complexAlbert a b c u v w =
      a • diagonalAlbert 1 0 0 + b • diagonalAlbert 0 1 0 +
      c • diagonalAlbert 0 0 1 + slot01 u + slot02 v + slot12 w := by
  ext <;> simp [complexAlbert, diagonalAlbert, complexOct, slot01, slot02, slot12]

/-- A regular diagonal generator and a complex generator with nonzero triangle
area force the entire actual nine-dimensional complex sector into K. -/
theorem complexSector_le_of_regular_triangle
    (K : Submodule ℝ Albert) (h1 : (1 : Albert) ∈ K)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (a b c d e f : ℝ) (u v w : ℂ)
    (hx : diagonalAlbert a b c ∈ K)
    (hy : complexAlbert d e f u v w ∈ K)
    (hab : a - b ≠ 0) (hbc : b - c ≠ 0) (hca : c - a ≠ 0)
    (htriangle : (u * w * star v).im ≠ 0) : complexSector ≤ K := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hab))
  have hac : a - c ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hca))
  have hcb : c - b ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hbc))
  have he0 := diagonal_projector_first_mem K h1 hJ a b c hx hab hac
  have he1 := diagonal_projector_middle_mem K h1 hJ a b c hx hba hbc
  have he2 := diagonal_projector_last_mem K h1 hJ a b c hx hca hcb
  have hu : slot01 u ∈ K := by
    simpa [slot01, complexAlbert, complexOct_zero] using
      peirce01_mem K hJ he0 he1 (complexAlbert d e f u v w) hy
  have hv : slot02 v ∈ K := by
    simpa [slot02, complexAlbert, complexOct_zero] using
      peirce02_mem K hJ he0 he2 (complexAlbert d e f u v w) hy
  have hw : slot12 w ∈ K := by
    simpa [slot12, complexAlbert, complexOct_zero] using
      peirce12_mem K hJ he1 he2 (complexAlbert d e f u v w) hy
  have huv : slot12 (star u * v) ∈ K := by
    rw [← cross_slot01_02 u v w]
    exact K.smul_mem 2 (hJ _ hu _ hv)
  have huw : slot02 (u * w) ∈ K := by
    rw [← cross_slot01_12 u v w]
    exact K.smul_mem 2 (hJ _ hu _ hw)
  have hvw : slot01 (v * star w) ∈ K := by
    rw [← cross_slot02_12 u v w]
    exact K.smul_mem 2 (hJ _ hv _ hw)
  have hdet01 : u.re * (v * star w).im - u.im * (v * star w).re ≠ 0 := by
    rw [triangle_real_det01]
    exact neg_ne_zero.mpr htriangle
  have hdet12 : w.re * (star u * v).im - w.im * (star u * v).re ≠ 0 := by
    rw [triangle_real_det12]
    exact neg_ne_zero.mpr htriangle
  have hdet02 : v.re * (u * w).im - v.im * (u * w).re ≠ 0 := by
    rw [triangle_real_det02]
    exact htriangle
  have h01 : ∀ z : ℂ, slot01 z ∈ K :=
    complex_line_mem_of_real_det_ne_zero K slot01 u (v * star w) hu hvw hdet01
  have h12 : ∀ z : ℂ, slot12 z ∈ K :=
    complex_line_mem_of_real_det_ne_zero K slot12 w (star u * v) hw huv hdet12
  have h02 : ∀ z : ℂ, slot02 z ∈ K :=
    complex_line_mem_of_real_det_ne_zero K slot02 v (u * w) hv huw hdet02
  intro z hz
  rcases hz with ⟨q, rfl⟩
  change complexAlbert q.1.1 q.1.2.1 q.1.2.2 q.2.1 q.2.2.1 q.2.2.2 ∈ K
  rw [complexAlbert_decomposition]
  exact K.add_mem
    (K.add_mem
      (K.add_mem
        (K.add_mem
          (K.add_mem (K.smul_mem _ he0) (K.smul_mem _ he1))
          (K.smul_mem _ he2))
        (h01 _))
      (h02 _))
    (h12 _)

end
end Glennie.NativeGenerationComplexSectorR01
