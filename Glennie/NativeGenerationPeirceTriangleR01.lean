/- Second coordinate stage toward native unital generation.
No full generation result is assumed here. -/
module
public import Glennie.NativeGenerationCoordinatesR01
public import Mathlib.LinearAlgebra.Complex.Module

@[expose] public section
namespace Glennie.NativeGenerationPeirceTriangleR01
noncomputable section
open Glennie.NativeGenerationCoordinatesR01

theorem diagonal_projector_middle_numerator (a b c : ℝ) :
    jordan (diagonalAlbert a b c) (diagonalAlbert a b c) -
      (a + c) • diagonalAlbert a b c + (a * c) • (1 : Albert) =
      ((b - a) * (b - c)) • diagonalAlbert 0 1 0 := by
  apply Albert.ext
  all_goals simp [diagonalAlbert, unit, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12, octDot, octRe, octMul, octConj]
  all_goals ring

theorem diagonal_projector_middle_mem
    (K : Submodule ℝ Albert) (h1 : (1 : Albert) ∈ K)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (a b c : ℝ) (hx : diagonalAlbert a b c ∈ K)
    (hg1 : b - a ≠ 0) (hg2 : b - c ≠ 0) :
    diagonalAlbert 0 1 0 ∈ K := by
  have hn : jordan (diagonalAlbert a b c) (diagonalAlbert a b c) -
      (a + c) • diagonalAlbert a b c + (a * c) • (1 : Albert) ∈ K :=
    K.add_mem (K.sub_mem (hJ _ hx _ hx) (K.smul_mem _ hx)) (K.smul_mem _ h1)
  rw [diagonal_projector_middle_numerator] at hn
  have hp := K.smul_mem (((b - a) * (b - c))⁻¹) hn
  simpa only [smul_smul, inv_mul_cancel₀ (mul_ne_zero hg1 hg2), one_smul] using hp

theorem diagonal_projector_last_numerator (a b c : ℝ) :
    jordan (diagonalAlbert a b c) (diagonalAlbert a b c) -
      (a + b) • diagonalAlbert a b c + (a * b) • (1 : Albert) =
      ((c - a) * (c - b)) • diagonalAlbert 0 0 1 := by
  apply Albert.ext
  all_goals simp [diagonalAlbert, unit, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12, octDot, octRe, octMul, octConj]
  all_goals ring

theorem diagonal_projector_last_mem
    (K : Submodule ℝ Albert) (h1 : (1 : Albert) ∈ K)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (a b c : ℝ) (hx : diagonalAlbert a b c ∈ K)
    (hg1 : c - a ≠ 0) (hg2 : c - b ≠ 0) :
    diagonalAlbert 0 0 1 ∈ K := by
  have hn : jordan (diagonalAlbert a b c) (diagonalAlbert a b c) -
      (a + b) • diagonalAlbert a b c + (a * b) • (1 : Albert) ∈ K :=
    K.add_mem (K.sub_mem (hJ _ hx _ hx) (K.smul_mem _ hx)) (K.smul_mem _ h1)
  rw [diagonal_projector_last_numerator] at hn
  have hp := K.smul_mem (((c - a) * (c - b))⁻¹) hn
  simpa only [smul_smul, inv_mul_cancel₀ (mul_ne_zero hg1 hg2), one_smul] using hp

theorem peirce02_extract (z : Albert) :
    (4 : ℝ) • jordan (diagonalAlbert 1 0 0)
      (jordan (diagonalAlbert 0 0 1) z) =
      (⟨0, 0, 0, 0, z.o02, 0⟩ : Albert) := by
  apply Albert.ext
  all_goals norm_num [diagonalAlbert, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12, octDot, octRe, octMul, octConj,
    smul_smul]
  all_goals apply Prod.ext <;> apply Quaternion.ext <;> norm_num

theorem peirce02_mem (K : Submodule ℝ Albert)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (h0 : diagonalAlbert 1 0 0 ∈ K) (h1 : diagonalAlbert 0 0 1 ∈ K)
    (z : Albert) (hz : z ∈ K) : (⟨0, 0, 0, 0, z.o02, 0⟩ : Albert) ∈ K := by
  rw [← peirce02_extract]
  exact K.smul_mem 4 (hJ _ h0 _ (hJ _ h1 _ hz))

theorem peirce12_extract (z : Albert) :
    (4 : ℝ) • jordan (diagonalAlbert 0 1 0)
      (jordan (diagonalAlbert 0 0 1) z) =
      (⟨0, 0, 0, 0, 0, z.o12⟩ : Albert) := by
  apply Albert.ext
  all_goals norm_num [diagonalAlbert, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12, octDot, octRe, octMul, octConj,
    smul_smul]
  all_goals apply Prod.ext <;> apply Quaternion.ext <;> norm_num

theorem peirce12_mem (K : Submodule ℝ Albert)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (h0 : diagonalAlbert 0 1 0 ∈ K) (h1 : diagonalAlbert 0 0 1 ∈ K)
    (z : Albert) (hz : z ∈ K) : (⟨0, 0, 0, 0, 0, z.o12⟩ : Albert) ∈ K := by
  rw [← peirce12_extract]
  exact K.smul_mem 4 (hJ _ h0 _ (hJ _ h1 _ hz))

/-- Division-free real inversion in the complex plane. -/
theorem complex_real_det_expansion (u v z : ℂ) :
    (u.re * v.im - u.im * v.re) • z =
      (z.re * v.im - z.im * v.re) • u +
      (u.re * z.im - u.im * z.re) • v := by
  apply Complex.ext <;>
    simp [Complex.smul_re, Complex.smul_im, smul_eq_mul] <;> ring

/-- Two complex coordinates with nonzero real determinant fill a real-linear
image, without imposing a complex module structure on the ambient submodule. -/
theorem complex_line_mem_of_real_det_ne_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (K : Submodule ℝ V) (T : ℂ →ₗ[ℝ] V) (u v : ℂ)
    (hu : T u ∈ K) (hv : T v ∈ K)
    (hd : u.re * v.im - u.im * v.re ≠ 0) (z : ℂ) : T z ∈ K := by
  have hm : (u.re * v.im - u.im * v.re) • T z ∈ K := by
    have he := congrArg T (complex_real_det_expansion u v z)
    simp only [map_smul, map_add] at he
    rw [he]
    exact K.add_mem (K.smul_mem _ hu) (K.smul_mem _ hv)
  have hp := K.smul_mem ((u.re * v.im - u.im * v.re)⁻¹) hm
  simpa only [smul_smul, inv_mul_cancel₀ hd, one_smul] using hp

theorem triangle_real_det01 (u v w : ℂ) :
    u.re * (v * star w).im - u.im * (v * star w).re =
      -(u * w * star v).im := by
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem triangle_real_det12 (u v w : ℂ) :
    w.re * (star u * v).im - w.im * (star u * v).re =
      -(u * w * star v).im := by
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem triangle_real_det02 (u v w : ℂ) :
    v.re * (u * w).im - v.im * (u * w).re =
      (u * w * star v).im := by
  simp [Complex.mul_re, Complex.mul_im]
  ring

end
end Glennie.NativeGenerationPeirceTriangleR01
