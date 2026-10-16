/- Dimension-parametric coordinatewise Euclidean Jordan target. -/
module
public import Glennie.Compact.NormCompatibleNullTargetR01

@[expose] public section
namespace Glennie.Compact.VariableDiagonalNullTargetR01
noncomputable section
open scoped BigOperators
open Glennie.Compact.CyclicTraceNullR01

abbrev DiagonalN (n : ℕ) := EuclideanSpace ℝ (Fin n)

def diagonalNProduct {n : ℕ} (a b : DiagonalN n) : DiagonalN n :=
  WithLp.toLp 2 (fun i => a i * b i)

def diagonalNRepresentation (n : ℕ) : DiagonalN n →ₗ[ℝ] (Fin n → ℝ) where
  toFun a := fun i => a i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def diagonalNTrace (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun a := ∑ i, a i
  map_add' a b := Finset.sum_add_distrib
  map_smul' r a := by simp [Finset.mul_sum]

theorem diagonalN_product_map {n : ℕ} (a b : DiagonalN n) :
    diagonalNRepresentation n (diagonalNProduct a b) =
      symmProd (diagonalNRepresentation n a) (diagonalNRepresentation n b) := by
  funext i
  change a i * b i = (1/2:ℝ) * (a i * b i + b i * a i)
  ring

theorem diagonalN_metric_compatible {n : ℕ} (a b : DiagonalN n) :
    Inner.inner ℝ a b =
      diagonalNTrace n (diagonalNRepresentation n a * diagonalNRepresentation n b) := by
  change (∑ i, b i * a i) = ∑ i, a i * b i
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem diagonalN_trace_cyclic (n : ℕ) (a b : Fin n → ℝ) :
    diagonalNTrace n (a*b) = diagonalNTrace n (b*a) := by rw [mul_comm]

theorem diagonalN_phi_zero {n : ℕ} (x y z : DiagonalN n) :
    phiWith diagonalNProduct (Inner.inner ℝ) x y z = 0 :=
  phiWith_eq_zero_of_compatible_trace diagonalNProduct (Inner.inner ℝ)
    (diagonalNRepresentation n) (diagonalNTrace n) diagonalN_product_map
    diagonalN_metric_compatible (diagonalN_trace_cyclic n) x y z

theorem diagonalN_product_norm {n : ℕ} (a b : DiagonalN n) :
    ‖diagonalNProduct a b‖ ≤ ‖a‖ * ‖b‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, EuclideanSpace.real_norm_sq_eq (diagonalNProduct a b),
    EuclideanSpace.real_norm_sq_eq b, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have ha : (a i)^2 ≤ ‖a‖^2 := by
    have hh := (sq_le_sq₀ (norm_nonneg (a i)) (norm_nonneg a)).mpr
      (PiLp.norm_apply_le a i)
    simpa only [Real.norm_eq_abs, sq_abs] using hh
  change (a i*b i)^2 ≤ ‖a‖^2 * (b i)^2
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right ha (sq_nonneg _)

theorem diagonalN_quadratic_sandwich {n : ℕ} (a b : DiagonalN n) :
    quadraticWith diagonalNProduct a b = diagonalNProduct a (diagonalNProduct a b) := by
  ext i
  change 2*(a i*(a i*b i)) - (a i*a i)*b i = a i*(a i*b i)
  ring

theorem diagonalN_quadratic_norm {n : ℕ} (a b : DiagonalN n) :
    ‖quadraticWith diagonalNProduct a b‖ ≤ ‖a‖^2 * ‖b‖ := by
  rw [diagonalN_quadratic_sandwich]
  calc
    ‖diagonalNProduct a (diagonalNProduct a b)‖ ≤ ‖a‖ * ‖diagonalNProduct a b‖ :=
      diagonalN_product_norm _ _
    _ ≤ ‖a‖ * (‖a‖ * ‖b‖) :=
      mul_le_mul_of_nonneg_left (diagonalN_product_norm _ _) (norm_nonneg _)
    _ = ‖a‖^2 * ‖b‖ := by ring

end
end Glennie.Compact.VariableDiagonalNullTargetR01
