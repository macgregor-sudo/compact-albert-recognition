/- Concrete dimension27 diagonal target plus generic representation bounds. -/
module
public import Glennie.Compact.CyclicTraceNullR01
public import Glennie.Hilbert
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.Positivity

@[expose] public section
namespace Glennie.Compact.NormCompatibleNullTargetR01
noncomputable section
open scoped BigOperators
open Glennie.Compact.CyclicTraceNullR01

section RepresentedBounds
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing M] [NormedAlgebra ℝ M]

theorem symmProd_norm (a b : M) :
    ‖symmProd a b‖ ≤ ‖a‖ * ‖b‖ := by
  rw [symmProd, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
  calc
    (1/2:ℝ) * ‖a*b+b*a‖ ≤ (1/2:ℝ) * (‖a*b‖+‖b*a‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ ≤ (1/2:ℝ) * (‖a‖*‖b‖+‖b‖*‖a‖) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (norm_mul_le _ _) (norm_mul_le _ _)) (by norm_num)
    _ = ‖a‖*‖b‖ := by ring

theorem represented_product_norm (j : E → E → E) (ρ : E →ₗᵢ[ℝ] M)
    (hj : ∀ a b, ρ (j a b) = symmProd (ρ a) (ρ b)) (a b : E) :
    ‖j a b‖ ≤ ‖a‖ * ‖b‖ := by
  rw [← ρ.norm_map (j a b), hj]
  simpa only [ρ.norm_map] using symmProd_norm (ρ a) (ρ b)

theorem represented_quadratic_norm (j : E → E → E) (ρ : E →ₗᵢ[ℝ] M)
    (hj : ∀ a b, ρ (j a b) = symmProd (ρ a) (ρ b)) (a b : E) :
    ‖quadraticWith j a b‖ ≤ ‖a‖^2 * ‖b‖ := by
  rw [← ρ.norm_map (quadraticWith j a b)]
  change ‖ρ.toLinearMap (quadraticWith j a b)‖ ≤ _
  rw [map_quadraticWith j ρ.toLinearMap hj, quadratic_eq_sandwich]
  calc
    ‖ρ a * ρ b * ρ a‖ ≤ ‖ρ a * ρ b‖ * ‖ρ a‖ := norm_mul_le _ _
    _ ≤ (‖ρ a‖ * ‖ρ b‖) * ‖ρ a‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = ‖a‖^2 * ‖b‖ := by simp only [ρ.norm_map]; ring
end RepresentedBounds

/- This concrete target has dimension27, actual positive Hilbert metric,
   a unit, bilinear commutative product, and compatible cyclic trace. -/
abbrev Diagonal27 := EuclideanSpace ℝ (Fin 27)

def nativeToDiagonal : Glennie.Albert ≃ₗᵢ[ℝ] Diagonal27 :=
  ((stdOrthonormalBasis ℝ Glennie.Albert).reindex (finCongr Glennie.albert_finrank)).repr

def diagonalProduct (a b : Diagonal27) : Diagonal27 :=
  WithLp.toLp 2 (fun i => a i * b i)

def diagonalUnit : Diagonal27 := WithLp.toLp 2 (fun _ => 1)

def diagonalRepresentation : Diagonal27 →ₗ[ℝ] (Fin 27 → ℝ) where
  toFun a := fun i => a i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def diagonalTrace : (Fin 27 → ℝ) →ₗ[ℝ] ℝ where
  toFun a := ∑ i, a i
  map_add' a b := Finset.sum_add_distrib
  map_smul' r a := by simp [Finset.mul_sum]

theorem diagonal_product_map (a b : Diagonal27) :
    diagonalRepresentation (diagonalProduct a b) =
      symmProd (diagonalRepresentation a) (diagonalRepresentation b) := by
  funext i
  change a i * b i = (1/2:ℝ) * (a i * b i + b i * a i)
  ring

theorem diagonal_metric_compatible (a b : Diagonal27) :
    Inner.inner ℝ a b =
      diagonalTrace (diagonalRepresentation a * diagonalRepresentation b) := by
  change (∑ i, b i * a i) = ∑ i, a i * b i
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem diagonal_trace_cyclic (a b : Fin 27 → ℝ) :
    diagonalTrace (a*b) = diagonalTrace (b*a) := by rw [mul_comm]

theorem diagonal_phi_zero (x y z : Diagonal27) :
    phiWith diagonalProduct (Inner.inner ℝ) x y z = 0 :=
  phiWith_eq_zero_of_compatible_trace diagonalProduct (Inner.inner ℝ)
    diagonalRepresentation diagonalTrace diagonal_product_map
    diagonal_metric_compatible diagonal_trace_cyclic x y z

theorem diagonal_product_norm (a b : Diagonal27) :
    ‖diagonalProduct a b‖ ≤ ‖a‖ * ‖b‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, EuclideanSpace.real_norm_sq_eq (diagonalProduct a b),
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

theorem diagonal_quadratic_sandwich (a b : Diagonal27) :
    quadraticWith diagonalProduct a b = diagonalProduct a (diagonalProduct a b) := by
  ext i
  change 2*(a i*(a i*b i)) - (a i*a i)*b i = a i*(a i*b i)
  ring

theorem diagonal_quadratic_norm (a b : Diagonal27) :
    ‖quadraticWith diagonalProduct a b‖ ≤ ‖a‖^2 * ‖b‖ := by
  rw [diagonal_quadratic_sandwich]
  calc
    ‖diagonalProduct a (diagonalProduct a b)‖ ≤ ‖a‖ * ‖diagonalProduct a b‖ :=
      diagonal_product_norm _ _
    _ ≤ ‖a‖ * (‖a‖ * ‖b‖) :=
      mul_le_mul_of_nonneg_left (diagonal_product_norm _ _) (norm_nonneg _)
    _ = ‖a‖^2 * ‖b‖ := by ring

theorem diagonal_unit_left (a : Diagonal27) :
    diagonalProduct diagonalUnit a = a := by
  ext i
  exact one_mul (a i)

theorem diagonal_product_comm (a b : Diagonal27) :
    diagonalProduct a b = diagonalProduct b a := by
  ext i
  exact mul_comm (a i) (b i)

theorem diagonal_product_add_left (a b c : Diagonal27) :
    diagonalProduct (a+b) c = diagonalProduct a c + diagonalProduct b c := by
  ext i
  exact add_mul (a i) (b i) (c i)

theorem diagonal_product_smul_left (r : ℝ) (a b : Diagonal27) :
    diagonalProduct (r • a) b = r • diagonalProduct a b := by
  ext i
  exact mul_assoc r (a i) (b i)

end
end Glennie.Compact.NormCompatibleNullTargetR01
