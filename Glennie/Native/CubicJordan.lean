/-
Adapted from AlbertLean/CubicJordan.lean in albert-lean-public-clean at
dd06ef5d423a0e4a5d814d2c221e999b98887ee1, source SHA256
cc885b590ac2317fbde15b490d8205d684fafbf7dbe4ffd883155275a0986826.
The upstream repository is licensed under Apache-2.0. See THIRD-PARTY-NOTICES.
The adaptation changes the scalar field from ℚ to ℝ and the module API.
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Module

@[expose] public section

namespace Glennie.CubicJordan

noncomputable section

set_option maxHeartbeats 2000000

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Six times the cubic characteristic identity, with Newton coefficients. -/
def residual (mul : V →ₗ[ℝ] V →ₗ[ℝ] V) (T : V →ₗ[ℝ] ℝ) (e x : V) : V :=
  (6 : ℝ) • mul x (mul x x) - (6 * T x) • mul x x +
    (3 * (T x) ^ 2 - 3 * T (mul x x)) • x -
    ((T x) ^ 3 - 3 * T x * T (mul x x) + 2 * T (mul x (mul x x))) • e

/-- Twice the coefficient of the linear perturbation in the cubic identity. -/
def linearResidual (mul : V →ₗ[ℝ] V →ₗ[ℝ] V)
    (T : V →ₗ[ℝ] ℝ) (e x y : V) : V :=
  (4 : ℝ) • mul x (mul x y) + (2 : ℝ) • mul (mul x x) y -
    (2 * T y) • mul x x - (4 * T x) • mul x y +
    (2 * T x * T y - 2 * T (mul x y)) • x +
    ((T x) ^ 2 - T (mul x x)) • y -
    (((T x) ^ 2 - T (mul x x)) * T y -
      2 * T x * T (mul x y) + 2 * T (mul (mul x x) y)) • e

theorem linearResidual_eq_zero
    (mul : V →ₗ[ℝ] V →ₗ[ℝ] V) (T : V →ₗ[ℝ] ℝ) (e : V)
    (comm : ∀ x y, mul x y = mul y x)
    (assocTrace : ∀ x y z, T (mul (mul x y) z) = T (mul x (mul y z)))
    (char : ∀ x, residual mul T e x = 0) (x y : V) :
    linearResidual mul T e x y = 0 := by
  calc
    linearResidual mul T e x y = (1 / 6 : ℝ) •
        (residual mul T e (x + y) - residual mul T e (x - y) -
          (2 : ℝ) • residual mul T e y) := by
      simp only [linearResidual, residual, map_add, map_sub, map_smul,
        LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        smul_eq_mul]
      simp only [comm y x, comm y (mul x x), ← assocTrace x x y]
      module
    _ = 0 := by rw [char, char, char]; simp

/-- Concrete commutativity, unit, trace associativity and Newton residual imply Jordan. -/
theorem jordan_of_cubic_trace_identity
    (mul : V →ₗ[ℝ] V →ₗ[ℝ] V) (T : V →ₗ[ℝ] ℝ) (e : V)
    (comm : ∀ x y, mul x y = mul y x)
    (unit : ∀ x, mul e x = x)
    (assocTrace : ∀ x y z, T (mul (mul x y) z) = T (mul x (mul y z)))
    (char : ∀ x, residual mul T e x = 0) (x y : V) :
    mul (mul x y) (mul x x) = mul x (mul y (mul x x)) := by
  have unitR (z : V) : mul z e = z := by rw [comm, unit]
  have hB₁ : T (mul x (mul x y)) = T (mul (mul x x) y) :=
    (assocTrace x x y).symm
  have hB₂ : T (mul (mul x x) (mul x y)) =
      T (mul (mul x (mul x x)) y) := by
    rw [← assocTrace, comm (mul x x) x]
  have hlin := linearResidual_eq_zero mul T e comm assocTrace char
  have hj : mul (mul x x) (mul x y) - mul x (mul (mul x x) y) = 0 := by
    calc
      mul (mul x x) (mul x y) - mul x (mul (mul x x) y) =
          (-1 / 2 : ℝ) •
            (mul x (linearResidual mul T e x y) -
              linearResidual mul T e x (mul x y)) -
          (T y / 6) • residual mul T e x +
          ((1 / 6 : ℝ) * T (mul (residual mul T e x) y)) • e := by
        simp only [linearResidual, residual, map_add, map_sub, map_smul,
          LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
          smul_eq_mul, unit, unitR, hB₁, hB₂]
        module
      _ = 0 := by rw [hlin, hlin, char]; simp
  have heq := sub_eq_zero.mp hj
  simpa only [comm (mul x y) (mul x x), comm y (mul x x)] using heq

end
end Glennie.CubicJordan
