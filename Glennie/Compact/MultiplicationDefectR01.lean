/- Explicit generic norm hypotheses, with no assumed Phi-null field. -/
module
public import Glennie.Compact.CyclicTraceNullR01
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Module

@[expose] public section
namespace Glennie.Compact.MultiplicationDefectR01
noncomputable section
open Glennie.Compact.CyclicTraceNullR01
set_option autoImplicit false

variable {A E : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev Product (V : Type*) [AddCommGroup V] [Module ℝ V] := V →ₗ[ℝ] V →ₗ[ℝ] V

def Q (j : Product A) (a b : A) : A := quadraticWith (fun u v => j u v) a b

def commutator (j : Product A) (x y z : A) : A :=
  Q j x (Q j y z) - Q j y (Q j x z)

def rightFactor (j : Product A) (x y z : A) : A := Q j z (j x y)

def response (j : Product A) (x y z : A) : ℝ :=
  phiWith (fun a b => j a b) (Inner.inner ℝ) x y z

/-- Linearity of the quadratic representation in its final argument. -/
theorem Q_sub (j : Product A) (a b c : A) : Q j a (b - c) = Q j a b - Q j a c := by
  simp only [Q, quadraticWith, map_sub]
  module

/-- A four-term triangle inequality, isolating the coefficients 2,2,1,1. -/
theorem norm_four (a b c d : E) :
    ‖(2 : ℝ) • a + (2 : ℝ) • b - c - d‖ ≤
      2 * ‖a‖ + 2 * ‖b‖ + ‖c‖ + ‖d‖ := by
  calc
    _ ≤ ‖(2 : ℝ) • a + (2 : ℝ) • b - c‖ + ‖d‖ := norm_sub_le _ _
    _ ≤ (‖(2 : ℝ) • a + (2 : ℝ) • b‖ + ‖c‖) + ‖d‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ ((‖(2 : ℝ) • a‖ + ‖(2 : ℝ) • b‖) + ‖c‖) + ‖d‖ :=
      add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
    _ = _ := by norm_num [norm_smul]

/-- Bilinear multiplication error propagates to U with coefficient six. -/
theorem quadratic_error
    (jA : Product A) (jE : Product E) (f : A →ₗᵢ[ℝ] E)
    (hA : ∀ a b, ‖jA a b‖ ≤ ‖a‖ * ‖b‖)
    (hE : ∀ a b, ‖jE a b‖ ≤ ‖a‖ * ‖b‖)
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hdef : ∀ a b, ‖f (jA a b) - jE (f a) (f b)‖ ≤ μ * ‖a‖ * ‖b‖)
    (a b : A) :
    ‖f (Q jA a b) - Q jE (f a) (f b)‖ ≤ 6 * μ * ‖a‖ ^ 2 * ‖b‖ := by
  let D : A → A → E := fun u v => f (jA u v) - jE (f u) (f v)
  have hD (u v : A) : ‖D u v‖ ≤ μ * ‖u‖ * ‖v‖ := hdef u v
  have hexpand : f (Q jA a b) - Q jE (f a) (f b) =
      (2 : ℝ) • D a (jA a b) + (2 : ℝ) • jE (f a) (D a b) -
        D (jA a a) b - jE (D a a) (f b) := by
    simp only [Q, quadraticWith, D, map_sub, map_smul, LinearMap.sub_apply]
    module
  have h₁ : ‖D a (jA a b)‖ ≤ μ * ‖a‖ ^ 2 * ‖b‖ := by
    calc
      _ ≤ μ * ‖a‖ * ‖jA a b‖ := hD _ _
      _ ≤ μ * ‖a‖ * (‖a‖ * ‖b‖) :=
        mul_le_mul_of_nonneg_left (hA a b) (mul_nonneg hμ (norm_nonneg a))
      _ = _ := by ring
  have h₂ : ‖jE (f a) (D a b)‖ ≤ μ * ‖a‖ ^ 2 * ‖b‖ := by
    calc
      _ ≤ ‖f a‖ * ‖D a b‖ := hE _ _
      _ = ‖a‖ * ‖D a b‖ := by rw [f.norm_map]
      _ ≤ ‖a‖ * (μ * ‖a‖ * ‖b‖) :=
        mul_le_mul_of_nonneg_left (hD a b) (norm_nonneg a)
      _ = _ := by ring
  have h₃ : ‖D (jA a a) b‖ ≤ μ * ‖a‖ ^ 2 * ‖b‖ := by
    calc
      _ ≤ μ * ‖jA a a‖ * ‖b‖ := hD _ _
      _ ≤ μ * (‖a‖ * ‖a‖) * ‖b‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hA a a) hμ)
          (norm_nonneg b)
      _ = _ := by ring
  have h₄ : ‖jE (D a a) (f b)‖ ≤ μ * ‖a‖ ^ 2 * ‖b‖ := by
    calc
      _ ≤ ‖D a a‖ * ‖f b‖ := hE _ _
      _ = ‖D a a‖ * ‖b‖ := by rw [f.norm_map]
      _ ≤ (μ * ‖a‖ * ‖a‖) * ‖b‖ :=
        mul_le_mul_of_nonneg_right (hD a a) (norm_nonneg b)
      _ = _ := by ring
  rw [hexpand]
  calc
    _ ≤ 2 * ‖D a (jA a b)‖ + 2 * ‖jE (f a) (D a b)‖ +
        ‖D (jA a a) b‖ + ‖jE (D a a) (f b)‖ := norm_four _ _ _ _
    _ ≤ 2 * (μ * ‖a‖ ^ 2 * ‖b‖) + 2 * (μ * ‖a‖ ^ 2 * ‖b‖) +
        (μ * ‖a‖ ^ 2 * ‖b‖) + (μ * ‖a‖ ^ 2 * ‖b‖) := by
      exact add_le_add (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left h₁ (by norm_num))
        (mul_le_mul_of_nonneg_left h₂ (by norm_num))) h₃) h₄
    _ = _ := by ring

/-- One composed quadratic word has transport error twelve. -/
theorem nested_error
    (jA : Product A) (jE : Product E) (f : A →ₗᵢ[ℝ] E)
    (hUA : ∀ a b, ‖Q jA a b‖ ≤ ‖a‖ ^ 2 * ‖b‖)
    (hUE : ∀ a b, ‖Q jE a b‖ ≤ ‖a‖ ^ 2 * ‖b‖)
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hQ : ∀ a b, ‖f (Q jA a b) - Q jE (f a) (f b)‖ ≤
      6 * μ * ‖a‖ ^ 2 * ‖b‖) (x y z : A) :
    ‖f (Q jA x (Q jA y z)) - Q jE (f x) (Q jE (f y) (f z))‖ ≤
      12 * μ * ‖x‖ ^ 2 * ‖y‖ ^ 2 * ‖z‖ := by
  have heq : f (Q jA x (Q jA y z)) - Q jE (f x) (Q jE (f y) (f z)) =
      (f (Q jA x (Q jA y z)) - Q jE (f x) (f (Q jA y z))) +
      Q jE (f x) (f (Q jA y z) - Q jE (f y) (f z)) := by
    rw [Q_sub]
    module
  have h₁ : ‖f (Q jA x (Q jA y z)) - Q jE (f x) (f (Q jA y z))‖ ≤
      6 * μ * ‖x‖ ^ 2 * ‖y‖ ^ 2 * ‖z‖ := by
    calc
      _ ≤ 6 * μ * ‖x‖ ^ 2 * ‖Q jA y z‖ := hQ x (Q jA y z)
      _ ≤ 6 * μ * ‖x‖ ^ 2 * (‖y‖ ^ 2 * ‖z‖) :=
        mul_le_mul_of_nonneg_left (hUA y z) (by positivity)
      _ = _ := by ring
  have h₂ : ‖Q jE (f x) (f (Q jA y z) - Q jE (f y) (f z))‖ ≤
      6 * μ * ‖x‖ ^ 2 * ‖y‖ ^ 2 * ‖z‖ := by
    calc
      _ ≤ ‖f x‖ ^ 2 * ‖f (Q jA y z) - Q jE (f y) (f z)‖ := hUE _ _
      _ = ‖x‖ ^ 2 * ‖f (Q jA y z) - Q jE (f y) (f z)‖ := by rw [f.norm_map]
      _ ≤ ‖x‖ ^ 2 * (6 * μ * ‖y‖ ^ 2 * ‖z‖) :=
        mul_le_mul_of_nonneg_left (hQ y z) (sq_nonneg _)
      _ = _ := by ring
  rw [heq]
  calc
    _ ≤ ‖f (Q jA x (Q jA y z)) - Q jE (f x) (f (Q jA y z))‖ +
      ‖Q jE (f x) (f (Q jA y z) - Q jE (f y) (f z))‖ := norm_add_le _ _
    _ ≤ (6 * μ * ‖x‖ ^ 2 * ‖y‖ ^ 2 * ‖z‖) +
      (6 * μ * ‖x‖ ^ 2 * ‖y‖ ^ 2 * ‖z‖) := add_le_add h₁ h₂
    _ = _ := by ring

/-- Difference of the two composed words has transport error twenty-four. -/
theorem commutator_error
    (jA : Product A) (jE : Product E) (f : A →ₗᵢ[ℝ] E)
    (hUA : ∀ a b, ‖Q jA a b‖ ≤ ‖a‖ ^ 2 * ‖b‖)
    (hUE : ∀ a b, ‖Q jE a b‖ ≤ ‖a‖ ^ 2 * ‖b‖)
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hQ : ∀ a b, ‖f (Q jA a b) - Q jE (f a) (f b)‖ ≤
      6 * μ * ‖a‖ ^ 2 * ‖b‖) (x y z : A) :
    ‖f (commutator jA x y z) - commutator jE (f x) (f y) (f z)‖ ≤
      24 * μ * ‖x‖ ^ 2 * ‖y‖ ^ 2 * ‖z‖ := by
  have heq : f (commutator jA x y z) - commutator jE (f x) (f y) (f z) =
      (f (Q jA x (Q jA y z)) - Q jE (f x) (Q jE (f y) (f z))) -
      (f (Q jA y (Q jA x z)) - Q jE (f y) (Q jE (f x) (f z))) := by
    simp only [commutator, map_sub]
    module
  rw [heq]
  calc
    _ ≤ ‖f (Q jA x (Q jA y z)) - Q jE (f x) (Q jE (f y) (f z))‖ +
        ‖f (Q jA y (Q jA x z)) - Q jE (f y) (Q jE (f x) (f z))‖ := norm_sub_le _ _
    _ ≤ (12 * μ * ‖x‖ ^ 2 * ‖y‖ ^ 2 * ‖z‖) +
        (12 * μ * ‖y‖ ^ 2 * ‖x‖ ^ 2 * ‖z‖) :=
      add_le_add (nested_error jA jE f hUA hUE μ hμ hQ x y z)
        (nested_error jA jE f hUA hUE μ hμ hQ y x z)
    _ = _ := by ring

/-- The final U/product factor has transport error seven. -/
theorem rightFactor_error
    (jA : Product A) (jE : Product E) (f : A →ₗᵢ[ℝ] E)
    (hA : ∀ a b, ‖jA a b‖ ≤ ‖a‖ * ‖b‖)
    (hUE : ∀ a b, ‖Q jE a b‖ ≤ ‖a‖ ^ 2 * ‖b‖)
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hdef : ∀ a b, ‖f (jA a b) - jE (f a) (f b)‖ ≤ μ * ‖a‖ * ‖b‖)
    (hQ : ∀ a b, ‖f (Q jA a b) - Q jE (f a) (f b)‖ ≤
      6 * μ * ‖a‖ ^ 2 * ‖b‖) (x y z : A) :
    ‖f (rightFactor jA x y z) - rightFactor jE (f x) (f y) (f z)‖ ≤
      7 * μ * ‖z‖ ^ 2 * ‖x‖ * ‖y‖ := by
  have heq : f (rightFactor jA x y z) - rightFactor jE (f x) (f y) (f z) =
      (f (Q jA z (jA x y)) - Q jE (f z) (f (jA x y))) +
      Q jE (f z) (f (jA x y) - jE (f x) (f y)) := by
    simp only [rightFactor, Q_sub]
    module
  have h₁ : ‖f (Q jA z (jA x y)) - Q jE (f z) (f (jA x y))‖ ≤
      6 * μ * ‖z‖ ^ 2 * ‖x‖ * ‖y‖ := by
    calc
      _ ≤ 6 * μ * ‖z‖ ^ 2 * ‖jA x y‖ := hQ _ _
      _ ≤ 6 * μ * ‖z‖ ^ 2 * (‖x‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_left (hA x y) (by positivity)
      _ = _ := by ring
  have h₂ : ‖Q jE (f z) (f (jA x y) - jE (f x) (f y))‖ ≤
      μ * ‖z‖ ^ 2 * ‖x‖ * ‖y‖ := by
    calc
      _ ≤ ‖f z‖ ^ 2 * ‖f (jA x y) - jE (f x) (f y)‖ := hUE _ _
      _ = ‖z‖ ^ 2 * ‖f (jA x y) - jE (f x) (f y)‖ := by rw [f.norm_map]
      _ ≤ ‖z‖ ^ 2 * (μ * ‖x‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_left (hdef x y) (sq_nonneg _)
      _ = _ := by ring
  rw [heq]
  calc
    _ ≤ ‖f (Q jA z (jA x y)) - Q jE (f z) (f (jA x y))‖ +
      ‖Q jE (f z) (f (jA x y) - jE (f x) (f y))‖ := norm_add_le _ _
    _ ≤ (6 * μ * ‖z‖ ^ 2 * ‖x‖ * ‖y‖) +
      (μ * ‖z‖ ^ 2 * ‖x‖ * ‖y‖) := add_le_add h₁ h₂
    _ = _ := by ring

/-- Coefficient-one U bounds give a coefficient-two commutator bound. -/
theorem norm_commutator_le (j : Product A)
    (hU : ∀ a b, ‖Q j a b‖ ≤ ‖a‖ ^ 2 * ‖b‖) (x y z : A) :
    ‖commutator j x y z‖ ≤ 2 * ‖x‖ ^ 2 * ‖y‖ ^ 2 * ‖z‖ := by
  have hxy : ‖Q j x (Q j y z)‖ ≤ ‖x‖ ^ 2 * (‖y‖ ^ 2 * ‖z‖) :=
    (hU _ _).trans (mul_le_mul_of_nonneg_left (hU y z) (sq_nonneg _))
  have hyx : ‖Q j y (Q j x z)‖ ≤ ‖y‖ ^ 2 * (‖x‖ ^ 2 * ‖z‖) :=
    (hU _ _).trans (mul_le_mul_of_nonneg_left (hU x z) (sq_nonneg _))
  calc
    _ ≤ ‖Q j x (Q j y z)‖ + ‖Q j y (Q j x z)‖ := norm_sub_le _ _
    _ ≤ ‖x‖ ^ 2 * (‖y‖ ^ 2 * ‖z‖) + ‖y‖ ^ 2 * (‖x‖ ^ 2 * ‖z‖) :=
      add_le_add hxy hyx
    _ = _ := by ring

theorem norm_rightFactor_le (j : Product A)
    (hJ : ∀ a b, ‖j a b‖ ≤ ‖a‖ * ‖b‖)
    (hU : ∀ a b, ‖Q j a b‖ ≤ ‖a‖ ^ 2 * ‖b‖) (x y z : A) :
    ‖rightFactor j x y z‖ ≤ ‖z‖ ^ 2 * ‖x‖ * ‖y‖ := by
  calc
    _ ≤ ‖z‖ ^ 2 * ‖j x y‖ := hU _ _
    _ ≤ ‖z‖ ^ 2 * (‖x‖ * ‖y‖) :=
      mul_le_mul_of_nonneg_left (hJ x y) (sq_nonneg _)
    _ = _ := by ring

/-- Generic metric/product discrepancy; no target vanishing assumption.
The sharper anisotropic form also handles zero arguments without division. -/
theorem response_discrepancy
    (jA : Product A) (jE : Product E) (f : A →ₗᵢ[ℝ] E)
    (hA : ∀ a b, ‖jA a b‖ ≤ ‖a‖ * ‖b‖)
    (hE : ∀ a b, ‖jE a b‖ ≤ ‖a‖ * ‖b‖)
    (hUA : ∀ a b, ‖Q jA a b‖ ≤ ‖a‖ ^ 2 * ‖b‖)
    (hUE : ∀ a b, ‖Q jE a b‖ ≤ ‖a‖ ^ 2 * ‖b‖)
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hdef : ∀ a b, ‖f (jA a b) - jE (f a) (f b)‖ ≤ μ * ‖a‖ * ‖b‖)
    (x y z : A) :
    |response jA x y z - response jE (f x) (f y) (f z)| ≤
      38 * μ * ‖x‖ ^ 3 * ‖y‖ ^ 3 * ‖z‖ ^ 3 := by
  have hQ := quadratic_error jA jE f hA hE μ hμ hdef
  have hF := commutator_error jA jE f hUA hUE μ hμ hQ x y z
  have hH := rightFactor_error jA jE f hA hUE μ hμ hdef hQ x y z
  have hnH : ‖f (rightFactor jA x y z)‖ ≤ ‖z‖ ^ 2 * ‖x‖ * ‖y‖ := by
    rw [f.norm_map]
    exact norm_rightFactor_le jA hA hUA x y z
  have hnF : ‖commutator jE (f x) (f y) (f z)‖ ≤
      2 * ‖x‖ ^ 2 * ‖y‖ ^ 2 * ‖z‖ := by
    simpa only [f.norm_map] using norm_commutator_le jE hUE (f x) (f y) (f z)
  have heq : response jA x y z - response jE (f x) (f y) (f z) =
      Inner.inner ℝ (f (commutator jA x y z) - commutator jE (f x) (f y) (f z))
        (f (rightFactor jA x y z)) +
      Inner.inner ℝ (commutator jE (f x) (f y) (f z))
        (f (rightFactor jA x y z) - rightFactor jE (f x) (f y) (f z)) := by
    change Inner.inner ℝ (commutator jA x y z) (rightFactor jA x y z) -
      Inner.inner ℝ (commutator jE (f x) (f y) (f z)) (rightFactor jE (f x) (f y) (f z)) = _
    rw [← f.inner_map_map (commutator jA x y z) (rightFactor jA x y z)]
    rw [_root_.inner_sub_left, _root_.inner_sub_right]
    ring
  rw [heq]
  calc
    _ ≤ |Inner.inner ℝ (f (commutator jA x y z) - commutator jE (f x) (f y) (f z))
          (f (rightFactor jA x y z))| +
        |Inner.inner ℝ (commutator jE (f x) (f y) (f z))
          (f (rightFactor jA x y z) - rightFactor jE (f x) (f y) (f z))| := abs_add_le _ _
    _ ≤ ‖f (commutator jA x y z) - commutator jE (f x) (f y) (f z)‖ *
          ‖f (rightFactor jA x y z)‖ +
        ‖commutator jE (f x) (f y) (f z)‖ *
          ‖f (rightFactor jA x y z) - rightFactor jE (f x) (f y) (f z)‖ :=
      add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ (24 * μ * ‖x‖ ^ 2 * ‖y‖ ^ 2 * ‖z‖) * (‖z‖ ^ 2 * ‖x‖ * ‖y‖) +
        (2 * ‖x‖ ^ 2 * ‖y‖ ^ 2 * ‖z‖) * (7 * μ * ‖z‖ ^ 2 * ‖x‖ * ‖y‖) :=
      add_le_add (mul_le_mul hF hnH (norm_nonneg _) (by positivity))
        (mul_le_mul hnF hH (norm_nonneg _) (by positivity))
    _ = _ := by ring

/-- Radius-ball form, with radius power nine and no smallness restriction on μ. -/
theorem response_discrepancy_radius
    (jA : Product A) (jE : Product E) (f : A →ₗᵢ[ℝ] E)
    (hA : ∀ a b, ‖jA a b‖ ≤ ‖a‖ * ‖b‖)
    (hE : ∀ a b, ‖jE a b‖ ≤ ‖a‖ * ‖b‖)
    (hUA : ∀ a b, ‖Q jA a b‖ ≤ ‖a‖ ^ 2 * ‖b‖)
    (hUE : ∀ a b, ‖Q jE a b‖ ≤ ‖a‖ ^ 2 * ‖b‖)
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hdef : ∀ a b, ‖f (jA a b) - jE (f a) (f b)‖ ≤ μ * ‖a‖ * ‖b‖)
    (R : ℝ) (hR : 0 ≤ R) (x y z : A)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
    |response jA x y z - response jE (f x) (f y) (f z)| ≤ 38 * μ * R ^ 9 := by
  calc
    _ ≤ 38 * μ * ‖x‖ ^ 3 * ‖y‖ ^ 3 * ‖z‖ ^ 3 :=
      response_discrepancy jA jE f hA hE hUA hUE μ hμ hdef x y z
    _ ≤ 38 * μ * R ^ 3 * R ^ 3 * R ^ 3 := by gcongr
    _ = _ := by ring

/-- Compatible cyclic-trace specialization. Nullness is produced by the existing
explicit associative representation theorem, rather than assumed as a field.
Generic norm hypotheses remain visible until concrete native/target producers apply. -/
theorem response_bound_of_compatible_trace
    {M : Type*} [Ring M] [Algebra ℝ M]
    (jA : Product A) (jE : Product E) (f : A →ₗᵢ[ℝ] E)
    (hA : ∀ a b, ‖jA a b‖ ≤ ‖a‖ * ‖b‖)
    (hE : ∀ a b, ‖jE a b‖ ≤ ‖a‖ * ‖b‖)
    (hUA : ∀ a b, ‖Q jA a b‖ ≤ ‖a‖ ^ 2 * ‖b‖)
    (hUE : ∀ a b, ‖Q jE a b‖ ≤ ‖a‖ ^ 2 * ‖b‖)
    (ρ : E →ₗ[ℝ] M) (τ : M →ₗ[ℝ] ℝ)
    (hj : ∀ a b, ρ (jE a b) = symmProd (ρ a) (ρ b))
    (hB : ∀ a b, Inner.inner ℝ a b = τ (ρ a * ρ b))
    (hcyclic : ∀ a b : M, τ (a * b) = τ (b * a))
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hdef : ∀ a b, ‖f (jA a b) - jE (f a) (f b)‖ ≤ μ * ‖a‖ * ‖b‖)
    (R : ℝ) (hR : 0 ≤ R) (x y z : A)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
    |response jA x y z| ≤ 38 * μ * R ^ 9 := by
  have hnull : response jE (f x) (f y) (f z) = 0 :=
    phiWith_eq_zero_of_compatible_trace (fun a b => jE a b) (Inner.inner ℝ) ρ τ hj hB hcyclic
      (f x) (f y) (f z)
  have h := response_discrepancy_radius jA jE f hA hE hUA hUE μ hμ hdef R hR x y z hx hy hz
  simpa only [hnull, sub_zero] using h

end
end Glennie.Compact.MultiplicationDefectR01
