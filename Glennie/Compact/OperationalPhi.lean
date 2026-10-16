module

public import Glennie.BasicLaws

/- Pure native algebra only. No positivity,
probability interpretation, normalization of effects, or operational framework
is asserted. All products and pairings are the existing Glennie definitions.
-/
@[expose] public section
namespace Glennie.Compact.OperationalPhi
open Glennie
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The swapped-order contrast, with an arbitrary unnormalized final argument. -/
def contrast (x y z v : Albert) : ℝ :=
  inner z (U y (U x (U z v)) - U x (U y (U z v)))

/-- The amplitude h=(1+x)/2, expressed with real scalar multiplication. -/
def halfAmplitude (x : Albert) : Albert := (1 / 2 : ℝ) • ((1 : Albert) + x)

/-- The history difference Delta_a with arbitrary input rho. -/
def delta (x y z a rho : Albert) : ℝ := contrast x y z (U a rho)

theorem jordan_pairing_selfadjoint (x a b : Albert) :
    inner a (jordan x b) = inner (jordan x a) b := by
  rw [← inner_jordan_associative, jordan_comm a x]

/-- Self-adjointness is derived from the native associative pairing. -/
theorem U_pairing_selfadjoint (x a b : Albert) :
    inner a (U x b) = inner (U x a) b := by
  simp only [U, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, jordan_pairing_selfadjoint]

theorem contrast_add (x y z u v : Albert) :
    contrast x y z (u + v) = contrast x y z u + contrast x y z v := by
  simp only [contrast, U_add_argument, inner_sub_right, inner_add_right]
  ring

theorem contrast_sub (x y z u v : Albert) :
    contrast x y z (u - v) = contrast x y z u - contrast x y z v := by
  simp only [contrast, U_sub_argument, inner_sub_right]
  ring

theorem contrast_smul (x y z v : Albert) (r : ℝ) :
    contrast x y z (r • v) = r * contrast x y z v := by
  simp only [contrast, U_smul_argument, inner_sub_right, inner_smul_right]
  ring

/-- Reversing the commutator across the pairing fixes the contrast sign. -/
theorem phi_eq_contrast (x y z : Albert) :
    phi x y z = contrast x y z (jordan x y) := by
  simp only [phi, contrast, inner_sub_left, inner_sub_right,
    ← U_pairing_selfadjoint]

theorem U_one (w : Albert) : U (1 : Albert) w = w := by
  simp only [U, jordan_unit_left]
  module

theorem crossU_one (x w : Albert) : crossU (1 : Albert) x w = (2 : ℝ) • jordan x w := by
  simp only [crossU, jordan_unit_left]
  module

/-- The required 4U_h-U_x-U_1=2L_x identity, with no spectral hypotheses. -/
theorem four_U_halfAmplitude (x w : Albert) :
    (4 : ℝ) • U (halfAmplitude x) w - U x w - U (1 : Albert) w =
      (2 : ℝ) • jordan x w := by
  rw [halfAmplitude, U_smul_base, U_add_base, U_one, crossU_one]
  module

/-- Division-free six-term identity with the original y as input. -/
theorem phi_division_free (x y z : Albert) :
    4 * delta x y z (halfAmplitude x) y - delta x y z x y - delta x y z 1 y =
      2 * phi x y z := by
  have h := congrArg (contrast x y z) (four_U_halfAmplitude x y)
  simp only [contrast_sub, contrast_smul, ← phi_eq_contrast] at h
  exact h

/-- Algebraic six-history identity for rho=y/tr(y), requiring only nonzero trace. -/
theorem phi_six_contrasts (x y z : Albert) (hy : trace y ≠ 0) :
    phi x y z = trace y / 2 *
      (4 * delta x y z (halfAmplitude x) ((trace y)⁻¹ • y) -
        delta x y z x ((trace y)⁻¹ • y) -
        delta x y z 1 ((trace y)⁻¹ • y)) := by
  simp only [delta, U_smul_argument, contrast_smul]
  have h := phi_division_free x y z
  change 4 * contrast x y z (U (halfAmplitude x) y) -
    contrast x y z (U x y) - contrast x y z (U 1 y) = 2 * phi x y z at h
  have hs : (trace y / 2 * (trace y)⁻¹) * 2 = 1 := by
    calc
      (trace y / 2 * (trace y)⁻¹) * 2 = trace y * (trace y)⁻¹ := by ring
      _ = 1 := mul_inv_cancel₀ hy
  calc
    phi x y z = 1 * phi x y z := by ring
    _ = ((trace y / 2 * (trace y)⁻¹) * 2) * phi x y z := by rw [hs]
    _ = (trace y / 2 * (trace y)⁻¹) * (2 * phi x y z) := by ring
    _ = (trace y / 2 * (trace y)⁻¹) *
        (4 * contrast x y z (U (halfAmplitude x) y) -
          contrast x y z (U x y) - contrast x y z (U 1 y)) := by rw [h]
    _ = _ := by ring

end
end Glennie.Compact.OperationalPhi
