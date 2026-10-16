/- Elementary consequences of the native compact coordinates. -/
module
public import Glennie.Native.AlgebraLaws
public import Mathlib.Tactic.Abel

@[expose] public section
namespace Glennie
noncomputable section

@[simp] theorem trace_zero : trace (0 : Albert) = 0 := by simp [trace]

@[simp] theorem inner_zero_left (x : Albert) : inner 0 x = 0 := by simp [inner]
@[simp] theorem inner_zero_right (x : Albert) : inner x 0 = 0 := by simp [inner]
@[simp] theorem inner_unit_left (x : Albert) : inner 1 x = trace x := by simp [inner]
@[simp] theorem inner_unit_right (x : Albert) : inner x 1 = trace x := by simp [inner]

theorem U_smul_argument (a : ℝ) (x z : Albert) : U x (a • z) = a • U x z := by
  simp only [U, jordan_smul_right, smul_sub, smul_smul]
  congr 1
  rw [mul_comm]

theorem U_smul_base (a : ℝ) (x z : Albert) : U (a • x) z = a^2 • U x z := by
  simp only [U, jordan_smul_left, jordan_smul_right, smul_smul, smul_sub]
  congr 1 <;> congr 1 <;> ring

theorem U_sub_argument (x y z : Albert) : U x (y-z) = U x y - U x z := by
  simp only [U, jordan_sub_right, smul_sub]
  abel

theorem U_add_argument (x y z : Albert) : U x (y+z) = U x y + U x z := by
  simp only [U, jordan_add_right, smul_add]
  abel

/-- The cross term in the quadratic base variable of U. -/
def crossU (x y z : Albert) : Albert :=
  (2 : ℝ) • (jordan x (jordan y z) + jordan y (jordan x z) -
    jordan (jordan x y) z)

theorem U_add_base (x y z : Albert) :
    U (x+y) z = U x z + U y z + crossU x y z := by
  simp only [U, crossU, jordan_add_left, jordan_add_right]
  rw [jordan_comm y x]
  module

theorem crossU_smul_second (t : ℝ) (x y z : Albert) :
    crossU x (t • y) z = t • crossU x y z := by
  simp only [crossU, jordan_smul_left, jordan_smul_right]
  module

theorem U_line (x y z : Albert) (t : ℝ) :
    U (x + t • y) z = U x z + t • crossU x y z + t^2 • U y z := by
  rw [U_add_base, U_smul_base, crossU_smul_second]
  abel

/-- Exact cubic restriction in the first input, with native coefficients. -/
theorem phi_line_first (x y z w : Albert) (t : ℝ) :
    phi (x + t • z) y w =
      phi x y w +
      t * (inner (crossU x z (U y w) - U y (crossU x z w)) (U w (jordan x y)) +
        inner (U x (U y w) - U y (U x w)) (U w (jordan z y))) +
      t^2 * (inner (U z (U y w) - U y (U z w)) (U w (jordan x y)) +
        inner (crossU x z (U y w) - U y (crossU x z w)) (U w (jordan z y))) +
      t^3 * phi z y w := by
  simp only [phi, U_line, jordan_add_left, jordan_smul_left, U_add_argument,
    U_smul_argument, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, inner_smul_left, inner_smul_right]
  ring

theorem phi_smul_first (a : ℝ) (x y z : Albert) :
    phi (a • x) y z = a^3 * phi x y z := by
  simp only [phi, U_smul_base, U_smul_argument, ← smul_sub,
    jordan_smul_left, inner_smul_left, inner_smul_right]
  ring

theorem phi_smul_second (a : ℝ) (x y z : Albert) :
    phi x (a • y) z = a^3 * phi x y z := by
  simp only [phi, U_smul_base, U_smul_argument, ← smul_sub,
    jordan_smul_right, inner_smul_left, inner_smul_right]
  ring

theorem phi_smul_third (a : ℝ) (x y z : Albert) :
    phi x y (a • z) = a^3 * phi x y z := by
  simp only [phi, U_smul_base, U_smul_argument, ← smul_sub,
    inner_smul_left, inner_smul_right]
  ring

theorem phi_swap_first_two (x y z : Albert) : phi y x z = -phi x y z := by
  rw [phi, phi, jordan_comm y x, inner_sub_left, inner_sub_left]
  ring

@[simp] theorem phi_repeated_first_two (x z : Albert) : phi x x z = 0 := by
  simp [phi]

end
end Glennie
