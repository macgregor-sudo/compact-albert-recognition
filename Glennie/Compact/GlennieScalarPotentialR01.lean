/- Native scalar contraction of the retained degree-eight Glennie vector.
All exposition and Lean code are AI-generated under Robert MacGregor's direction.
No novelty is asserted.
-/
module
public import Glennie.Compact.OperationalPhi

@[expose] public section
namespace Glennie.Compact.GlennieScalarPotentialR01
open Glennie
open Glennie.Compact.OperationalPhi
noncomputable section
set_option autoImplicit false

/-- The commutator of the two native quadratic operators, applied to z. -/
def commU (x y z : Albert) : Albert := U x (U y z) - U y (U x z)

/-- The unhalved Jordan triple product. The name uses the factor-two
convention; it does not double the element `jordan x y` used below. -/
def doubledTriple (a z b : Albert) : Albert :=
  (2 : ℝ) • (jordan a (jordan z b) + jordan (jordan a z) b - jordan (jordan a b) z)

/-- Native/introductory G8, with p = x circle y and the unhalved triple product. -/
def glennieVector (x y z : Albert) : Albert :=
  doubledTriple (commU x y z) z (jordan x y) - commU x y (U z (jordan x y))

/-- The commutator of the self-adjoint U operators is skew-adjoint for raw B. -/
theorem commU_pairing (x y a b : Albert) :
    inner (commU x y a) b = -inner a (commU x y b) := by
  simp only [commU, inner_sub_left, inner_sub_right, ← U_pairing_selfadjoint]
  ring

/-- Contracting the unhalved triple against its middle argument gives 2 U. -/
theorem doubledTriple_pairing (a z b : Albert) :
    inner (doubledTriple a z b) z = 2 * inner a (U z b) := by
  have h1 : inner (jordan a (jordan z b)) z =
      inner a (jordan z (jordan z b)) := by
    rw [inner_jordan_associative, jordan_comm (jordan z b) z]
  have h2 : inner (jordan (jordan a z) b) z =
      inner a (jordan z (jordan z b)) := by
    rw [inner_jordan_associative, inner_jordan_associative, jordan_comm b z]
  have h3 : inner (jordan (jordan a b) z) z =
      inner a (jordan (jordan z z) b) := by
    rw [inner_jordan_associative, inner_jordan_associative,
      jordan_comm b (jordan z z)]
  simp only [doubledTriple, inner_smul_left, inner_sub_left, inner_add_left,
    h1, h2, h3, U, inner_sub_right, inner_smul_right]
  ring

/-- Native G8 contracts to three times the retained scalar Phi, for all inputs. -/
theorem glennieVector_pairing (x y z : Albert) :
    inner (glennieVector x y z) z = 3 * phi x y z := by
  rw [glennieVector, inner_sub_left, doubledTriple_pairing,
    commU_pairing x y (U z (jordan x y)) z,
    inner_comm (U z (jordan x y)) (commU x y z)]
  change 2 * phi x y z - -phi x y z = 3 * phi x y z
  ring

/-- Pointwise vanishing of the vector implies vanishing of its scalar contraction. -/
theorem phi_eq_zero_of_glennieVector_eq_zero (x y z : Albert)
    (h : glennieVector x y z = 0) : phi x y z = 0 := by
  have hp := glennieVector_pairing x y z
  rw [h, inner_zero_left] at hp
  exact (mul_eq_zero.mp hp.symm).resolve_left (by norm_num)

/-- A nonzero scalar is a sufficient certificate that native G8 is nonzero. -/
theorem glennieVector_ne_zero_of_phi_ne_zero (x y z : Albert)
    (h : phi x y z ≠ 0) : glennieVector x y z ≠ 0 := by
  intro hz
  exact h (phi_eq_zero_of_glennieVector_eq_zero x y z hz)

end
end Glennie.Compact.GlennieScalarPotentialR01
