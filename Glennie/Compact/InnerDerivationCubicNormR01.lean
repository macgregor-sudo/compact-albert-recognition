/- Native inner-derivation identity for the raw cubic norm.
All exposition and Lean code are AI-generated under Robert MacGregor's direction.
No novelty is asserted.

Conventions: D = innerDer x y = [L_x,L_y], without an additional factor of four;
inner is the native raw trace pairing, and newtonCubicNorm is the existing native
Newton norm. No frame, classification, invariant-ring or certificate premise is used.
-/
module
public import Glennie.Compact.InnerDerivation
public import Glennie.Compact.OperationalPhi
public import Glennie.Compact.WordNormIdentity
public import Mathlib.Tactic.Linarith

@[expose] public section
namespace Glennie.Compact.InnerDerivationCubicNormR01
open Glennie
open Glennie.Compact.OperationalPhi
noncomputable section
set_option autoImplicit false

/-- The native commutator of two Jordan multiplication operators is B-skew.
This follows from native trace adjunction and does not assume skew-adjointness. -/
theorem innerDer_pairing (x y a b : Albert) :
    inner (innerDer x y a) b = -inner a (innerDer x y b) := by
  simp only [innerDer, inner_sub_left, inner_sub_right,
    ← jordan_pairing_selfadjoint]
  ring

/-- Leibniz on a square, in the native half-Jordan product convention. -/
theorem innerDer_square (x y z : Albert) :
    innerDer x y (jordan z z) = (2 : ℝ) • jordan z (innerDer x y z) := by
  rw [innerDer_jordan x y z z, jordan_comm (innerDer x y z) z]
  module

/-- Write u = Dz and v = D²z. Moving D from v and expanding D(z circle u)
gives 2 B(v,z circle u) = -B(u,u circle u). -/
theorem innerDer_second_pairing_product (x y z : Albert) :
    2 * inner (innerDer x y (innerDer x y z)) (jordan z (innerDer x y z)) =
      -inner (innerDer x y z) (jordan (innerDer x y z) (innerDer x y z)) := by
  have hcross :
      inner (innerDer x y z) (jordan z (innerDer x y (innerDer x y z))) =
        inner (innerDer x y (innerDer x y z)) (jordan z (innerDer x y z)) := by
    calc
      inner (innerDer x y z) (jordan z (innerDer x y (innerDer x y z))) =
          inner (jordan z (innerDer x y z)) (innerDer x y (innerDer x y z)) :=
        jordan_pairing_selfadjoint z (innerDer x y z) (innerDer x y (innerDer x y z))
      _ = inner (innerDer x y (innerDer x y z)) (jordan z (innerDer x y z)) :=
        inner_comm _ _
  have hp := innerDer_pairing x y (innerDer x y z) (jordan z (innerDer x y z))
  rw [innerDer_jordan x y z (innerDer x y z), inner_add_right, hcross] at hp
  linarith only [hp]

/-- The third-iterate square pairing equals the cubic pairing of the first iterate.
Only native derivation and associative-pairing laws enter this identity. -/
theorem innerDer_third_pairing_square (x y z : Albert) :
    inner (innerDer x y (innerDer x y (innerDer x y z))) (jordan z z) =
      inner (innerDer x y z) (jordan (innerDer x y z) (innerDer x y z)) := by
  calc
    inner (innerDer x y (innerDer x y (innerDer x y z))) (jordan z z) =
        -inner (innerDer x y (innerDer x y z)) (innerDer x y (jordan z z)) :=
      innerDer_pairing x y (innerDer x y (innerDer x y z)) (jordan z z)
    _ = -(2 * inner (innerDer x y (innerDer x y z))
        (jordan z (innerDer x y z))) := by
      rw [innerDer_square x y z, inner_smul_right]
    _ = -(-inner (innerDer x y z)
        (jordan (innerDer x y z) (innerDer x y z))) := by
      rw [innerDer_second_pairing_product x y z]
    _ = inner (innerDer x y z) (jordan (innerDer x y z) (innerDer x y z)) :=
      neg_neg _

/-- For D = [L_x,L_y], raw B(D³z,z²) = 3 N(Dz), for arbitrary native inputs.
The factor three comes from the existing trace-zero Newton norm formula. -/
theorem innerDer_cube_pairing_norm (x y z : Albert) :
    inner (innerDer x y (innerDer x y (innerDer x y z))) (jordan z z) =
      3 * newtonCubicNorm (innerDer x y z) := by
  rw [innerDer_third_pairing_square x y z,
    WordNormIdentity.newtonCubicNorm_of_trace_zero (innerDer x y z)
      (trace_innerDer x y z)]
  change inner (innerDer x y z) (jordan (innerDer x y z) (innerDer x y z)) =
    3 * (inner (innerDer x y z) (jordan (innerDer x y z) (innerDer x y z)) / 3)
  ring

end
end Glennie.Compact.InnerDerivationCubicNormR01
