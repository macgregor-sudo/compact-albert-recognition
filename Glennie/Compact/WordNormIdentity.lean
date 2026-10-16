module

public import Glennie.BasicLaws
public import Glennie.Theorems.CubicNorm

/- No Frame hypothesis or invariant-theory theorem is an input.
The local names omega and omegaPrime denote the two explicit Jordan words only;
omegaPrime is not identified with a deck conjugate.
The correction c below is a cubic trace difference. It is distinct from kappa,
the omega coefficient in an omega-product decomposition, and from its sheet-even
remainder E. No global c = kappa or E = 0 statement is asserted.
-/

@[expose] public section
namespace Glennie.Compact.WordNormIdentity
open Glennie
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

def a (x y z : Albert) : Albert := jordan (jordan z x) y
def b (x y z : Albert) : Albert := jordan (jordan z y) x
def W0 (x y z : Albert) : Albert := b x y z - a x y z
def omega (x y z : Albert) : ℝ := inner (jordan (a x y z) (a x y z)) (b x y z)
def omegaPrime (x y z : Albert) : ℝ := inner (jordan (b x y z) (b x y z)) (a x y z)
def correctionC (x y z : Albert) : ℝ :=
  (trace (jordan (b x y z) (jordan (b x y z) (b x y z))) -
    trace (jordan (a x y z) (jordan (a x y z) (a x y z)))) / 3

/-- The two nested products always have equal trace. -/
theorem trace_b_eq_trace_a (x y z : Albert) : trace (b x y z) = trace (a x y z) := by
  change inner (jordan z y) x = inner (jordan z x) y
  rw [inner_jordan_associative, inner_jordan_associative, jordan_comm y x]

/-- Tracelessness is an identity for all triples. -/
theorem trace_W0_zero (x y z : Albert) : trace (W0 x y z) = 0 := by
  rw [W0, trace_sub, trace_b_eq_trace_a, sub_self]

/-- At trace zero the existing definition itself is tr(w³)/3. -/
theorem newtonCubicNorm_of_trace_zero (w : Albert) (hw : trace w = 0) :
    newtonCubicNorm w = trace (jordan w (jordan w w)) / 3 := by
  simp only [newtonCubicNorm, hw]
  ring

/-- Symmetry exchanging the first two cubic slots. -/
theorem cubic_swap (u v w : Albert) : inner u (jordan v w) = inner v (jordan u w) := by
  rw [← inner_jordan_associative, jordan_comm u v, inner_jordan_associative]

/-- Bilinear expansion with the two mixed cubic terms retained. -/
theorem cubic_difference (u v : Albert) :
    inner (v - u) (jordan (v - u) (v - u)) =
      inner v (jordan v v) - inner u (jordan u u) +
        3 * (inner (jordan u u) v - inner (jordan v v) u) := by
  simp only [jordan_sub_left, jordan_sub_right, inner_sub_left, inner_sub_right,
    inner_jordan_associative]
  simp only [jordan_comm, cubic_swap]
  have h : inner u (jordan u v) = inner v (jordan u u) := by
    simpa only [jordan_comm v u] using cubic_swap u v u
  rw [h]
  ring

/-- General corrected identity, with its trace correction written out. -/
theorem newtonCubicNorm_W0 (x y z : Albert) :
    newtonCubicNorm (W0 x y z) = omega x y z - omegaPrime x y z +
      (trace (jordan (b x y z) (jordan (b x y z) (b x y z))) -
        trace (jordan (a x y z) (jordan (a x y z) (a x y z)))) / 3 := by
  rw [newtonCubicNorm_of_trace_zero _ (trace_W0_zero x y z)]
  change inner (b x y z - a x y z)
      (jordan (b x y z - a x y z) (b x y z - a x y z)) / 3 = _
  rw [cubic_difference]
  change (inner (b x y z) (jordan (b x y z) (b x y z)) -
    inner (a x y z) (jordan (a x y z) (a x y z)) +
    3 * (omega x y z - omegaPrime x y z)) / 3 =
      omega x y z - omegaPrime x y z +
        (inner (b x y z) (jordan (b x y z) (b x y z)) -
          inner (a x y z) (jordan (a x y z) (a x y z))) / 3
  ring

/-- The same identity using the explicitly named cubic correction c. -/
theorem newtonCubicNorm_W0_corrected (x y z : Albert) :
    newtonCubicNorm (W0 x y z) = omega x y z - omegaPrime x y z + correctionC x y z :=
  newtonCubicNorm_W0 x y z

end
end Glennie.Compact.WordNormIdentity
