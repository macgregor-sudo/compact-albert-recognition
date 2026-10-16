/- The actual compact Newton cubic identity and resulting Jordan identity. -/
module

public import Glennie.Native.AlgebraLaws
public import Glennie.Native.CubicJordan

@[expose] public section

namespace Glennie
noncomputable section

set_option linter.unusedSimpArgs false

def jordanLinear : Albert →ₗ[ℝ] Albert →ₗ[ℝ] Albert where
  toFun x :=
    { toFun := jordan x
      map_add' := fun y z => jordan_add_right x y z
      map_smul' := fun r y => jordan_smul_right r x y }
  map_add' x y := LinearMap.ext fun z => jordan_add_left x y z
  map_smul' r x := LinearMap.ext fun y => jordan_smul_left r x y

def traceLinear : Albert →ₗ[ℝ] ℝ where
  toFun := trace
  map_add' := trace_add
  map_smul' := trace_smul

@[simp] theorem jordanLinear_apply (x y : Albert) : jordanLinear x y = jordan x y := rfl
@[simp] theorem traceLinear_apply (x : Albert) : traceLinear x = trace x := rfl

set_option maxHeartbeats 8000000 in
/-- The Newton residual is proved in all 27 native compact coordinates. -/
theorem cubicResidual_eq_zero (x : Albert) :
    CubicJordan.residual jordanLinear traceLinear (1 : Albert) x = 0 := by
  change (6 : ℝ) • jordan x (jordan x x) - (6 * trace x) • jordan x x +
    (3 * (trace x) ^ 2 - 3 * trace (jordan x x)) • x -
    ((trace x) ^ 3 - 3 * trace x * trace (jordan x x) +
      2 * trace (jordan x (jordan x x))) • (1 : Albert) = 0
  ext
  all_goals simp [jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02,
    jordan_o12, trace, octDot_coordinates, octNormSq, Quaternion.normSq_def',
    octMul, octConj, Quaternion.re_mul,
    Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, smul_eq_mul]
  all_goals ring

set_option maxHeartbeats 2000000 in
/-- The native compact Hermitian product satisfies the Jordan identity. -/
theorem jordan_identity (x y : Albert) :
    jordan (jordan x y) (jordan x x) = jordan x (jordan y (jordan x x)) := by
  have hc : ∀ a b, jordanLinear a b = jordanLinear b a := fun a b => by
    simpa only [jordanLinear_apply] using jordan_comm a b
  have hu : ∀ a, jordanLinear 1 a = a := fun a => by
    simpa only [jordanLinear_apply] using jordan_unit_left a
  have ht : ∀ a b c, traceLinear (jordanLinear (jordanLinear a b) c) =
      traceLinear (jordanLinear a (jordanLinear b c)) := fun a b c => by
    simp only [jordanLinear_apply, traceLinear_apply]
    exact inner_jordan_associative a b c
  have h := CubicJordan.jordan_of_cubic_trace_identity jordanLinear traceLinear 1
    hc hu ht cubicResidual_eq_zero x y
  simpa only [jordanLinear_apply] using h

end
end Glennie
