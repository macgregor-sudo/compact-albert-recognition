module

public import Glennie.Native.CubicIdentity
public import Glennie.Theorems.CubicNorm
public import Glennie.Theorems.Frames

/- Polynomial projectors for trace-zero norm-two cubic-norm-zero elements.
   These are derived from the native cubic residual and Jordan identity. -/

@[expose] public section
namespace Glennie
noncomputable section

set_option maxHeartbeats 2000000

def projectorFrame (x : Albert) : Fin 3 → Albert :=
  ![(1 / 2 : ℝ) • (jordan x x - x), 1 - jordan x x,
    (1 / 2 : ℝ) • (jordan x x + x)]

private theorem projector_cube_recursion (x : Albert) :
    jordan x (jordan x x) = (trace x) • jordan x x -
      (((trace x)^2-inner x x)/2) • x + newtonCubicNorm x • (1 : Albert) := by
  have h6 : (6 : ℝ) • (jordan x (jordan x x) -
      ((trace x) • jordan x x - (((trace x)^2-inner x x)/2) • x +
        newtonCubicNorm x • (1 : Albert))) = 0 := by
    calc
      _ = CubicJordan.residual jordanLinear traceLinear (1 : Albert) x := by
        simp only [CubicJordan.residual,jordanLinear_apply,traceLinear_apply,
          newtonCubicNorm,inner]
        module
      _ = 0 := cubicResidual_eq_zero x
  have h := congrArg (fun z : Albert => (1/6 : ℝ) • z) h6
  have hz : jordan x (jordan x x) -
      ((trace x) • jordan x x - (((trace x)^2-inner x x)/2) • x +
        newtonCubicNorm x • (1 : Albert)) = 0 := by
    simpa [smul_smul] using h
  exact sub_eq_zero.mp hz

theorem cube_of_trace_norm_cubic (x : Albert) (ht : trace x=0)
    (hn : inner x x=2) (hc : newtonCubicNorm x=0) :
    jordan x (jordan x x)=x := by
  rw [projector_cube_recursion,ht,hn,hc]
  norm_num

theorem projectorFrame_is_frame_of_cube (x : Albert) (ht : trace x=0)
    (hn : inner x x=2) (hc : jordan x (jordan x x)=x) :
    Frame (projectorFrame x) := by
  have hs : trace (jordan x x)=2 := hn
  have h4 : jordan (jordan x x) (jordan x x)=jordan x x := by
    rw [jordan_identity x x,hc]
  have hsx : jordan (jordan x x) x=x := by rw [jordan_comm,hc]
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    fin_cases i <;> norm_num [projectorFrame,trace_smul,trace_add,
      trace_sub,trace_unit,ht,hs]
  · intro i
    fin_cases i <;> simp only [Fin.reduceFinMk,projectorFrame,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.tail_cons,Matrix.head_cons,
      Matrix.cons_val_fin_one,
      jordan_add_left,jordan_add_right,jordan_sub_left,jordan_sub_right,
      jordan_smul_left,jordan_smul_right,jordan_unit_left,jordan_unit_right,
      hc,h4,hsx] <;> module
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals try exact (hij rfl).elim
    all_goals simp only [Fin.reduceFinMk,projectorFrame,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.tail_cons,Matrix.head_cons,
      Matrix.cons_val_fin_one,
      jordan_add_left,jordan_add_right,jordan_sub_left,jordan_sub_right,
      jordan_smul_left,jordan_smul_right,jordan_unit_left,jordan_unit_right,
      hc,h4,hsx]
    all_goals module
  · simp only [projectorFrame,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.tail_cons,Matrix.head_cons,Matrix.cons_val_fin_one]
    module

theorem projectorFrame_is_frame (x : Albert) (ht : trace x=0)
    (hn : inner x x=2) (hc : newtonCubicNorm x=0) : Frame (projectorFrame x) :=
  projectorFrame_is_frame_of_cube x ht hn (cube_of_trace_norm_cubic x ht hn hc)

theorem projectorFrame_encoder (x : Albert) : encoder (projectorFrame x)=x := by
  simp only [encoder,projectorFrame,Matrix.cons_val_zero,
    Matrix.cons_val_two,Matrix.tail_cons,Matrix.head_cons]
  module

theorem newtonCubicNorm_smul (a : ℝ) (x : Albert) :
    newtonCubicNorm (a • x)=a^3*newtonCubicNorm x := by
  simp only [newtonCubicNorm,jordan_smul_left,jordan_smul_right,
    trace_smul,smul_smul]
  ring

end
end Glennie
