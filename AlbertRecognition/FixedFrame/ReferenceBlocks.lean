/- Derived native reference-curvature blocks for the bounded fixed-frame gate.
D is the actual wedge plus KA commutator; no block identity is assumed. -/
module

public import AlbertRecognition.FixedFrame.FrameCoordinates
public import AlbertRecognition.CubicOperators

@[expose] public section
namespace AlbertRecognition.FixedFrame
noncomputable section
open Glennie

private theorem octDot_zero_left (a : Octonion) : octDot 0 a = 0 := by
  simp [octDot_coordinates]
private theorem octDot_zero_right (a : Octonion) : octDot a 0 = 0 := by
  simp [octDot_coordinates]
@[simp] private theorem octConj_zero_native : octConj (0 : Octonion) = 0 := by
  simp [octConj]
private theorem octDot_smul_right (r : ℝ) (a b : Octonion) :
    octDot a (r • b) = r * octDot a b := by
  rw [octDot_comm, octDot_smul_left, octDot_comm b a]

/-- The full native commutator is tracefree by the proved trace pairing law. -/
theorem trace_full_commutator (x y z : V) :
    Glennie.trace (jordan (x : Albert) (jordan (y : Albert) (z : Albert)) -
      jordan (y : Albert) (jordan (x : Albert) (z : Albert))) = 0 := by
  rw [trace_sub]
  change inner (x : Albert) (jordan (y : Albert) (z : Albert)) -
    inner (y : Albert) (jordan (x : Albert) (z : Albert)) = 0
  rw [← inner_jordan_associative, ← inner_jordan_associative,
    jordan_comm (y : Albert) (x : Albert)]
  simp

/-- Raising and projecting indices contributes the exact scalar metric term. -/
theorem KA_projected_composition (x y z : V) :
    KA x (KA y z) =
      project (jordan (x : Albert) (jordan (y : Albert) (z : Albert))) -
        gA y z • x := by
  change project (jordan (x : Albert)
    (traceless (jordan (y : Albert) (z : Albert)))) = _
  rw [traceless, jordan_sub_right, jordan_smul_right, jordan_unit_right,
    map_sub, map_smul, project_V]
  rfl

/-- Exact unit/trace splitting identifies D with the full Jordan commutator.
This uses bilinearity and associative trace pairing, not a Jordan identity. -/
theorem D_apply_project_native (x y z : V) :
    D x y z = project
      (jordan (x : Albert) (jordan (y : Albert) (z : Albert)) -
        jordan (y : Albert) (jordan (x : Albert) (z : Albert))) := by
  unfold D q operatorComm
  rw [KB_referenceCubic]
  change gA y z • x - gA x z • y + (KA x (KA y z) - KA y (KA x z)) = _
  rw [map_sub, KA_projected_composition, KA_projected_composition]
  module

theorem D_apply_native (x y z : V) :
    (D x y z : Albert) =
      jordan (x : Albert) (jordan (y : Albert) (z : Albert)) -
        jordan (y : Albert) (jordan (x : Albert) (z : Albert)) := by
  rw [D_apply_project_native]
  change traceless _ = _
  rw [traceless, trace_full_commutator]
  simp

/- Native coordinate projections of additive negation. These are definitional
identities for the inspected coordinate transport on Albert. -/
@[simp] private theorem albert_neg_d0 (x : Albert) : (-x).d0 = -x.d0 := rfl
@[simp] private theorem albert_neg_d1 (x : Albert) : (-x).d1 = -x.d1 := rfl
@[simp] private theorem albert_neg_d2 (x : Albert) : (-x).d2 = -x.d2 := rfl
@[simp] private theorem albert_neg_o01 (x : Albert) : (-x).o01 = -x.o01 := rfl
@[simp] private theorem albert_neg_o02 (x : Albert) : (-x).o02 = -x.o02 := rfl
@[simp] private theorem albert_neg_o12 (x : Albert) : (-x).o12 = -x.o12 := rfl

private def nativeDiagonal (r s t : ℝ) : Albert := ⟨r,s,t,0,0,0⟩

/-- Finite native diagonal multiplication, with arbitrary real coefficients. -/
private theorem jordan_diagonal (r s t : ℝ) (x : Albert) :
    jordan (nativeDiagonal r s t) x =
      ⟨r*x.d0,s*x.d1,t*x.d2,((r+s)/2) • x.o01,
        ((r+t)/2) • x.o02,((s+t)/2) • x.o12⟩ := by
  apply Albert.ext
  all_goals simp [nativeDiagonal, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12, octDot_zero_left, octMul_zero_left,
    octMul_zero_right, octConj_zero_native, smul_smul, div_eq_mul_inv]
  all_goals first | ring | (congr 1 <;> ring)

/-- Finite slot12 multiplication, preserving each native binary product. -/
private theorem jordan_slot12 (a : Octonion) (x : Albert) :
    jordan (X12 a : Albert) x =
      ⟨0,octDot a x.o12,octDot a x.o12,
        (1/2 : ℝ) • octMul x.o02 (octConj a),
        (1/2 : ℝ) • octMul x.o01 a,((x.d1+x.d2)/2) • a⟩ := by
  apply Albert.ext
  all_goals simp [X12, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12, octDot_zero_left, octMul_zero_left,
    octMul_zero_right, octConj_zero_native, smul_smul, div_eq_mul_inv]
  all_goals first | ring | (congr 1 <;> ring)

private theorem h1_nativeDiagonal : (h 1 : Albert) = nativeDiagonal 1 (-2) 1 := by
  apply Albert.ext <;> norm_num [h, e, unit, nativeDiagonal]

/-- The complete native formula on an arbitrary full Albert input. -/
private theorem full_commutator_h1_slot12 (a : Octonion) (x : Albert) :
    jordan (nativeDiagonal 1 (-2) 1) (jordan (X12 a : Albert) x) -
      jordan (X12 a : Albert) (jordan (nativeDiagonal 1 (-2) 1) x) =
      ⟨0,-(3/2 : ℝ)*octDot a x.o12,(3/2 : ℝ)*octDot a x.o12,
        -(3/4 : ℝ) • octMul x.o02 (octConj a),
        (3/4 : ℝ) • octMul x.o01 a,
        ((3/4 : ℝ)*(x.d1-x.d2)) • a⟩ := by
  apply Albert.ext
  all_goals simp [jordan_diagonal, jordan_slot12, octDot_smul_right,
    octMul_smul_left, smul_smul]
  all_goals try simp only [← sub_smul, ← neg_smul]
  all_goals congr 1 <;> ring

/-- The operator uses the zero-based h1, complementary to the distinguished h0. -/
def frameAction (a : Octonion) : V →ₗ[ℝ] V := D (h 1) (X12 a)

theorem frameAction_coordinates (a : Octonion) (x : V) :
    (frameAction a x : Albert) =
      ⟨0,-(3/2 : ℝ)*octDot a (x : Albert).o12,
        (3/2 : ℝ)*octDot a (x : Albert).o12,
        -(3/4 : ℝ) • octMul (x : Albert).o02 (octConj a),
        (3/4 : ℝ) • octMul (x : Albert).o01 a,
        ((3/4 : ℝ)*((x : Albert).d1-(x : Albert).d2)) • a⟩ := by
  rw [frameAction, D_apply_native, h1_nativeDiagonal]
  exact full_commutator_h1_slot12 a (x : Albert)

theorem frameAction_h0 (a : Octonion) : frameAction a (h 0) = 0 := by
  apply Subtype.ext
  rw [frameAction_coordinates]
  apply Albert.ext <;>
    simp [h, e, unit, octDot_zero_right, octMul_zero_left] <;> ring

theorem frameAction_d (a : Octonion) :
    frameAction a frameD = (3/2 : ℝ) • X12 a := by
  apply Subtype.ext
  rw [frameAction_coordinates]
  apply Albert.ext <;>
    simp [frameD, X12, octDot_zero_right, octMul_zero_left, smul_smul] <;>
    first | ring | module

theorem frameAction_X12 (a z : Octonion) :
    frameAction a (X12 z) = (-(3/2 : ℝ)*octDot a z) • frameD := by
  apply Subtype.ext
  rw [frameAction_coordinates]
  apply Albert.ext <;>
    simp [X12, frameD, octMul_zero_left] <;> first | ring | module

theorem frameAction_X01 (a u : Octonion) :
    frameAction a (X01 u) = (3/4 : ℝ) • X02 (octMul u a) := by
  apply Subtype.ext
  rw [frameAction_coordinates]
  apply Albert.ext <;>
    simp [X01, X02, octDot_zero_right, octMul_zero_left] <;> first | ring | module

theorem frameAction_X02 (a v : Octonion) :
    frameAction a (X02 v) = -(3/4 : ℝ) • X01 (octMul v (octConj a)) := by
  apply Subtype.ext
  rw [frameAction_coordinates]
  apply Albert.ext <;>
    simp [X01, X02, octDot_zero_right, octMul_zero_left] <;> first | ring | module

/-- The exact signed native 16D block, with its actual upper-slot embeddings. -/
theorem frameAction_spin (a : Octonion) (s : Spin) :
    frameAction a (frameSpin s) = (3/4 : ℝ) • frameSpin (spinJ a s) := by
  rcases s with ⟨u,v⟩
  rw [frameSpin_apply, map_add, frameAction_X01, frameAction_X02, spinJ_apply,
    frameSpin_apply]
  simp only [map_neg]
  module

/-- The entire operator in actual rational frame coordinates. -/
theorem frameAction_frameEmbed (a : Octonion) (alpha beta : ℝ)
    (z : Octonion) (s : Spin) :
    frameAction a (frameEmbed (alpha,beta,z,s)) =
      frameEmbed (0,-(3/2 : ℝ)*octDot a z,
        ((3/2 : ℝ)*beta) • a,(3/4 : ℝ) • spinJ a s) := by
  rw [frameEmbed_eq, frameEmbed_eq]
  simp only [map_add, map_smul, frameAction_h0, frameAction_d,
    frameAction_X12, frameAction_spin, zero_smul, zero_add]
  module

end
end AlbertRecognition.FixedFrame
