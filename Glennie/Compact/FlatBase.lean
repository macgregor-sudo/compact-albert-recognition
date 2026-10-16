/- The flat base, read through the dictionary, gives actual native frames
  P = projectorFrame x,  Q = projectorFrame y,  R = projectorFrame z,
with x = -witnessX, y = s * Y1, z = s * witnessZ and s = 1/sqrt 3. Here
witnessX and witnessZ are the literals of Native/Statements, and Y1
is the flat y at s = 1.
  * phi(P, Q, R) = -4/27. The first-frame reversal P' = projectorFrame witnessX
    (proved equal to reverseFrame P) has phi(P', Q, R) = +4/27.
  * Both triples have the uniform ledger (all 27 raw triple traces 1/9), by
    the `frame_equality`, and all 27 pair overlaps 1/3. So the two
    opposite-sign triples share the same complete 54-entry ledger.
The literal computation, phi(witnessX, Y1, witnessZ) = 4, follows the
Theorems/Witness.lean pattern. -/
module

public import Glennie.Compact.NativeDictionaryLiteral
public import Glennie.Theorems.ProjectorFrame
public import Glennie.Theorems.Frames
public import Glennie.Theorems.FrameEquality
public import Glennie.BasicLaws

@[expose] public section

namespace Glennie.Compact.FlatBase

open Glennie.Compact.NativeDictionary

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-! ## The flat elements and their coordinates -/

/-- s = theta^-1 = 1/sqrt 3. -/
def flatScale : ℝ := 1 / Real.sqrt 3

theorem flatScale_sq : flatScale ^ 2 = 1 / 3 := by
  dsimp [flatScale]
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

/-- The flat x = diag(1, 0, -1). -/
def flatXN : Albert := ⟨1, 0, -1, 0, 0, 0⟩

/-- The flat y at s = 1. -/
def flatY1 : Albert := ⟨0, 0, 0, octScalar 1, -octI, octScalar 1⟩

theorem flatXN_eq : flatXN = (-1 : ℝ) • witnessX := by
  refine Albert.ext ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Albert.smul_d0]
    norm_num [flatXN, witnessX]
  · rw [Albert.smul_d1]
    norm_num [flatXN, witnessX]
  · rw [Albert.smul_d2]
    norm_num [flatXN, witnessX]
  · rw [Albert.smul_o01]
    simp [flatXN, witnessX]
  · rw [Albert.smul_o02]
    simp [flatXN, witnessX]
  · rw [Albert.smul_o12]
    simp [flatXN, witnessX]

theorem extDecode_flatXCoords_eq : extDecode flatXCoords = flatXN := by
  rw [extDecode_flatX]
  rfl

theorem extDecode_flatYCoords_eq (s : ℝ) : extDecode (flatYCoords s) = s • flatY1 := by
  rw [extDecode_flatY]
  ext <;> simp [complexAlbert, complexOct, flatY1, octScalar, octI, quatI] <;> ring

theorem extDecode_flatZCoords_eq (s : ℝ) : extDecode (flatZCoords s) = s • witnessZ := by
  rw [extDecode_flatZ]
  ext <;> simp [hiddenAlbert, hiddenOct, witnessZ, octJL, octL, octK, quatJ, quatK] <;> ring

/-! ## Literal invariants (Witness.lean pattern) -/

theorem flat_traces :
    trace flatXN = 0 ∧ trace witnessX = 0 ∧ trace flatY1 = 0 ∧ trace witnessZ = 0 := by
  norm_num [trace, flatXN, witnessX, flatY1, witnessZ]

theorem flat_norms : inner flatXN flatXN = 2 ∧ inner witnessX witnessX = 2 ∧
    inner flatY1 flatY1 = 6 ∧ inner witnessZ witnessZ = 6 := by
  norm_num [inner_self_coordinates, flatXN, witnessX, flatY1, witnessZ, octNormSq,
    Quaternion.normSq_def', octScalar, octI, octJL, octL, octK, quatI, quatJ, quatK]

theorem flat_cubic_norms : newtonCubicNorm flatXN = 0 ∧ newtonCubicNorm witnessX = 0 ∧
    newtonCubicNorm flatY1 = 0 ∧ newtonCubicNorm witnessZ = 0 := by
  norm_num [newtonCubicNorm_coordinates, flatXN, witnessX, flatY1, witnessZ, octNormSq,
    Quaternion.normSq_def', octScalar, octI, octJL, octL, octK, quatI, quatJ, quatK,
    octMul, octConj, octRe, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul]
  all_goals (try norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat])

/-- witnessX o Y1 (equal to the private witnessXY). -/
def flatBaseXY : Albert := ⟨0, 0, 0,
  ((⟨(-1/2 : ℝ), 0, 0, 0⟩ : Quaternion ℝ), 0), 0,
  ((⟨(1/2 : ℝ), 0, 0, 0⟩ : Quaternion ℝ), 0)⟩

/-- U witnessX (U Y1 witnessZ). -/
def flatBaseFirstU : Albert := ⟨0, 0, 0, 0,
  ((⟨0, 0, -1, 0⟩ : Quaternion ℝ), (⟨-1, 0, 0, -1⟩ : Quaternion ℝ)), 0⟩

/-- U Y1 (U witnessX witnessZ). -/
def flatBaseSecondU : Albert := ⟨0, 0, 0,
  (0, (⟨0, 1, 0, 0⟩ : Quaternion ℝ)),
  (0, (⟨-1, 0, 0, 0⟩ : Quaternion ℝ)),
  (0, (⟨0, -1, 0, 0⟩ : Quaternion ℝ))⟩

/-- U witnessZ (witnessX o Y1). -/
def flatBaseThirdU : Albert := ⟨0, 0, 0,
  ((⟨(1/2 : ℝ), 0, 0, 0⟩ : Quaternion ℝ), (⟨0, (-1/2 : ℝ), 0, 0⟩ : Quaternion ℝ)),
  ((⟨0, 0, (-1/2 : ℝ), 0⟩ : Quaternion ℝ), (⟨0, 0, 0, (-1/2 : ℝ)⟩ : Quaternion ℝ)),
  ((⟨(-1/2 : ℝ), 0, 0, 0⟩ : Quaternion ℝ), (⟨0, (1/2 : ℝ), 0, 0⟩ : Quaternion ℝ))⟩

theorem flat_xy : jordan witnessX flatY1 = flatBaseXY := by
  ext <;> norm_num [flatBaseXY, witnessX, flatY1, octI, quatI, octScalar,
    jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
    octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals (try norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat])
  all_goals (try ring)

theorem flat_first_u : U witnessX (U flatY1 witnessZ) = flatBaseFirstU := by
  ext <;> norm_num [U, flatBaseFirstU, witnessX, flatY1, witnessZ,
    octI, octJ, octK, octL, octJL, quatI, quatJ, quatK, octScalar,
    jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
    octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals (try norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat])
  all_goals (try ring)

theorem flat_second_u : U flatY1 (U witnessX witnessZ) = flatBaseSecondU := by
  ext <;> norm_num [U, flatBaseSecondU, witnessX, flatY1, witnessZ,
    octI, octJ, octK, octL, octJL, quatI, quatJ, quatK, octScalar,
    jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
    octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals (try norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat])
  all_goals (try ring)

theorem flat_third_u : U witnessZ (jordan witnessX flatY1) = flatBaseThirdU := by
  rw [flat_xy]
  ext <;> norm_num [U, flatBaseXY, flatBaseThirdU, witnessZ,
    octJ, octK, octL, octJL, quatI, quatJ, quatK, octScalar,
    jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
    octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals (try norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat])
  all_goals (try ring)

/-- The one new scalar: phi(witnessX, Y1, witnessZ) = 4. -/
theorem phi_witnessX_flatY1_witnessZ : phi witnessX flatY1 witnessZ = 4 := by
  rw [phi, flat_first_u, flat_second_u, flat_third_u]
  norm_num [inner_coordinates, octDot_coordinates, flatBaseFirstU, flatBaseSecondU,
    flatBaseThirdU]

/-! ## Frames, first-frame reversal and the shared complete ledger -/

/-- First-frame reversal of an ordered frame. -/
def reverseFrame (p : Fin 3 → Albert) : Fin 3 → Albert := ![p 2, p 1, p 0]

theorem reverseFrame_reverseFrame (p : Fin 3 → Albert) :
    reverseFrame (reverseFrame p) = p := by
  funext i
  fin_cases i <;> rfl

theorem projectorFrame_neg_one_smul (x : Albert) :
    projectorFrame ((-1 : ℝ) • x) = reverseFrame (projectorFrame x) := by
  have hxx : jordan ((-1 : ℝ) • x) ((-1 : ℝ) • x) = jordan x x := by
    rw [jordan_smul_left, jordan_smul_right, smul_smul, neg_one_mul, neg_neg, one_smul]
  funext i
  fin_cases i
  · show (1 / 2 : ℝ) • (jordan ((-1 : ℝ) • x) ((-1 : ℝ) • x) - (-1 : ℝ) • x) =
      (1 / 2 : ℝ) • (jordan x x + x)
    rw [hxx]
    module
  · show (1 : Albert) - jordan ((-1 : ℝ) • x) ((-1 : ℝ) • x) = 1 - jordan x x
    rw [hxx]
  · show (1 / 2 : ℝ) • (jordan ((-1 : ℝ) • x) ((-1 : ℝ) • x) + (-1 : ℝ) • x) =
      (1 / 2 : ℝ) • (jordan x x - x)
    rw [hxx]
    module

def flatFrameP : Fin 3 → Albert := projectorFrame flatXN
def flatFrameQ : Fin 3 → Albert := projectorFrame (flatScale • flatY1)
def flatFrameR : Fin 3 → Albert := projectorFrame (flatScale • witnessZ)
/-- The opposite-sign partner: first-frame reversal of flatFrameP. -/
def flatFramePRev : Fin 3 → Albert := projectorFrame witnessX

theorem flatFramePRev_eq_reverse : flatFramePRev = reverseFrame flatFrameP := by
  show projectorFrame witnessX = reverseFrame (projectorFrame flatXN)
  rw [flatXN_eq, projectorFrame_neg_one_smul, reverseFrame_reverseFrame]

/-- The four frames are the flat base read through the dictionary. -/
theorem flatFrames_archive :
    flatFrameP = projectorFrame (extDecode flatXCoords) ∧
      flatFrameQ = projectorFrame (extDecode (flatYCoords flatScale)) ∧
      flatFrameR = projectorFrame (extDecode (flatZCoords flatScale)) ∧
      flatFramePRev = reverseFrame (projectorFrame (extDecode flatXCoords)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [flatFrameP, extDecode_flatXCoords_eq]
  · simp only [flatFrameQ, extDecode_flatYCoords_eq]
  · simp only [flatFrameR, extDecode_flatZCoords_eq]
  · rw [extDecode_flatXCoords_eq]
    exact flatFramePRev_eq_reverse

theorem flatFrameP_frame : Frame flatFrameP :=
  projectorFrame_is_frame flatXN flat_traces.1 flat_norms.1 flat_cubic_norms.1

theorem flatFramePRev_frame : Frame flatFramePRev :=
  projectorFrame_is_frame witnessX flat_traces.2.1 flat_norms.2.1 flat_cubic_norms.2.1

theorem flatFrameQ_frame : Frame flatFrameQ := by
  apply projectorFrame_is_frame
  · rw [trace_smul, flat_traces.2.2.1, mul_zero]
  · rw [inner_smul_left, inner_smul_right, flat_norms.2.2.1]
    linear_combination 6 * flatScale_sq
  · rw [newtonCubicNorm_smul, flat_cubic_norms.2.2.1, mul_zero]

theorem flatFrameR_frame : Frame flatFrameR := by
  apply projectorFrame_is_frame
  · rw [trace_smul, flat_traces.2.2.2, mul_zero]
  · rw [inner_smul_left, inner_smul_right, flat_norms.2.2.2]
    linear_combination 6 * flatScale_sq
  · rw [newtonCubicNorm_smul, flat_cubic_norms.2.2.2, mul_zero]

theorem flatFrameP_encoder : encoder flatFrameP = flatXN := projectorFrame_encoder _
theorem flatFramePRev_encoder : encoder flatFramePRev = witnessX := projectorFrame_encoder _
theorem flatFrameQ_encoder : encoder flatFrameQ = flatScale • flatY1 := projectorFrame_encoder _
theorem flatFrameR_encoder : encoder flatFrameR = flatScale • witnessZ := projectorFrame_encoder _

theorem flat_phi :
    phi (encoder flatFrameP) (encoder flatFrameQ) (encoder flatFrameR) = -4 / 27 := by
  rw [flatFrameP_encoder, flatFrameQ_encoder, flatFrameR_encoder, flatXN_eq,
    phi_smul_first, phi_smul_second, phi_smul_third, phi_witnessX_flatY1_witnessZ]
  calc
    _ = -4 * (flatScale ^ 2) ^ 3 := by ring
    _ = -4 / 27 := by rw [flatScale_sq]; norm_num

theorem flatRev_phi :
    phi (encoder flatFramePRev) (encoder flatFrameQ) (encoder flatFrameR) = 4 / 27 := by
  rw [flatFramePRev_encoder, flatFrameQ_encoder, flatFrameR_encoder,
    phi_smul_second, phi_smul_third, phi_witnessX_flatY1_witnessZ]
  calc
    _ = 4 * (flatScale ^ 2) ^ 3 := by ring
    _ = 4 / 27 := by rw [flatScale_sq]; norm_num

/-- All 27 raw triple traces are 1/9, by the audited frame equality. -/
theorem flat_uniform : UniformLedger flatFrameP flatFrameQ flatFrameR :=
  (frame_equality flatFrameP flatFrameQ flatFrameR flatFrameP_frame flatFrameQ_frame
    flatFrameR_frame).mp (by rw [flat_phi, abs_of_neg (by norm_num : (-4 / 27 : ℝ) < 0)]; norm_num)

theorem flatRev_uniform : UniformLedger flatFramePRev flatFrameQ flatFrameR :=
  (frame_equality flatFramePRev flatFrameQ flatFrameR flatFramePRev_frame flatFrameQ_frame
    flatFrameR_frame).mp (by rw [flatRev_phi, abs_of_pos (by norm_num : (0 : ℝ) < 4 / 27)])

/-- The three 9-entry pair-overlap blocks of a uniform frame triple are all 1/3. -/
theorem uniform_pair_blocks (p q r : Fin 3 → Albert) (hp : Frame p) (hq : Frame q)
    (hr : Frame r) (hu : UniformLedger p q r) (i j : Fin 3) :
    inner (p i) (q j) = 1 / 3 ∧ inner (q i) (r j) = 1 / 3 ∧ inner (r i) (p j) = 1 / 3 :=
  ⟨uniformLedger_pair_overlap p q r hr hu i j,
    uniformLedger_pair_overlap q r p hp (uniformLedger_cyclic p q r hu) i j,
    uniformLedger_pair_overlap r p q hq
      (uniformLedger_cyclic q r p (uniformLedger_cyclic p q r hu)) i j⟩

/-- Two genuine native frame triples at the flat base,
with the same complete 54-entry ledger (27 triple traces 1/9, 27 pair overlaps
1/3) and opposite Phi = -4/27 and +4/27; the second is the first-frame reversal
of the first. -/
theorem flat_base_two_witnesses :
    Frame flatFrameP ∧ Frame flatFramePRev ∧ Frame flatFrameQ ∧ Frame flatFrameR ∧
      flatFramePRev = reverseFrame flatFrameP ∧
      UniformLedger flatFrameP flatFrameQ flatFrameR ∧
      UniformLedger flatFramePRev flatFrameQ flatFrameR ∧
      (∀ i j : Fin 3, inner (flatFrameP i) (flatFrameQ j) = 1 / 3 ∧
        inner (flatFrameQ i) (flatFrameR j) = 1 / 3 ∧
        inner (flatFrameR i) (flatFrameP j) = 1 / 3) ∧
      (∀ i j : Fin 3, inner (flatFramePRev i) (flatFrameQ j) = 1 / 3 ∧
        inner (flatFrameQ i) (flatFrameR j) = 1 / 3 ∧
        inner (flatFrameR i) (flatFramePRev j) = 1 / 3) ∧
      phi (encoder flatFrameP) (encoder flatFrameQ) (encoder flatFrameR) = -4 / 27 ∧
      phi (encoder flatFramePRev) (encoder flatFrameQ) (encoder flatFrameR) = 4 / 27 :=
  ⟨flatFrameP_frame, flatFramePRev_frame, flatFrameQ_frame, flatFrameR_frame,
    flatFramePRev_eq_reverse, flat_uniform, flatRev_uniform,
    uniform_pair_blocks _ _ _ flatFrameP_frame flatFrameQ_frame flatFrameR_frame flat_uniform,
    uniform_pair_blocks _ _ _ flatFramePRev_frame flatFrameQ_frame flatFrameR_frame
      flatRev_uniform,
    flat_phi, flatRev_phi⟩

end
end Glennie.Compact.FlatBase
