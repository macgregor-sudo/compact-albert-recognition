/- Exactly original FlatBase columns0 and1, all20 rows including zeros.
   Their native coordinate proofs precede comparison with JQ. The
   NativeFlatColumns23 module supplies only the two original fixed-column
   comparisons used by the final four-column conjunction. This module adds
   no desired derivative/Jacobian hypothesis, replacement family or definition. -/
module

public import Glennie.Compact.NativeFlatColumns23

@[expose] public section

namespace Glennie.Compact.NativeFlatColumns01

open Glennie.Compact.NativeDictionary
open Glennie.Compact.FlatBase
open Glennie.Compact.FlowFamily
open Glennie.Compact.Rank20
open Glennie.Compact.Rank20Certificate

noncomputable section
set_option autoImplicit false

private theorem flatFrameP_literal (i : Fin 3) :
    flatFrameP i =
      ![diagonalAlbert 0 0 1, diagonalAlbert 0 1 0,
        diagonalAlbert 1 0 0] i := by
  fin_cases i <;> ext <;>
    norm_num [flatFrameP, projectorFrame, flatXN, diagonalAlbert,
      jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octNormSq, Quaternion.normSq_def', octMul, octConj, octScalar,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul]

set_option maxHeartbeats 1000000 in
private theorem direction_zero_flatFrameP (i : Fin 3) :
    direction 0 (flatFrameP i) =
      ![(0 : Albert),
        ⟨0, 0, 0, octScalar (1 / 2), 0, 0⟩,
        ⟨0, 0, 0, octScalar (-1 / 2), 0, 0⟩] i := by
  have hp : partnerIndex (0 : Fin 20) = 3 := rfl
  rw [direction, hp, extDecode_extUnit_1, extDecode_extUnit_3,
    Glennie.Compact.innerDerLinear_apply, flatFrameP_literal i]
  fin_cases i <;> ext <;>
    norm_num [Glennie.Compact.innerDer, diagonalAlbert, complexAlbert, complexOct,
      jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octNormSq, Quaternion.normSq_def', octMul, octConj, octScalar,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;>
    simp only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num

set_option maxHeartbeats 1000000 in
private theorem direction_one_flatFrameP (i : Fin 3) :
    direction 1 (flatFrameP i) =
      ![(0 : Albert),
        ⟨0, 0, 0, ((⟨0, 1 / 2, 0, 0⟩ : Quaternion ℝ), 0), 0, 0⟩,
        ⟨0, 0, 0, ((⟨0, -1 / 2, 0, 0⟩ : Quaternion ℝ), 0), 0, 0⟩] i := by
  have hp : partnerIndex (1 : Fin 20) = 4 := rfl
  rw [direction, hp, extDecode_extUnit_1, extDecode_extUnit_4,
    Glennie.Compact.innerDerLinear_apply, flatFrameP_literal i]
  fin_cases i <;> ext <;>
    norm_num [Glennie.Compact.innerDer, diagonalAlbert, complexAlbert, complexOct,
      jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octNormSq, Quaternion.normSq_def', octMul, octConj, octScalar,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;>
    simp only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num

/- These are whole native atom equalities, derived from the projector formula.
   They contain no certificate entry, assumed velocity or trace hypothesis. -/
private theorem flatFrameQ_literal (j : Fin 3) :
    flatFrameQ j =
      ![(⟨1 / 3, 1 / 3, 1 / 3,
          ((⟨-flatScale / 2, -1 / 6, 0, 0⟩ : Quaternion ℝ), 0),
          ((⟨1 / 6, flatScale / 2, 0, 0⟩ : Quaternion ℝ), 0),
          ((⟨-flatScale / 2, -1 / 6, 0, 0⟩ : Quaternion ℝ), 0)⟩ : Albert),
        ⟨1 / 3, 1 / 3, 1 / 3,
          ((⟨0, 1 / 3, 0, 0⟩ : Quaternion ℝ), 0),
          ((⟨-1 / 3, 0, 0, 0⟩ : Quaternion ℝ), 0),
          ((⟨0, 1 / 3, 0, 0⟩ : Quaternion ℝ), 0)⟩,
        ⟨1 / 3, 1 / 3, 1 / 3,
          ((⟨flatScale / 2, -1 / 6, 0, 0⟩ : Quaternion ℝ), 0),
          ((⟨1 / 6, -flatScale / 2, 0, 0⟩ : Quaternion ℝ), 0),
          ((⟨flatScale / 2, -1 / 6, 0, 0⟩ : Quaternion ℝ), 0)⟩] j := by
  fin_cases j <;> ext <;>
    simp [flatFrameQ, projectorFrame, flatY1, octI, quatI, octScalar,
      jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octNormSq, Quaternion.normSq_def', octMul, octConj,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;>
    ring_nf <;> norm_num [flatScale_sq]

private theorem flatFrameR_literal (k : Fin 3) :
    flatFrameR k =
      ![(⟨1 / 3, 1 / 3, 1 / 3,
          (0, (⟨0, 0, -flatScale / 2, 1 / 6⟩ : Quaternion ℝ)),
          (0, (⟨flatScale / 2, 1 / 6, 0, 0⟩ : Quaternion ℝ)),
          ((⟨0, 0, -1 / 6, flatScale / 2⟩ : Quaternion ℝ), 0)⟩ : Albert),
        ⟨1 / 3, 1 / 3, 1 / 3,
          (0, (⟨0, 0, 0, -1 / 3⟩ : Quaternion ℝ)),
          (0, (⟨0, -1 / 3, 0, 0⟩ : Quaternion ℝ)),
          ((⟨0, 0, 1 / 3, 0⟩ : Quaternion ℝ), 0)⟩,
        ⟨1 / 3, 1 / 3, 1 / 3,
          (0, (⟨0, 0, flatScale / 2, 1 / 6⟩ : Quaternion ℝ)),
          (0, (⟨-flatScale / 2, 1 / 6, 0, 0⟩ : Quaternion ℝ)),
          ((⟨0, 0, -1 / 6, -flatScale / 2⟩ : Quaternion ℝ), 0)⟩] k := by
  fin_cases k <;> ext <;>
    simp [flatFrameR, projectorFrame, witnessZ, octJL, octL, octK, quatJ, quatK,
      jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octNormSq, Quaternion.normSq_def', octMul, octConj,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;>
    ring_nf <;> norm_num [flatScale_sq]

private theorem flat_pair_o01_re (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o01.1.re =
      ![-flatScale / 6, 0, flatScale / 6] j := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o01, octMul, octConj,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;> ring

private theorem flat_pair_o01_imI (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o01.1.imI =
      ![(-1 / 18 : ℝ), 1 / 9, -1 / 18] j := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o01, octMul, octConj,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;> ring

private theorem flatScale_eq_sqrt3_div_three : flatScale = Real.sqrt 3 / 3 := by
  have hsq : Real.sqrt (3 : ℝ) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn : Real.sqrt (3 : ℝ) ≠ 0 := by
    intro h
    rw [h] at hsq
    norm_num at hsq
  dsimp [flatScale]
  apply (div_eq_div_iff hn (by norm_num : (3 : ℝ) ≠ 0)).2
  nlinarith [hsq]

set_option maxHeartbeats 1000000 in
/-- All20 original raw rows in fixed column0, including its thirteen zeros. -/
theorem jacobianEntry_flatBase_column_zero (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 0 = JQ r 0 := by
  rw [jacobianEntry_ctx0 _ r 0 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_zero_flatFrameP]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates, octScalar,
      flat_pair_o01_re, flatScale_eq_sqrt3_div_three, JQ, JZ] <;>
    simp only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num <;> ring

set_option maxHeartbeats 1000000 in
/-- All20 original raw rows in fixed column1, including its eight zeros. -/
theorem jacobianEntry_flatBase_column_one (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 1 = JQ r 1 := by
  rw [jacobianEntry_ctx0 _ r 1 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_one_flatFrameP]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates,
      flat_pair_o01_imI, JQ, JZ] <;>
    simp only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num <;> ring

/-- Actual original derivative linear map on parameter axis0. -/
theorem rowLedgerDeriv_flatBase_column_zero (r : Fin 20) :
    rowLedgerDeriv ![flatFrameP, flatFrameQ, flatFrameR]
      (Pi.single (0 : Fin 20) 1) r = JQ r 0 := by
  rw [rowLedgerDeriv_single, jacobianEntry_flatBase_column_zero]

/-- Actual original derivative linear map on parameter axis1. -/
theorem rowLedgerDeriv_flatBase_column_one (r : Fin 20) :
    rowLedgerDeriv ![flatFrameP, flatFrameQ, flatFrameR]
      (Pi.single (1 : Fin 20) 1) r = JQ r 1 := by
  rw [rowLedgerDeriv_single, jacobianEntry_flatBase_column_one]

/- This internal chain rule adds no derivative equality hypothesis. It fixes
   the same original triple and consumes its written strict family derivative. -/
private theorem hasDerivAt_flatBase_axis (n r : Fin 20) :
    HasDerivAt
      (fun t : ℝ => rowLedger ![flatFrameP, flatFrameQ, flatFrameR]
        (Pi.single n t) r)
      (jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r n) 0 := by
  have hf : HasFDerivAt (rowLedger ![flatFrameP, flatFrameQ, flatFrameR])
      (rowLedgerDeriv ![flatFrameP, flatFrameQ, flatFrameR])
      (Pi.single n (0 : ℝ)) := by
    simpa only [Pi.single_zero] using
      (hasStrictFDerivAt_rowLedger ![flatFrameP, flatFrameQ, flatFrameR]).hasFDerivAt
  have ha := hf.comp_hasDerivAt (0 : ℝ) (hasDerivAt_single n (0 : ℝ))
  have hp : HasFDerivAt
      (ContinuousLinearMap.proj r : (Fin 20 → ℝ) →L[ℝ] ℝ)
      (ContinuousLinearMap.proj r : (Fin 20 → ℝ) →L[ℝ] ℝ)
      ((rowLedger ![flatFrameP, flatFrameQ, flatFrameR] ∘ Pi.single n) 0) :=
    (ContinuousLinearMap.proj r : (Fin 20 → ℝ) →L[ℝ] ℝ).hasFDerivAt
  have hr := hp.comp_hasDerivAt (0 : ℝ) ha
  simpa only [Function.comp_def, ContinuousLinearMap.proj_apply,
    rowLedgerDeriv_single] using hr

/-- Same exponential-family scalar derivatives, all20 rows of column0. -/
theorem hasDerivAt_flatBase_column_zero (r : Fin 20) :
    HasDerivAt
      (fun t : ℝ => rowLedger ![flatFrameP, flatFrameQ, flatFrameR]
        (Pi.single (0 : Fin 20) t) r)
      (JQ r 0) 0 := by
  simpa only [jacobianEntry_flatBase_column_zero] using
    hasDerivAt_flatBase_axis 0 r

/-- Same exponential-family scalar derivatives, all20 rows of column1. -/
theorem hasDerivAt_flatBase_column_one (r : Fin 20) :
    HasDerivAt
      (fun t : ℝ => rowLedger ![flatFrameP, flatFrameQ, flatFrameR]
        (Pi.single (1 : Fin 20) t) r)
      (JQ r 1) 0 := by
  simpa only [jacobianEntry_flatBase_column_one] using
    hasDerivAt_flatBase_axis 1 r

/-- Four ORIGINAL columns, eighty distinct entries, using columns2+3.
The other sixteen columns are not asserted here. -/
theorem jacobianEntry_flatBase_first_four (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 0 = JQ r 0 ∧
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 1 = JQ r 1 ∧
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 2 = JQ r 2 ∧
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 3 = JQ r 3 :=
  ⟨jacobianEntry_flatBase_column_zero r, jacobianEntry_flatBase_column_one r,
    Glennie.Compact.NativeFlatColumns23.jacobianEntry_flatBase_column_two r,
    Glennie.Compact.NativeFlatColumns23.jacobianEntry_flatBase_column_three r⟩

end
end Glennie.Compact.NativeFlatColumns01
