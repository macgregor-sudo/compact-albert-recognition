/- Exactly original FlatBase columns6 and7, every Fin20 raw row including zeros.
   Original full-basis11/12 are POSITIVE upper J/K in slot02. Their ordered
   HALF commutators and actual two-index Q/R product projections precede JQ.
   No desired Jacobian/derivative/trace/rank premise or replacement family. -/
module

public import Glennie.Compact.FlatBase
public import Glennie.Compact.Rank20Reduction
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Linear

@[expose] public section

namespace Glennie.Compact.NativeFlatColumns67

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
private theorem direction_six_flatFrameP (i : Fin 3) :
    direction 6 (flatFrameP i) =
      ![(⟨0, 0, 0, 0,
          ((⟨0, 0, 1 / 4, 0⟩ : Quaternion ℝ), 0), 0⟩ : Glennie.Albert),
        0,
        ⟨0, 0, 0, 0,
          ((⟨0, 0, -1 / 4, 0⟩ : Quaternion ℝ), 0), 0⟩] i := by
  have hp : partnerIndex (6 : Fin 20) = 11 := rfl
  rw [direction, hp, extDecode_extUnit_1, extDecode_extUnit_11,
    Glennie.Compact.innerDerLinear_apply, flatFrameP_literal i]
  fin_cases i <;> ext <;>
    norm_num [Glennie.Compact.innerDer, diagonalAlbert, archivalHiddenBasis,
      hiddenAlbert, hiddenOct, jordan_d0, jordan_d1, jordan_d2,
      jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octNormSq, Quaternion.normSq_def', octMul, octConj, octScalar,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;>
    simp -failIfUnchanged only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num

set_option maxHeartbeats 1000000 in
private theorem direction_seven_flatFrameP (i : Fin 3) :
    direction 7 (flatFrameP i) =
      ![(⟨0, 0, 0, 0,
          ((⟨0, 0, 0, 1 / 4⟩ : Quaternion ℝ), 0), 0⟩ : Glennie.Albert),
        0,
        ⟨0, 0, 0, 0,
          ((⟨0, 0, 0, -1 / 4⟩ : Quaternion ℝ), 0), 0⟩] i := by
  have hp : partnerIndex (7 : Fin 20) = 12 := rfl
  rw [direction, hp, extDecode_extUnit_1, extDecode_extUnit_12,
    Glennie.Compact.innerDerLinear_apply, flatFrameP_literal i]
  fin_cases i <;> ext <;>
    norm_num [Glennie.Compact.innerDer, diagonalAlbert, archivalHiddenBasis,
      hiddenAlbert, hiddenOct, jordan_d0, jordan_d1, jordan_d2,
      jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octNormSq, Quaternion.normSq_def', octMul, octConj, octScalar,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;>
    simp -failIfUnchanged only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num

/- Whole actual Q/R literals are rederived from their projector definitions.
   No earlier private helper or assumed coordinate/value table is imported. -/
private theorem flatFrameQ_literal (j : Fin 3) :
    flatFrameQ j =
      ![(⟨1 / 3, 1 / 3, 1 / 3,
          ((⟨-flatScale / 2, -1 / 6, 0, 0⟩ : Quaternion ℝ), 0),
          ((⟨1 / 6, flatScale / 2, 0, 0⟩ : Quaternion ℝ), 0),
          ((⟨-flatScale / 2, -1 / 6, 0, 0⟩ : Quaternion ℝ), 0)⟩ : Glennie.Albert),
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
          ((⟨0, 0, -1 / 6, flatScale / 2⟩ : Quaternion ℝ), 0)⟩ : Glennie.Albert),
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

private theorem flat_pair_o02_imJ (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o02.1.imJ =
      ![![flatScale / 12, -flatScale / 12, (0 : ℝ)],
        ![-flatScale / 12, 0, flatScale / 12],
        ![0, flatScale / 12, -flatScale / 12]] j k := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o02, octMul,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;> ring

private theorem flat_pair_o02_imK (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o02.1.imK =
      ![![(-1 / 36 : ℝ), -1 / 36, 1 / 18],
        ![-1 / 36, 1 / 18, -1 / 36],
        ![1 / 18, -1 / 36, -1 / 36]] j k := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o02, octMul,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;>
    ring_nf <;> norm_num [flatScale_sq]

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
/-- All20 original raw rows of column6, including its twelve zeros. -/
theorem jacobianEntry_flatBase_column_six (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 6 = JQ r 6 := by
  rw [jacobianEntry_ctx0 _ r 6 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_six_flatFrameP]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates,
      flat_pair_o02_imJ, flatScale_eq_sqrt3_div_three, JQ, JZ] <;>
    simp -failIfUnchanged only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num <;> ring

set_option maxHeartbeats 1000000 in
/-- All20 original raw rows of column7, including its eight zeros. -/
theorem jacobianEntry_flatBase_column_seven (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 7 = JQ r 7 := by
  rw [jacobianEntry_ctx0 _ r 7 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_seven_flatFrameP]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates,
      flat_pair_o02_imK, JQ, JZ] <;>
    simp -failIfUnchanged only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num <;> ring

/-- Same actual original derivative, on its parameter axis6. -/
theorem rowLedgerDeriv_flatBase_column_six (r : Fin 20) :
    rowLedgerDeriv ![flatFrameP, flatFrameQ, flatFrameR]
      (Pi.single (6 : Fin 20) 1) r = JQ r 6 := by
  rw [rowLedgerDeriv_single, jacobianEntry_flatBase_column_six]

/-- Same actual original derivative, on its parameter axis7. -/
theorem rowLedgerDeriv_flatBase_column_seven (r : Fin 20) :
    rowLedgerDeriv ![flatFrameP, flatFrameQ, flatFrameR]
      (Pi.single (7 : Fin 20) 1) r = JQ r 7 := by
  rw [rowLedgerDeriv_single, jacobianEntry_flatBase_column_seven]

/- Existing original strict derivative and typed scalar-axis/projection API,
   with no added desired derivative, velocity or invertibility premise. -/
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

/-- Same original exponential-family derivatives in column6, all20 rows. -/
theorem hasDerivAt_flatBase_column_six (r : Fin 20) :
    HasDerivAt
      (fun t : ℝ => rowLedger ![flatFrameP, flatFrameQ, flatFrameR]
        (Pi.single (6 : Fin 20) t) r)
      (JQ r 6) 0 := by
  simpa only [jacobianEntry_flatBase_column_six] using
    hasDerivAt_flatBase_axis 6 r

/-- Same original exponential-family derivatives in column7, all20 rows. -/
theorem hasDerivAt_flatBase_column_seven (r : Fin 20) :
    HasDerivAt
      (fun t : ℝ => rowLedger ![flatFrameP, flatFrameQ, flatFrameR]
        (Pi.single (7 : Fin 20) t) r)
      (JQ r 7) 0 := by
  simpa only [jacobianEntry_flatBase_column_seven] using
    hasDerivAt_flatBase_axis 7 r

end
end Glennie.Compact.NativeFlatColumns67
