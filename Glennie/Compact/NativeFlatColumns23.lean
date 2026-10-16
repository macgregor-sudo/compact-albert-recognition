/- Fixed original FlatBase columns2 and3, each with all20 raw rows including
   zeros. Native projector/CD/HALF coordinate bodies precede comparison with
   JQ; no desired Jacobian hypothesis or replacement family is supplied.
   The literal base below is definitionally Sections.flatBase. Importing
   Sections solely for that alias would add its separate IFT/reversal chain. -/
module

public import Glennie.Compact.FlatBase
public import Glennie.Compact.Rank20Reduction
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Linear

@[expose] public section

namespace Glennie.Compact.NativeFlatColumns23

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
private theorem direction_two_flatFrameP (i : Fin 3) :
    direction 2 (flatFrameP i) =
      ![(⟨0, 0, 0, 0, octScalar (1 / 4), 0⟩ : Albert),
        0, ⟨0, 0, 0, 0, octScalar (-1 / 4), 0⟩] i := by
  have hp : partnerIndex (2 : Fin 20) = 5 := rfl
  rw [direction, hp, extDecode_extUnit_1, extDecode_extUnit_5,
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
private theorem direction_three_flatFrameP (i : Fin 3) :
    direction 3 (flatFrameP i) =
      ![(⟨0, 0, 0, 0, ((⟨0, 1 / 4, 0, 0⟩ : Quaternion ℝ), 0), 0⟩ : Albert),
        0, ⟨0, 0, 0, 0, ((⟨0, -1 / 4, 0, 0⟩ : Quaternion ℝ), 0), 0⟩] i := by
  have hp : partnerIndex (3 : Fin 20) = 6 := rfl
  rw [direction, hp, extDecode_extUnit_1, extDecode_extUnit_6,
    Glennie.Compact.innerDerLinear_apply, flatFrameP_literal i]
  fin_cases i <;> ext <;>
    norm_num [Glennie.Compact.innerDer, diagonalAlbert, complexAlbert, complexOct,
      jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octNormSq, Quaternion.normSq_def', octMul, octConj, octScalar,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul]

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

private theorem flat_pair_o02_re (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o02.1.re =
      ![(1 / 18 : ℝ), -1 / 9, 1 / 18] j := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o02, octMul,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;> ring

private theorem flat_pair_o02_imI (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o02.1.imI =
      ![flatScale / 6, 0, -flatScale / 6] j := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o02, octMul,
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
/-- All20 original raw rows in fixed column2, including its eight zeros.
    The literal triple is exactly the original Sections.flatBase. -/
theorem jacobianEntry_flatBase_column_two (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 2 = JQ r 2 := by
  rw [jacobianEntry_ctx0 _ r 2 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_two_flatFrameP]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates, octScalar,
      flat_pair_o02_re, JQ, JZ] <;>
    simp only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num <;> ring

set_option maxHeartbeats 1000000 in
/-- All20 original raw rows in fixed column3, including its thirteen zeros.
    The scalar conversion uses the actual positive-root definition of flatScale. -/
theorem jacobianEntry_flatBase_column_three (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 3 = JQ r 3 := by
  rw [jacobianEntry_ctx0 _ r 3 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_three_flatFrameP]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates,
      flat_pair_o02_imI, flatScale_eq_sqrt3_div_three, JQ, JZ] <;> ring

/-- Same actual original rowLedger derivative, on its actual parameter axis2. -/
theorem rowLedgerDeriv_flatBase_column_two (r : Fin 20) :
    rowLedgerDeriv ![flatFrameP, flatFrameQ, flatFrameR]
      (Pi.single (2 : Fin 20) 1) r = JQ r 2 := by
  rw [rowLedgerDeriv_single, jacobianEntry_flatBase_column_two]

/-- Same actual original rowLedger derivative, on its actual parameter axis3. -/
theorem rowLedgerDeriv_flatBase_column_three (r : Fin 20) :
    rowLedgerDeriv ![flatFrameP, flatFrameQ, flatFrameR]
      (Pi.single (3 : Fin 20) 1) r = JQ r 3 := by
  rw [rowLedgerDeriv_single, jacobianEntry_flatBase_column_three]

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

/-- Actual exponential-family scalar derivatives in fixed column2, all20 rows. -/
theorem hasDerivAt_flatBase_column_two (r : Fin 20) :
    HasDerivAt
      (fun t : ℝ => rowLedger ![flatFrameP, flatFrameQ, flatFrameR]
        (Pi.single (2 : Fin 20) t) r)
      (JQ r 2) 0 := by
  simpa only [jacobianEntry_flatBase_column_two] using
    hasDerivAt_flatBase_axis 2 r

/-- Actual exponential-family scalar derivatives in fixed column3, all20 rows. -/
theorem hasDerivAt_flatBase_column_three (r : Fin 20) :
    HasDerivAt
      (fun t : ℝ => rowLedger ![flatFrameP, flatFrameQ, flatFrameR]
        (Pi.single (3 : Fin 20) t) r)
      (JQ r 3) 0 := by
  simpa only [jacobianEntry_flatBase_column_three] using
    hasDerivAt_flatBase_axis 3 r

end
end Glennie.Compact.NativeFlatColumns23
