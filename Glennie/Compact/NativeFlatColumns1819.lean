/- Exactly final original FlatBase columns18/19, all Fin20 raw rows including zeros.
   Actual basis13/14 are NEGATIVE upper J/K in slot01; BOTH contexts are1.
   Whole Q tangents occupy upper J/K slots02/12, preserving both native words,
   HALF commutator, all20 moving parameters and original three-term chart.
   No desired Jacobian/derivative/trace/rank premise or replacement family. -/
module

public import Glennie.Compact.FlatBase
public import Glennie.Compact.Rank20Reduction
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Linear

@[expose] public section

namespace Glennie.Compact.NativeFlatColumns1819

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

set_option maxHeartbeats 1000000 in
private theorem direction_eighteen_flatFrameQ (j : Fin 3) :
    direction 18 (flatFrameQ j) =
      ![(⟨0, 0, 0, 0,
          ((⟨0, 0, flatScale / 4, -1 / 12⟩ : Quaternion ℝ), 0),
          ((⟨0, 0, -1 / 12, flatScale / 4⟩ : Quaternion ℝ), 0)⟩ : Glennie.Albert),
        ⟨0, 0, 0, 0,
          ((⟨0, 0, 0, 1 / 6⟩ : Quaternion ℝ), 0),
          ((⟨0, 0, 1 / 6, 0⟩ : Quaternion ℝ), 0)⟩,
        ⟨0, 0, 0, 0,
          ((⟨0, 0, -flatScale / 4, -1 / 12⟩ : Quaternion ℝ), 0),
          ((⟨0, 0, -1 / 12, -flatScale / 4⟩ : Quaternion ℝ), 0)⟩] j := by
  have hp : partnerIndex (18 : Fin 20) = 13 := rfl
  rw [direction, hp, extDecode_extUnit_1, extDecode_extUnit_13,
    Glennie.Compact.innerDerLinear_apply, flatFrameQ_literal j]
  fin_cases j <;> ext <;>
    norm_num [Glennie.Compact.innerDer, diagonalAlbert, archivalHiddenBasis,
      hiddenAlbert, hiddenOct, jordan_d0, jordan_d1, jordan_d2,
      jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octNormSq, Quaternion.normSq_def', octMul, octConj, octScalar,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;>
    simp -failIfUnchanged only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num <;> ring

set_option maxHeartbeats 1000000 in
private theorem direction_nineteen_flatFrameQ (j : Fin 3) :
    direction 19 (flatFrameQ j) =
      ![(⟨0, 0, 0, 0,
          ((⟨0, 0, 1 / 12, flatScale / 4⟩ : Quaternion ℝ), 0),
          ((⟨0, 0, -flatScale / 4, -1 / 12⟩ : Quaternion ℝ), 0)⟩ : Glennie.Albert),
        ⟨0, 0, 0, 0,
          ((⟨0, 0, -1 / 6, 0⟩ : Quaternion ℝ), 0),
          ((⟨0, 0, 0, 1 / 6⟩ : Quaternion ℝ), 0)⟩,
        ⟨0, 0, 0, 0,
          ((⟨0, 0, 1 / 12, -flatScale / 4⟩ : Quaternion ℝ), 0),
          ((⟨0, 0, flatScale / 4, -1 / 12⟩ : Quaternion ℝ), 0)⟩] j := by
  have hp : partnerIndex (19 : Fin 20) = 14 := rfl
  rw [direction, hp, extDecode_extUnit_1, extDecode_extUnit_14,
    Glennie.Compact.innerDerLinear_apply, flatFrameQ_literal j]
  fin_cases j <;> ext <;>
    norm_num [Glennie.Compact.innerDer, diagonalAlbert, archivalHiddenBasis,
      hiddenAlbert, hiddenOct, jordan_d0, jordan_d1, jordan_d2,
      jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octNormSq, Quaternion.normSq_def', octMul, octConj, octScalar,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;>
    simp -failIfUnchanged only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num <;> ring

/- All nine P/R slot02 upper quaternions are zero. Both native mixed
   words vanish because P is diagonal; the actual R02 is lower quaternion. -/
private theorem flat_pair_o02_upper_zero (i k : Fin 3) :
    (jordan (flatFrameP i) (flatFrameR k)).o02.1 = 0 := by
  rw [flatFrameP_literal i, flatFrameR_literal k]
  fin_cases i <;> fin_cases k <;> ext <;>
    norm_num [diagonalAlbert, jordan_o02, octMul,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul]

/- All nine whole P/R slot12 upper quaternions: both J/K projections
   are retained, including the whole zero i2 row. -/
private theorem flat_pair_o12_upper_JK (i k : Fin 3) :
    (jordan (flatFrameP i) (flatFrameR k)).o12.1 =
      ![![(⟨0, 0, -1 / 12, flatScale / 4⟩ : Quaternion ℝ),
          ⟨0, 0, 1 / 6, 0⟩, ⟨0, 0, -1 / 12, -flatScale / 4⟩],
        ![⟨0, 0, -1 / 12, flatScale / 4⟩,
          ⟨0, 0, 1 / 6, 0⟩, ⟨0, 0, -1 / 12, -flatScale / 4⟩],
        ![0, 0, 0]] i k := by
  rw [flatFrameP_literal i, flatFrameR_literal k]
  fin_cases i <;> fin_cases k <;> ext <;>
    norm_num [diagonalAlbert, jordan_o12, octMul, octConj,
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
/-- All20 original raw rows of column18, including its four zeros. -/
theorem jacobianEntry_flatBase_column_eighteen (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 18 = JQ r 18 := by
  rw [jacobianEntry_ctx1 _ r 18 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_eighteen_flatFrameQ]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates,
      flat_pair_o02_upper_zero, flat_pair_o12_upper_JK, JQ, JZ] <;>
    ring_nf <;> norm_num [flatScale_sq] <;>
    simp -failIfUnchanged only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num

set_option maxHeartbeats 1000000 in
/-- All20 original raw rows of column19, including its eight zeros. -/
theorem jacobianEntry_flatBase_column_nineteen (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 19 = JQ r 19 := by
  rw [jacobianEntry_ctx1 _ r 19 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_nineteen_flatFrameQ]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates,
      flat_pair_o02_upper_zero, flat_pair_o12_upper_JK,
      flatScale_eq_sqrt3_div_three, JQ, JZ] <;>
    simp -failIfUnchanged only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num <;> ring

/-- Same actual original derivative, on its parameter axis18. -/
theorem rowLedgerDeriv_flatBase_column_eighteen (r : Fin 20) :
    rowLedgerDeriv ![flatFrameP, flatFrameQ, flatFrameR]
      (Pi.single (18 : Fin 20) 1) r = JQ r 18 := by
  rw [rowLedgerDeriv_single, jacobianEntry_flatBase_column_eighteen]

/-- Same actual original derivative, on its parameter axis19. -/
theorem rowLedgerDeriv_flatBase_column_nineteen (r : Fin 20) :
    rowLedgerDeriv ![flatFrameP, flatFrameQ, flatFrameR]
      (Pi.single (19 : Fin 20) 1) r = JQ r 19 := by
  rw [rowLedgerDeriv_single, jacobianEntry_flatBase_column_nineteen]

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

/-- Same original exponential-family derivatives in column18, all20 rows. -/
theorem hasDerivAt_flatBase_column_eighteen (r : Fin 20) :
    HasDerivAt
      (fun t : ℝ => rowLedger ![flatFrameP, flatFrameQ, flatFrameR]
        (Pi.single (18 : Fin 20) t) r)
      (JQ r 18) 0 := by
  simpa only [jacobianEntry_flatBase_column_eighteen] using
    hasDerivAt_flatBase_axis 18 r

/-- Same original exponential-family derivatives in column19, all20 rows. -/
theorem hasDerivAt_flatBase_column_nineteen (r : Fin 20) :
    HasDerivAt
      (fun t : ℝ => rowLedger ![flatFrameP, flatFrameQ, flatFrameR]
        (Pi.single (19 : Fin 20) t) r)
      (JQ r 19) 0 := by
  simpa only [jacobianEntry_flatBase_column_nineteen] using
    hasDerivAt_flatBase_axis 19 r

end
end Glennie.Compact.NativeFlatColumns1819
