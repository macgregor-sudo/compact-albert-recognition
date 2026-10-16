/- Exactly original FlatBase columns4 and5, every Fin20 raw row including zeros.
   Full-basis9/10 decode to negative upper J/K in slot12; native HALF ordered
   commutators and actual projector coordinates precede JQ comparison.
   No desired derivative/Jacobian/trace/rank premise or replacement family. -/
module

public import Glennie.Compact.FlatBase
public import Glennie.Compact.Rank20Reduction
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Linear

@[expose] public section

namespace Glennie.Compact.NativeFlatColumns45

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
private theorem direction_four_flatFrameP (i : Fin 3) :
    direction 4 (flatFrameP i) =
      ![(⟨0, 0, 0, 0, 0,
          ((⟨0, 0, 1 / 4, 0⟩ : Quaternion ℝ), 0)⟩ : Glennie.Albert),
        ⟨0, 0, 0, 0, 0,
          ((⟨0, 0, -1 / 4, 0⟩ : Quaternion ℝ), 0)⟩,
        0] i := by
  have hp : partnerIndex (4 : Fin 20) = 9 := rfl
  rw [direction, hp, extDecode_extUnit_1, extDecode_extUnit_9,
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
private theorem direction_five_flatFrameP (i : Fin 3) :
    direction 5 (flatFrameP i) =
      ![(⟨0, 0, 0, 0, 0,
          ((⟨0, 0, 0, 1 / 4⟩ : Quaternion ℝ), 0)⟩ : Glennie.Albert),
        ⟨0, 0, 0, 0, 0,
          ((⟨0, 0, 0, -1 / 4⟩ : Quaternion ℝ), 0)⟩,
        0] i := by
  have hp : partnerIndex (5 : Fin 20) = 10 := rfl
  rw [direction, hp, extDecode_extUnit_1, extDecode_extUnit_10,
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

/- Private whole Q/R identities have no public API in the earlier modules.
   Their same literal projector proofs are restated, with the canonical native
   carrier explicit. No previous module, value table or certificate is a premise. -/
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

private theorem flat_pair_o12_imJ (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o12.1.imJ =
      ![(-1 / 18 : ℝ), 1 / 9, -1 / 18] k := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o12, octMul, octConj,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;> ring

private theorem flat_pair_o12_imK (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o12.1.imK =
      ![flatScale / 6, 0, -flatScale / 6] k := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o12, octMul, octConj,
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
/-- Every original raw row of column4, including its four zeros. -/
theorem jacobianEntry_flatBase_column_four (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 4 = JQ r 4 := by
  rw [jacobianEntry_ctx0 _ r 4 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_four_flatFrameP]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates,
      flat_pair_o12_imJ, JQ, JZ] <;>
    simp -failIfUnchanged only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num <;> ring

set_option maxHeartbeats 1000000 in
/-- Every original raw row of column5, including its ten zeros. -/
theorem jacobianEntry_flatBase_column_five (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 5 = JQ r 5 := by
  rw [jacobianEntry_ctx0 _ r 5 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_five_flatFrameP]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates,
      flat_pair_o12_imK, flatScale_eq_sqrt3_div_three, JQ, JZ] <;>
    simp -failIfUnchanged only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num <;> ring

/-- Actual rowLedger derivative on its original parameter axis4. -/
theorem rowLedgerDeriv_flatBase_column_four (r : Fin 20) :
    rowLedgerDeriv ![flatFrameP, flatFrameQ, flatFrameR]
      (Pi.single (4 : Fin 20) 1) r = JQ r 4 := by
  rw [rowLedgerDeriv_single, jacobianEntry_flatBase_column_four]

/-- Actual rowLedger derivative on its original parameter axis5. -/
theorem rowLedgerDeriv_flatBase_column_five (r : Fin 20) :
    rowLedgerDeriv ![flatFrameP, flatFrameQ, flatFrameR]
      (Pi.single (5 : Fin 20) 1) r = JQ r 5 := by
  rw [rowLedgerDeriv_single, jacobianEntry_flatBase_column_five]

/- Same existing original strict derivative and typed scalar-axis/projection
   chain rule; no supplied derivative value or invertibility hypothesis. -/
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

/-- Same actual exponential-family derivatives in column4, all20 rows. -/
theorem hasDerivAt_flatBase_column_four (r : Fin 20) :
    HasDerivAt
      (fun t : ℝ => rowLedger ![flatFrameP, flatFrameQ, flatFrameR]
        (Pi.single (4 : Fin 20) t) r)
      (JQ r 4) 0 := by
  simpa only [jacobianEntry_flatBase_column_four] using
    hasDerivAt_flatBase_axis 4 r

/-- Same actual exponential-family derivatives in column5, all20 rows. -/
theorem hasDerivAt_flatBase_column_five (r : Fin 20) :
    HasDerivAt
      (fun t : ℝ => rowLedger ![flatFrameP, flatFrameQ, flatFrameR]
        (Pi.single (5 : Fin 20) t) r)
      (JQ r 5) 0 := by
  simpa only [jacobianEntry_flatBase_column_five] using
    hasDerivAt_flatBase_axis 5 r

end
end Glennie.Compact.NativeFlatColumns45
