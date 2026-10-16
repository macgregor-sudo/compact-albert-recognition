/- Finite-coordinate representation for the native word table. -/
module
public import Glennie.Compact.NativeWordCoordinateBridgeR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators
set_option autoImplicit false

def word0 : Word := .unit
def value0 : Albert := nativeEval word0
def column0 : Fin 27 → ℝ := ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem value0_decode : value0 = decode column0 := by
  change (1 : Albert) = decode column0
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, column0, witnessX, witnessY, witnessZ, unit, octI, octK, octL, octJL, quatI, quatJ, quatK, octScalar, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

def word1 : Word := .mark 0
def value1 : Albert := nativeEval word1
def column1 : Fin 27 → ℝ := ![-1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem value1_decode : value1 = decode column1 := by
  change witnessX = decode column1
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, column1, witnessX, witnessY, witnessZ, unit, octI, octK, octL, octJL, quatI, quatJ, quatK, octScalar, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

def word2 : Word := .mark 1
def value2 : Albert := nativeEval word2
def column2 : Fin 27 → ℝ := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem value2_decode : value2 = decode column2 := by
  change witnessY = decode column2
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, column2, witnessX, witnessY, witnessZ, unit, octI, octK, octL, octJL, quatI, quatJ, quatK, octScalar, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

def word3 : Word := .mark 2
def value3 : Albert := nativeEval word3
def column3 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem value3_decode : value3 = decode column3 := by
  change witnessZ = decode column3
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, column3, witnessX, witnessY, witnessZ, unit, octI, octK, octL, octJL, quatI, quatJ, quatK, octScalar, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

def word4 : Word := .mul word1 word1
def value4 : Albert := nativeEval word4
def column4 : Fin 27 → ℝ := ![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem value4_decode : value4 = decode column4 := by
  change jordan value1 value1 = decode column4
  simp only [value1_decode, value1_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, column4, column1, witnessX, witnessY, witnessZ, unit, octI, octK, octL, octJL, quatI, quatJ, quatK, octScalar, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

def word5 : Word := .mul word1 word2
def value5 : Albert := nativeEval word5
def column5 : Fin 27 → ℝ := ![0, 0, 0, (-1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem value5_decode : value5 = decode column5 := by
  change jordan value1 value2 = decode column5
  simp only [value1_decode, value2_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, column5, column1, column2, witnessX, witnessY, witnessZ, unit, octI, octK, octL, octJL, quatI, quatJ, quatK, octScalar, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

def word6 : Word := .mul word1 word3
def value6 : Albert := nativeEval word6
def column6 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem value6_decode : value6 = decode column6 := by
  change jordan value1 value3 = decode column6
  simp only [value1_decode, value3_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, column6, column1, column3, witnessX, witnessY, witnessZ, unit, octI, octK, octL, octJL, quatI, quatJ, quatK, octScalar, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

def word7 : Word := .mul word2 word2
def value7 : Albert := nativeEval word7
def column7 : Fin 27 → ℝ := ![2, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem value7_decode : value7 = decode column7 := by
  change jordan value2 value2 = decode column7
  simp only [value2_decode, value2_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, column7, column2, witnessX, witnessY, witnessZ, unit, octI, octK, octL, octJL, quatI, quatJ, quatK, octScalar, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

def word8 : Word := .mul word2 word3
def value8 : Albert := nativeEval word8
def column8 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-1/2), 0, (-1/2), 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, (1/2), 0, 0, 0, 0, 0, (-1/2), 0, 0, (-1/2)]

set_option maxHeartbeats 2000000 in
theorem value8_decode : value8 = decode column8 := by
  change jordan value2 value3 = decode column8
  simp only [value2_decode, value3_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, column8, column2, column3, witnessX, witnessY, witnessZ, unit, octI, octK, octL, octJL, quatI, quatJ, quatK, octScalar, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

def word9 : Word := .mul word3 word3
def value9 : Albert := nativeEval word9
def column9 : Fin 27 → ℝ := ![2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem value9_decode : value9 = decode column9 := by
  change jordan value3 value3 = decode column9
  simp only [value3_decode, value3_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, column9, column3, witnessX, witnessY, witnessZ, unit, octI, octK, octL, octJL, quatI, quatJ, quatK, octScalar, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

def word10 : Word := .mul word1 word5
def value10 : Albert := nativeEval word10
def column10 : Fin 27 → ℝ := ![0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem value10_decode : value10 = decode column10 := by
  change jordan value1 value5 = decode column10
  simp only [value1_decode, value5_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, column10, column1, column5, witnessX, witnessY, witnessZ, unit, octI, octK, octL, octJL, quatI, quatJ, quatK, octScalar, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

def word11 : Word := .mul word1 word6
def value11 : Albert := nativeEval word11
def column11 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem value11_decode : value11 = decode column11 := by
  change jordan value1 value6 = decode column11
  simp only [value1_decode, value6_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, column11, column1, column6, witnessX, witnessY, witnessZ, unit, octI, octK, octL, octJL, quatI, quatJ, quatK, octScalar, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

def word12 : Word := .mul word1 word7
def value12 : Albert := nativeEval word12
def column12 : Fin 27 → ℝ := ![-2, 0, 2, 0, (-1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem value12_decode : value12 = decode column12 := by
  change jordan value1 value7 = decode column12
  simp only [value1_decode, value7_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, column12, column1, column7, witnessX, witnessY, witnessZ, unit, octI, octK, octL, octJL, quatI, quatJ, quatK, octScalar, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

def word13 : Word := .mul word1 word8
def value13 : Albert := nativeEval word13
def column13 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (1/4), 0, (1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, (-1/4)]

set_option maxHeartbeats 2000000 in
theorem value13_decode : value13 = decode column13 := by
  change jordan value1 value8 = decode column13
  simp only [value1_decode, value8_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, column13, column1, column8, witnessX, witnessY, witnessZ, unit, octI, octK, octL, octJL, quatI, quatJ, quatK, octScalar, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

def word14 : Word := .mul word1 word9
def value14 : Albert := nativeEval word14
def column14 : Fin 27 → ℝ := ![-2, 0, 2, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem value14_decode : value14 = decode column14 := by
  change jordan value1 value9 = decode column14
  simp only [value1_decode, value9_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, column14, column1, column9, witnessX, witnessY, witnessZ, unit, octI, octK, octL, octJL, quatI, quatJ, quatK, octScalar, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

def word15 : Word := .mul word2 word6
def value15 : Albert := nativeEval word15
def column15 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, (1/4)]

set_option maxHeartbeats 2000000 in
theorem value15_decode : value15 = decode column15 := by
  change jordan value2 value6 = decode column15
  simp only [value2_decode, value6_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, column15, column2, column6, witnessX, witnessY, witnessZ, unit, octI, octK, octL, octJL, quatI, quatJ, quatK, octScalar, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

def word16 : Word := .mul word2 word8
def value16 : Albert := nativeEval word16
def column16 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (-1/4), 0, (1/4), (1/2), 0, 0, 0, (-1/4), 0, (-1/2), 0, 0, (-1/4), 0, 0, 0, (-1/2), 0, (-1/4), (1/4), 0]

set_option maxHeartbeats 2000000 in
theorem value16_decode : value16 = decode column16 := by
  change jordan value2 value8 = decode column16
  simp only [value2_decode, value8_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, column16, column2, column8, witnessX, witnessY, witnessZ, unit, octI, octK, octL, octJL, quatI, quatJ, quatK, octScalar, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

def word17 : Word := .mul word2 word9
def value17 : Albert := nativeEval word17
def column17 : Fin 27 → ℝ := ![0, 0, 0, 2, 0, 0, (1/2), 0, (1/2), 0, 0, 0, 2, (-1/2), 0, 0, 0, 0, (1/2), 2, 0, 0, 0, 0, (1/2), (1/2), 0]

set_option maxHeartbeats 2000000 in
theorem value17_decode : value17 = decode column17 := by
  change jordan value2 value9 = decode column17
  simp only [value2_decode, value9_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, column17, column2, column9, witnessX, witnessY, witnessZ, unit, octI, octK, octL, octJL, quatI, quatJ, quatK, octScalar, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

def word18 : Word := .mul word4 word7
def value18 : Albert := nativeEval word18
def column18 : Fin 27 → ℝ := ![2, 0, 2, 0, (1/2), 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem value18_decode : value18 = decode column18 := by
  change jordan value4 value7 = decode column18
  simp only [value4_decode, value7_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, column18, column4, column7, witnessX, witnessY, witnessZ, unit, octI, octK, octL, octJL, quatI, quatJ, quatK, octScalar, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

def word19 : Word := .mul word4 word8
def value19 : Albert := nativeEval word19
def column19 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-1/4), 0, (-1/4), 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, (1/2), 0, 0, 0, 0, 0, (-1/4), 0, 0, (-1/4)]

set_option maxHeartbeats 2000000 in
theorem value19_decode : value19 = decode column19 := by
  change jordan value4 value8 = decode column19
  simp only [value4_decode, value8_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, column19, column4, column8, witnessX, witnessY, witnessZ, unit, octI, octK, octL, octJL, quatI, quatJ, quatK, octScalar, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

def word20 : Word := .mul word4 word9
def value20 : Albert := nativeEval word20
def column20 : Fin 27 → ℝ := ![2, 0, 2, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem value20_decode : value20 = decode column20 := by
  change jordan value4 value9 = decode column20
  simp only [value4_decode, value9_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, column20, column4, column9, witnessX, witnessY, witnessZ, unit, octI, octK, octL, octJL, quatI, quatJ, quatK, octScalar, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

def word21 : Word := .mul word5 word8
def value21 : Albert := nativeEval word21
def column21 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (-1/8), 0, 0, (1/8), 0, 0, 0, (-1/8), 0, 0, 0, 0, (1/8), 0, 0, 0, (1/8), 0, 0, (-1/8), 0]

set_option maxHeartbeats 2000000 in
theorem value21_decode : value21 = decode column21 := by
  change jordan value5 value8 = decode column21
  simp only [value5_decode, value8_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, column21, column5, column8, witnessX, witnessY, witnessZ, unit, octI, octK, octL, octJL, quatI, quatJ, quatK, octScalar, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

def word22 : Word := .mul word5 word9
def value22 : Albert := nativeEval word22
def column22 : Fin 27 → ℝ := ![0, 0, 0, -1, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, (1/4), 0, 0, 0, 0, (1/4), 1, 0, 0, 0, 0, (-1/4), 0, 0]

set_option maxHeartbeats 2000000 in
theorem value22_decode : value22 = decode column22 := by
  change jordan value5 value9 = decode column22
  simp only [value5_decode, value9_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, column22, column5, column9, witnessX, witnessY, witnessZ, unit, octI, octK, octL, octJL, quatI, quatJ, quatK, octScalar, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

def word23 : Word := .mul word7 word9
def value23 : Albert := nativeEval word23
def column23 : Fin 27 → ℝ := ![4, 4, 4, 0, 2, (1/2), 0, (-1/2), 0, 0, 2, 2, 0, 0, (-1/2), 0, 2, (-1/2), 0, 0, 2, -2, 0, (1/2), 0, 0, (-1/2)]

set_option maxHeartbeats 2000000 in
theorem value23_decode : value23 = decode column23 := by
  change jordan value7 value9 = decode column23
  simp only [value7_decode, value9_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, column23, column7, column9, witnessX, witnessY, witnessZ, unit, octI, octK, octL, octJL, quatI, quatJ, quatK, octScalar, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

def word24 : Word := .mul word1 word15
def value24 : Albert := nativeEval word24
def column24 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (1/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/8)]

set_option maxHeartbeats 2000000 in
theorem value24_decode : value24 = decode column24 := by
  change jordan value1 value15 = decode column24
  simp only [value1_decode, value15_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, column24, column1, column15, witnessX, witnessY, witnessZ, unit, octI, octK, octL, octJL, quatI, quatJ, quatK, octScalar, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

def word25 : Word := .mul word1 word16
def value25 : Albert := nativeEval word25
def column25 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (1/8), 0, (-1/8), (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, (-1/8), (1/8), 0]

set_option maxHeartbeats 2000000 in
theorem value25_decode : value25 = decode column25 := by
  change jordan value1 value16 = decode column25
  simp only [value1_decode, value16_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, column25, column1, column16, witnessX, witnessY, witnessZ, unit, octI, octK, octL, octJL, quatI, quatJ, quatK, octScalar, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

def word26 : Word := .mul word1 word17
def value26 : Albert := nativeEval word26
def column26 : Fin 27 → ℝ := ![0, 0, 0, -1, 0, 0, (-1/4), 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, (1/4), (1/4), 0]

set_option maxHeartbeats 2000000 in
theorem value26_decode : value26 = decode column26 := by
  change jordan value1 value17 = decode column26
  simp only [value1_decode, value17_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, column26, column1, column17, witnessX, witnessY, witnessZ, unit, octI, octK, octL, octJL, quatI, quatJ, quatK, octScalar, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

def words : Fin 27 → Word := ![word0, word1, word2, word3, word4, word5, word6, word7, word8, word9, word10, word11, word12, word13, word14, word15, word16, word17, word18, word19, word20, word21, word22, word23, word24, word25, word26]
def nativeWords (i : Fin 27) : Albert := nativeEval (words i)
def columns : Fin 27 → Fin 27 → ℝ := ![column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26]

theorem nativeWords_unit : nativeWords 0 = 1 := rfl
theorem nativeWords_markX : nativeWords 1 = witnessX := rfl
theorem nativeWords_markY : nativeWords 2 = witnessY := rfl
theorem nativeWords_markZ : nativeWords 3 = witnessZ := rfl

theorem nativeWords_decode (i : Fin 27) : nativeWords i = decode (columns i) := by
  fin_cases i
  · exact value0_decode
  · exact value1_decode
  · exact value2_decode
  · exact value3_decode
  · exact value4_decode
  · exact value5_decode
  · exact value6_decode
  · exact value7_decode
  · exact value8_decode
  · exact value9_decode
  · exact value10_decode
  · exact value11_decode
  · exact value12_decode
  · exact value13_decode
  · exact value14_decode
  · exact value15_decode
  · exact value16_decode
  · exact value17_decode
  · exact value18_decode
  · exact value19_decode
  · exact value20_decode
  · exact value21_decode
  · exact value22_decode
  · exact value23_decode
  · exact value24_decode
  · exact value25_decode
  · exact value26_decode

theorem nativeWords_coordinates (i : Fin 27) : flatCoordinates (nativeWords i) = columns i := by
  change encode (nativeWords i) = columns i
  rw [nativeWords_decode, encode_decode]

end
end Glennie.Compact.NativeWordTableR01
