/- Literal raw Gram matrix for the native 27-word basis. -/
module
public import Glennie.Compact.NativeWordTableBasisR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Module Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def rawGramData : Matrix (Fin 27) (Fin 27) ℝ := ![
![3, 0, 0, 0, 2, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 4, 0, 0, 12, 0, 0, 0],
![0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
![0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0],
![0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
![2, 0, 0, 0, 2, 0, 0, 4, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 4, 0, 0, 8, 0, 0, 0],
![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2],
![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, (1/2), 0],
![6, 0, 0, 0, 4, 0, 0, 18, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 8, 0, 0, 36, 0, 0, 0],
![0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, (-1/4), 0, 0],
![6, 0, 0, 0, 4, 0, 0, 12, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 12, 0, 0, 36, 0, 0, 0],
![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
![0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
![0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, (1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
![0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, (9/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
![0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 27, 0, 0, 0, 0, 0, 0, 0, 0, 0],
![4, 0, 0, 0, 4, 0, 0, 12, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 8, 0, 0, 24, 0, 0, 0],
![0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (3/2), 0, 0, 0, 0, (-1/8), 0, 0],
![4, 0, 0, 0, 4, 0, 0, 8, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 11, 0, 0, 24, 0, 0, 0],
![0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (3/16), 0, 0, 0, (-3/16), 0],
![0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (9/2), 0, 0, 0, (15/4)],
![12, 0, 0, 0, 8, 0, 0, 36, 0, 36, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 24, 0, 0, 99, 0, 0, 0],
![0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/8), 0, 0, 0, 0, (1/16), 0, 0],
![0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-3/16), 0, 0, 0, (3/8), 0],
![0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (15/4), 0, 0, 0, (9/2)]
]

set_option maxHeartbeats 2000000 in
theorem rawGram_row0 (j : Fin 27) :
    inner (nativeWords 0) (nativeWords j) = rawGramData 0 j := by
  fin_cases j <;> simp only [nativeWords_decode] <;> norm_num [rawGramData, inner_coordinates, octDot_coordinates, decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, octNormSq, Quaternion.normSq_def']

set_option maxHeartbeats 2000000 in
theorem rawGram_row1 (j : Fin 27) :
    inner (nativeWords 1) (nativeWords j) = rawGramData 1 j := by
  fin_cases j <;> simp only [nativeWords_decode] <;> norm_num [rawGramData, inner_coordinates, octDot_coordinates, decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, octNormSq, Quaternion.normSq_def']

set_option maxHeartbeats 2000000 in
theorem rawGram_row2 (j : Fin 27) :
    inner (nativeWords 2) (nativeWords j) = rawGramData 2 j := by
  fin_cases j <;> simp only [nativeWords_decode] <;> norm_num [rawGramData, inner_coordinates, octDot_coordinates, decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, octNormSq, Quaternion.normSq_def']

set_option maxHeartbeats 2000000 in
theorem rawGram_row3 (j : Fin 27) :
    inner (nativeWords 3) (nativeWords j) = rawGramData 3 j := by
  fin_cases j <;> simp only [nativeWords_decode] <;> norm_num [rawGramData, inner_coordinates, octDot_coordinates, decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, octNormSq, Quaternion.normSq_def']

set_option maxHeartbeats 2000000 in
theorem rawGram_row4 (j : Fin 27) :
    inner (nativeWords 4) (nativeWords j) = rawGramData 4 j := by
  fin_cases j <;> simp only [nativeWords_decode] <;> norm_num [rawGramData, inner_coordinates, octDot_coordinates, decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, octNormSq, Quaternion.normSq_def']

set_option maxHeartbeats 2000000 in
theorem rawGram_row5 (j : Fin 27) :
    inner (nativeWords 5) (nativeWords j) = rawGramData 5 j := by
  fin_cases j <;> simp only [nativeWords_decode] <;> norm_num [rawGramData, inner_coordinates, octDot_coordinates, decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, octNormSq, Quaternion.normSq_def']

set_option maxHeartbeats 2000000 in
theorem rawGram_row6 (j : Fin 27) :
    inner (nativeWords 6) (nativeWords j) = rawGramData 6 j := by
  fin_cases j <;> simp only [nativeWords_decode] <;> norm_num [rawGramData, inner_coordinates, octDot_coordinates, decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, octNormSq, Quaternion.normSq_def']

set_option maxHeartbeats 2000000 in
theorem rawGram_row7 (j : Fin 27) :
    inner (nativeWords 7) (nativeWords j) = rawGramData 7 j := by
  fin_cases j <;> simp only [nativeWords_decode] <;> norm_num [rawGramData, inner_coordinates, octDot_coordinates, decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, octNormSq, Quaternion.normSq_def']

set_option maxHeartbeats 2000000 in
theorem rawGram_row8 (j : Fin 27) :
    inner (nativeWords 8) (nativeWords j) = rawGramData 8 j := by
  fin_cases j <;> simp only [nativeWords_decode] <;> norm_num [rawGramData, inner_coordinates, octDot_coordinates, decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, octNormSq, Quaternion.normSq_def']

set_option maxHeartbeats 2000000 in
theorem rawGram_row9 (j : Fin 27) :
    inner (nativeWords 9) (nativeWords j) = rawGramData 9 j := by
  fin_cases j <;> simp only [nativeWords_decode] <;> norm_num [rawGramData, inner_coordinates, octDot_coordinates, decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, octNormSq, Quaternion.normSq_def']

set_option maxHeartbeats 2000000 in
theorem rawGram_row10 (j : Fin 27) :
    inner (nativeWords 10) (nativeWords j) = rawGramData 10 j := by
  fin_cases j <;> simp only [nativeWords_decode] <;> norm_num [rawGramData, inner_coordinates, octDot_coordinates, decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, octNormSq, Quaternion.normSq_def']

set_option maxHeartbeats 2000000 in
theorem rawGram_row11 (j : Fin 27) :
    inner (nativeWords 11) (nativeWords j) = rawGramData 11 j := by
  fin_cases j <;> simp only [nativeWords_decode] <;> norm_num [rawGramData, inner_coordinates, octDot_coordinates, decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, octNormSq, Quaternion.normSq_def']

set_option maxHeartbeats 2000000 in
theorem rawGram_row12 (j : Fin 27) :
    inner (nativeWords 12) (nativeWords j) = rawGramData 12 j := by
  fin_cases j <;> simp only [nativeWords_decode] <;> norm_num [rawGramData, inner_coordinates, octDot_coordinates, decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, octNormSq, Quaternion.normSq_def']

set_option maxHeartbeats 2000000 in
theorem rawGram_row13 (j : Fin 27) :
    inner (nativeWords 13) (nativeWords j) = rawGramData 13 j := by
  fin_cases j <;> simp only [nativeWords_decode] <;> norm_num [rawGramData, inner_coordinates, octDot_coordinates, decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, octNormSq, Quaternion.normSq_def']

set_option maxHeartbeats 2000000 in
theorem rawGram_row14 (j : Fin 27) :
    inner (nativeWords 14) (nativeWords j) = rawGramData 14 j := by
  fin_cases j <;> simp only [nativeWords_decode] <;> norm_num [rawGramData, inner_coordinates, octDot_coordinates, decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, octNormSq, Quaternion.normSq_def']

set_option maxHeartbeats 2000000 in
theorem rawGram_row15 (j : Fin 27) :
    inner (nativeWords 15) (nativeWords j) = rawGramData 15 j := by
  fin_cases j <;> simp only [nativeWords_decode] <;> norm_num [rawGramData, inner_coordinates, octDot_coordinates, decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, octNormSq, Quaternion.normSq_def']

set_option maxHeartbeats 2000000 in
theorem rawGram_row16 (j : Fin 27) :
    inner (nativeWords 16) (nativeWords j) = rawGramData 16 j := by
  fin_cases j <;> simp only [nativeWords_decode] <;> norm_num [rawGramData, inner_coordinates, octDot_coordinates, decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, octNormSq, Quaternion.normSq_def']

set_option maxHeartbeats 2000000 in
theorem rawGram_row17 (j : Fin 27) :
    inner (nativeWords 17) (nativeWords j) = rawGramData 17 j := by
  fin_cases j <;> simp only [nativeWords_decode] <;> norm_num [rawGramData, inner_coordinates, octDot_coordinates, decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, octNormSq, Quaternion.normSq_def']

set_option maxHeartbeats 2000000 in
theorem rawGram_row18 (j : Fin 27) :
    inner (nativeWords 18) (nativeWords j) = rawGramData 18 j := by
  fin_cases j <;> simp only [nativeWords_decode] <;> norm_num [rawGramData, inner_coordinates, octDot_coordinates, decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, octNormSq, Quaternion.normSq_def']

set_option maxHeartbeats 2000000 in
theorem rawGram_row19 (j : Fin 27) :
    inner (nativeWords 19) (nativeWords j) = rawGramData 19 j := by
  fin_cases j <;> simp only [nativeWords_decode] <;> norm_num [rawGramData, inner_coordinates, octDot_coordinates, decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, octNormSq, Quaternion.normSq_def']

set_option maxHeartbeats 2000000 in
theorem rawGram_row20 (j : Fin 27) :
    inner (nativeWords 20) (nativeWords j) = rawGramData 20 j := by
  fin_cases j <;> simp only [nativeWords_decode] <;> norm_num [rawGramData, inner_coordinates, octDot_coordinates, decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, octNormSq, Quaternion.normSq_def']

set_option maxHeartbeats 2000000 in
theorem rawGram_row21 (j : Fin 27) :
    inner (nativeWords 21) (nativeWords j) = rawGramData 21 j := by
  fin_cases j <;> simp only [nativeWords_decode] <;> norm_num [rawGramData, inner_coordinates, octDot_coordinates, decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, octNormSq, Quaternion.normSq_def']

set_option maxHeartbeats 2000000 in
theorem rawGram_row22 (j : Fin 27) :
    inner (nativeWords 22) (nativeWords j) = rawGramData 22 j := by
  fin_cases j <;> simp only [nativeWords_decode] <;> norm_num [rawGramData, inner_coordinates, octDot_coordinates, decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, octNormSq, Quaternion.normSq_def']

set_option maxHeartbeats 2000000 in
theorem rawGram_row23 (j : Fin 27) :
    inner (nativeWords 23) (nativeWords j) = rawGramData 23 j := by
  fin_cases j <;> simp only [nativeWords_decode] <;> norm_num [rawGramData, inner_coordinates, octDot_coordinates, decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, octNormSq, Quaternion.normSq_def']

set_option maxHeartbeats 2000000 in
theorem rawGram_row24 (j : Fin 27) :
    inner (nativeWords 24) (nativeWords j) = rawGramData 24 j := by
  fin_cases j <;> simp only [nativeWords_decode] <;> norm_num [rawGramData, inner_coordinates, octDot_coordinates, decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, octNormSq, Quaternion.normSq_def']

set_option maxHeartbeats 2000000 in
theorem rawGram_row25 (j : Fin 27) :
    inner (nativeWords 25) (nativeWords j) = rawGramData 25 j := by
  fin_cases j <;> simp only [nativeWords_decode] <;> norm_num [rawGramData, inner_coordinates, octDot_coordinates, decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, octNormSq, Quaternion.normSq_def']

set_option maxHeartbeats 2000000 in
theorem rawGram_row26 (j : Fin 27) :
    inner (nativeWords 26) (nativeWords j) = rawGramData 26 j := by
  fin_cases j <;> simp only [nativeWords_decode] <;> norm_num [rawGramData, inner_coordinates, octDot_coordinates, decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, octNormSq, Quaternion.normSq_def']

theorem rawGram_native (i j : Fin 27) :
    inner (nativeWords i) (nativeWords j) = rawGramData i j := by
  fin_cases i
  · exact rawGram_row0 j
  · exact rawGram_row1 j
  · exact rawGram_row2 j
  · exact rawGram_row3 j
  · exact rawGram_row4 j
  · exact rawGram_row5 j
  · exact rawGram_row6 j
  · exact rawGram_row7 j
  · exact rawGram_row8 j
  · exact rawGram_row9 j
  · exact rawGram_row10 j
  · exact rawGram_row11 j
  · exact rawGram_row12 j
  · exact rawGram_row13 j
  · exact rawGram_row14 j
  · exact rawGram_row15 j
  · exact rawGram_row16 j
  · exact rawGram_row17 j
  · exact rawGram_row18 j
  · exact rawGram_row19 j
  · exact rawGram_row20 j
  · exact rawGram_row21 j
  · exact rawGram_row22 j
  · exact rawGram_row23 j
  · exact rawGram_row24 j
  · exact rawGram_row25 j
  · exact rawGram_row26 j

def rawForm : Albert →ₗ[ℝ] Albert →ₗ[ℝ] ℝ where
  toFun x :=
    { toFun := inner x
      map_add' y z := inner_add_right x y z
      map_smul' r y := inner_smul_right r x y }
  map_add' x y := by ext z; exact inner_add_left x y z
  map_smul' r x := by ext z; exact inner_smul_left r x z

theorem raw_inner_sum_left (c : Fin 27 → ℝ) (v : Fin 27 → Albert) (y : Albert) :
    inner (∑ i, c i • v i) y = ∑ i, c i * inner (v i) y := by
  change (rawForm.flip y) (∑ i, c i • v i) = _
  simp only [map_sum, map_smul, LinearMap.flip_apply, smul_eq_mul]
  all_goals rfl

theorem raw_inner_sum_right (x : Albert) (c : Fin 27 → ℝ) (v : Fin 27 → Albert) :
    inner x (∑ i, c i • v i) = ∑ i, c i * inner x (v i) := by
  change (rawForm x) (∑ i, c i • v i) = _
  simp only [map_sum, map_smul, smul_eq_mul]
  all_goals rfl

theorem raw_inner_word_sums (c d : Fin 27 → ℝ) :
    inner (∑ i, c i • nativeWords i) (∑ j, d j • nativeWords j) =
      ∑ i, ∑ j, c i * d j * rawGramData i j := by
  rw [raw_inner_sum_left]
  apply Finset.sum_congr rfl
  intro i hi
  rw [raw_inner_sum_right, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [rawGram_native]
  ring

/-- Positivity is derived from actual native independence and trace positivity.
    It is not a determinant sign or assumed certificate field. -/
theorem rawGram_positive (c : Fin 27 → ℝ) (hc : c ≠ 0) :
    0 < ∑ i, ∑ j, c i * c j * rawGramData i j := by
  rw [← raw_inner_word_sums]
  have hs : (∑ i, c i • nativeWords i) ≠ 0 := by
    intro hz
    apply hc
    funext i
    exact (Fintype.linearIndependent_iff.mp nativeWords_linearIndependent) c hz i
  have hn : inner (∑ i, c i • nativeWords i) (∑ i, c i • nativeWords i) ≠ 0 :=
    fun hz => hs ((inner_self_eq_zero _).mp hz)
  exact lt_of_le_of_ne (inner_self_nonneg _) (Ne.symm hn)

end
end Glennie.Compact.NativeWordTableR01
