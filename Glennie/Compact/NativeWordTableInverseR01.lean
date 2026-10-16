/- Explicit inverse of the selected native word-coordinate matrix. -/
module
public import Glennie.Compact.NativeWordTableCoordinatesR01
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def coordinateMatrix : Matrix (Fin 27) (Fin 27) ℝ := fun i j => columns j i

def inverseMatrix : Matrix (Fin 27) (Fin 27) ℝ := ![
![0, 1, 0, 0, -2, (4/3), 0, (-4/3), 0, 0, -2, 2, 0, 0, (-4/3), 0, 2, (-4/3), 0, 0, -2, 2, 0, (4/3), 0, 0, (-4/3)],
![(-1/2), 0, (1/2), 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0, 0, 0, 0],
![0, 0, 0, 0, 0, 0, (-2/3), 0, (-2/3), 0, 0, 0, 1, (2/3), 0, 0, 0, 0, (-2/3), 0, 0, 0, 0, 0, (-2/3), (-2/3), 0],
![0, 0, 0, 0, 0, 0, (1/3), 0, (-1/3), 0, 0, 0, 0, (1/3), 0, -1, 0, 0, (1/3), 0, 0, 0, 0, 0, (1/3), (-1/3), 0],
![(1/2), -1, (1/2), 0, 2, 0, 0, 0, 0, 0, 2, -4, 0, 0, 0, 0, -4, 0, 0, 0, 2, -2, 0, 0, 0, 0, 0],
![0, 0, 0, -1, 0, 0, 4, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 1, 0, 0, 0, 0, 0, -4, 0],
![0, 0, 0, 0, 0, 0, -1, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, -1, 0],
![0, 0, 0, 0, 1, (-2/3), 0, (2/3), 0, 0, 0, -1, 0, 0, (2/3), 0, 0, (2/3), 0, 0, 1, 0, 0, (-2/3), 0, 0, (2/3)],
![0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, -2, 0, 0, 0],
![0, 0, 0, 0, 0, (-2/3), 0, (2/3), 0, 0, 1, 0, 0, 0, (2/3), 0, -1, (2/3), 0, 0, 0, -1, 0, (-2/3), 0, 0, (2/3)],
![0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0],
![0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0],
![0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
![0, 0, 0, 0, 0, (2/3), 0, (4/3), 0, 0, 0, 0, 0, 0, (-2/3), 0, 0, (-2/3), 0, 0, 0, 0, 0, (-4/3), 0, 0, (-2/3)],
![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
![0, 0, 0, 0, 0, (-2/3), 0, (2/3), 0, 0, 0, 0, 0, 0, (-4/3), 0, 0, (-4/3), 0, 0, 0, 0, 0, (-2/3), 0, 0, (2/3)],
![0, 0, 0, 0, 0, 0, (-2/3), 0, (2/3), 0, 0, 0, 0, (-2/3), 0, 0, 0, 0, (-2/3), 0, 0, 0, 0, 0, (-2/3), (2/3), 0],
![0, 0, 0, 0, 0, 0, (1/3), 0, (1/3), 0, 0, 0, 0, (-1/3), 0, 0, 0, 0, (1/3), 0, 0, 0, 0, 0, (1/3), (1/3), 0],
![0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0],
![0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0],
![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
![0, 0, 0, 0, 0, 0, (-4/3), 0, (-4/3), 0, 0, 0, 0, (-8/3), 0, 0, 0, 0, (8/3), 0, 0, 0, 0, 0, (-4/3), (-4/3), 0],
![0, 0, 0, 0, 0, 0, (-2/3), 0, (2/3), 0, 0, 0, 0, (4/3), 0, 0, 0, 0, (4/3), 0, 0, 0, 0, 0, (-2/3), (2/3), 0],
![0, 0, 0, 0, 0, (1/3), 0, (-1/3), 0, 0, 0, 0, 0, 0, (-1/3), 0, 0, (-1/3), 0, 0, 0, 0, 0, (1/3), 0, 0, (-1/3)],
![0, 0, 0, 0, 0, 4, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 4],
![0, 0, 0, 0, 0, 0, (4/3), 0, (-8/3), 0, 0, 0, 0, (-4/3), 0, 0, 0, 0, (4/3), 0, 0, 0, 0, 0, (-8/3), (4/3), 0],
![0, 0, 0, 0, 0, 0, (-4/3), 0, (-2/3), 0, 0, 0, 0, (2/3), 0, 0, 0, 0, (2/3), 0, 0, 0, 0, 0, (2/3), (4/3), 0]
]



set_option maxHeartbeats 2000000 in
theorem left_row0 (j : Fin 27) :
    (inverseMatrix * coordinateMatrix) 0 j = (1 : Matrix (Fin 27) (Fin 27) ℝ) 0 j := by
  change (∑ k : Fin 27, inverseMatrix 0 k * coordinateMatrix k j) =
    (if (0 : Fin 27) = j then 1 else 0)
  fin_cases j <;> norm_num [inverseMatrix, coordinateMatrix, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
theorem left_row1 (j : Fin 27) :
    (inverseMatrix * coordinateMatrix) 1 j = (1 : Matrix (Fin 27) (Fin 27) ℝ) 1 j := by
  change (∑ k : Fin 27, inverseMatrix 1 k * coordinateMatrix k j) =
    (if (1 : Fin 27) = j then 1 else 0)
  fin_cases j <;> norm_num [inverseMatrix, coordinateMatrix, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
theorem left_row2 (j : Fin 27) :
    (inverseMatrix * coordinateMatrix) 2 j = (1 : Matrix (Fin 27) (Fin 27) ℝ) 2 j := by
  change (∑ k : Fin 27, inverseMatrix 2 k * coordinateMatrix k j) =
    (if (2 : Fin 27) = j then 1 else 0)
  fin_cases j <;> norm_num [inverseMatrix, coordinateMatrix, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
theorem left_row3 (j : Fin 27) :
    (inverseMatrix * coordinateMatrix) 3 j = (1 : Matrix (Fin 27) (Fin 27) ℝ) 3 j := by
  change (∑ k : Fin 27, inverseMatrix 3 k * coordinateMatrix k j) =
    (if (3 : Fin 27) = j then 1 else 0)
  fin_cases j <;> norm_num [inverseMatrix, coordinateMatrix, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
theorem left_row4 (j : Fin 27) :
    (inverseMatrix * coordinateMatrix) 4 j = (1 : Matrix (Fin 27) (Fin 27) ℝ) 4 j := by
  change (∑ k : Fin 27, inverseMatrix 4 k * coordinateMatrix k j) =
    (if (4 : Fin 27) = j then 1 else 0)
  fin_cases j <;> norm_num [inverseMatrix, coordinateMatrix, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
theorem left_row5 (j : Fin 27) :
    (inverseMatrix * coordinateMatrix) 5 j = (1 : Matrix (Fin 27) (Fin 27) ℝ) 5 j := by
  change (∑ k : Fin 27, inverseMatrix 5 k * coordinateMatrix k j) =
    (if (5 : Fin 27) = j then 1 else 0)
  fin_cases j <;> norm_num [inverseMatrix, coordinateMatrix, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
theorem left_row6 (j : Fin 27) :
    (inverseMatrix * coordinateMatrix) 6 j = (1 : Matrix (Fin 27) (Fin 27) ℝ) 6 j := by
  change (∑ k : Fin 27, inverseMatrix 6 k * coordinateMatrix k j) =
    (if (6 : Fin 27) = j then 1 else 0)
  fin_cases j <;> norm_num [inverseMatrix, coordinateMatrix, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
theorem left_row7 (j : Fin 27) :
    (inverseMatrix * coordinateMatrix) 7 j = (1 : Matrix (Fin 27) (Fin 27) ℝ) 7 j := by
  change (∑ k : Fin 27, inverseMatrix 7 k * coordinateMatrix k j) =
    (if (7 : Fin 27) = j then 1 else 0)
  fin_cases j <;> norm_num [inverseMatrix, coordinateMatrix, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
theorem left_row8 (j : Fin 27) :
    (inverseMatrix * coordinateMatrix) 8 j = (1 : Matrix (Fin 27) (Fin 27) ℝ) 8 j := by
  change (∑ k : Fin 27, inverseMatrix 8 k * coordinateMatrix k j) =
    (if (8 : Fin 27) = j then 1 else 0)
  fin_cases j <;> norm_num [inverseMatrix, coordinateMatrix, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
theorem left_row9 (j : Fin 27) :
    (inverseMatrix * coordinateMatrix) 9 j = (1 : Matrix (Fin 27) (Fin 27) ℝ) 9 j := by
  change (∑ k : Fin 27, inverseMatrix 9 k * coordinateMatrix k j) =
    (if (9 : Fin 27) = j then 1 else 0)
  fin_cases j <;> norm_num [inverseMatrix, coordinateMatrix, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
theorem left_row10 (j : Fin 27) :
    (inverseMatrix * coordinateMatrix) 10 j = (1 : Matrix (Fin 27) (Fin 27) ℝ) 10 j := by
  change (∑ k : Fin 27, inverseMatrix 10 k * coordinateMatrix k j) =
    (if (10 : Fin 27) = j then 1 else 0)
  fin_cases j <;> norm_num [inverseMatrix, coordinateMatrix, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
theorem left_row11 (j : Fin 27) :
    (inverseMatrix * coordinateMatrix) 11 j = (1 : Matrix (Fin 27) (Fin 27) ℝ) 11 j := by
  change (∑ k : Fin 27, inverseMatrix 11 k * coordinateMatrix k j) =
    (if (11 : Fin 27) = j then 1 else 0)
  fin_cases j <;> norm_num [inverseMatrix, coordinateMatrix, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
theorem left_row12 (j : Fin 27) :
    (inverseMatrix * coordinateMatrix) 12 j = (1 : Matrix (Fin 27) (Fin 27) ℝ) 12 j := by
  change (∑ k : Fin 27, inverseMatrix 12 k * coordinateMatrix k j) =
    (if (12 : Fin 27) = j then 1 else 0)
  fin_cases j <;> norm_num [inverseMatrix, coordinateMatrix, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
theorem left_row13 (j : Fin 27) :
    (inverseMatrix * coordinateMatrix) 13 j = (1 : Matrix (Fin 27) (Fin 27) ℝ) 13 j := by
  change (∑ k : Fin 27, inverseMatrix 13 k * coordinateMatrix k j) =
    (if (13 : Fin 27) = j then 1 else 0)
  fin_cases j <;> norm_num [inverseMatrix, coordinateMatrix, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
theorem left_row14 (j : Fin 27) :
    (inverseMatrix * coordinateMatrix) 14 j = (1 : Matrix (Fin 27) (Fin 27) ℝ) 14 j := by
  change (∑ k : Fin 27, inverseMatrix 14 k * coordinateMatrix k j) =
    (if (14 : Fin 27) = j then 1 else 0)
  fin_cases j <;> norm_num [inverseMatrix, coordinateMatrix, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
theorem left_row15 (j : Fin 27) :
    (inverseMatrix * coordinateMatrix) 15 j = (1 : Matrix (Fin 27) (Fin 27) ℝ) 15 j := by
  change (∑ k : Fin 27, inverseMatrix 15 k * coordinateMatrix k j) =
    (if (15 : Fin 27) = j then 1 else 0)
  fin_cases j <;> norm_num [inverseMatrix, coordinateMatrix, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
theorem left_row16 (j : Fin 27) :
    (inverseMatrix * coordinateMatrix) 16 j = (1 : Matrix (Fin 27) (Fin 27) ℝ) 16 j := by
  change (∑ k : Fin 27, inverseMatrix 16 k * coordinateMatrix k j) =
    (if (16 : Fin 27) = j then 1 else 0)
  fin_cases j <;> norm_num [inverseMatrix, coordinateMatrix, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
theorem left_row17 (j : Fin 27) :
    (inverseMatrix * coordinateMatrix) 17 j = (1 : Matrix (Fin 27) (Fin 27) ℝ) 17 j := by
  change (∑ k : Fin 27, inverseMatrix 17 k * coordinateMatrix k j) =
    (if (17 : Fin 27) = j then 1 else 0)
  fin_cases j <;> norm_num [inverseMatrix, coordinateMatrix, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
theorem left_row18 (j : Fin 27) :
    (inverseMatrix * coordinateMatrix) 18 j = (1 : Matrix (Fin 27) (Fin 27) ℝ) 18 j := by
  change (∑ k : Fin 27, inverseMatrix 18 k * coordinateMatrix k j) =
    (if (18 : Fin 27) = j then 1 else 0)
  fin_cases j <;> norm_num [inverseMatrix, coordinateMatrix, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
theorem left_row19 (j : Fin 27) :
    (inverseMatrix * coordinateMatrix) 19 j = (1 : Matrix (Fin 27) (Fin 27) ℝ) 19 j := by
  change (∑ k : Fin 27, inverseMatrix 19 k * coordinateMatrix k j) =
    (if (19 : Fin 27) = j then 1 else 0)
  fin_cases j <;> norm_num [inverseMatrix, coordinateMatrix, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
theorem left_row20 (j : Fin 27) :
    (inverseMatrix * coordinateMatrix) 20 j = (1 : Matrix (Fin 27) (Fin 27) ℝ) 20 j := by
  change (∑ k : Fin 27, inverseMatrix 20 k * coordinateMatrix k j) =
    (if (20 : Fin 27) = j then 1 else 0)
  fin_cases j <;> norm_num [inverseMatrix, coordinateMatrix, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
theorem left_row21 (j : Fin 27) :
    (inverseMatrix * coordinateMatrix) 21 j = (1 : Matrix (Fin 27) (Fin 27) ℝ) 21 j := by
  change (∑ k : Fin 27, inverseMatrix 21 k * coordinateMatrix k j) =
    (if (21 : Fin 27) = j then 1 else 0)
  fin_cases j <;> norm_num [inverseMatrix, coordinateMatrix, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
theorem left_row22 (j : Fin 27) :
    (inverseMatrix * coordinateMatrix) 22 j = (1 : Matrix (Fin 27) (Fin 27) ℝ) 22 j := by
  change (∑ k : Fin 27, inverseMatrix 22 k * coordinateMatrix k j) =
    (if (22 : Fin 27) = j then 1 else 0)
  fin_cases j <;> norm_num [inverseMatrix, coordinateMatrix, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
theorem left_row23 (j : Fin 27) :
    (inverseMatrix * coordinateMatrix) 23 j = (1 : Matrix (Fin 27) (Fin 27) ℝ) 23 j := by
  change (∑ k : Fin 27, inverseMatrix 23 k * coordinateMatrix k j) =
    (if (23 : Fin 27) = j then 1 else 0)
  fin_cases j <;> norm_num [inverseMatrix, coordinateMatrix, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
theorem left_row24 (j : Fin 27) :
    (inverseMatrix * coordinateMatrix) 24 j = (1 : Matrix (Fin 27) (Fin 27) ℝ) 24 j := by
  change (∑ k : Fin 27, inverseMatrix 24 k * coordinateMatrix k j) =
    (if (24 : Fin 27) = j then 1 else 0)
  fin_cases j <;> norm_num [inverseMatrix, coordinateMatrix, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
theorem left_row25 (j : Fin 27) :
    (inverseMatrix * coordinateMatrix) 25 j = (1 : Matrix (Fin 27) (Fin 27) ℝ) 25 j := by
  change (∑ k : Fin 27, inverseMatrix 25 k * coordinateMatrix k j) =
    (if (25 : Fin 27) = j then 1 else 0)
  fin_cases j <;> norm_num [inverseMatrix, coordinateMatrix, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
theorem left_row26 (j : Fin 27) :
    (inverseMatrix * coordinateMatrix) 26 j = (1 : Matrix (Fin 27) (Fin 27) ℝ) 26 j := by
  change (∑ k : Fin 27, inverseMatrix 26 k * coordinateMatrix k j) =
    (if (26 : Fin 27) = j then 1 else 0)
  fin_cases j <;> norm_num [inverseMatrix, coordinateMatrix, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem left_inverse : inverseMatrix * coordinateMatrix = 1 := by
  ext i j
  fin_cases i
  · exact left_row0 j
  · exact left_row1 j
  · exact left_row2 j
  · exact left_row3 j
  · exact left_row4 j
  · exact left_row5 j
  · exact left_row6 j
  · exact left_row7 j
  · exact left_row8 j
  · exact left_row9 j
  · exact left_row10 j
  · exact left_row11 j
  · exact left_row12 j
  · exact left_row13 j
  · exact left_row14 j
  · exact left_row15 j
  · exact left_row16 j
  · exact left_row17 j
  · exact left_row18 j
  · exact left_row19 j
  · exact left_row20 j
  · exact left_row21 j
  · exact left_row22 j
  · exact left_row23 j
  · exact left_row24 j
  · exact left_row25 j
  · exact left_row26 j

theorem right_inverse : coordinateMatrix * inverseMatrix = 1 :=
  mul_eq_one_comm.mp left_inverse

end
end Glennie.Compact.NativeWordTableR01
