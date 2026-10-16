/- Finite 27-branch product routing for this row. -/
module
public import Glennie.Compact.NativeWordProductRow00R01
public import Glennie.Compact.NativeWordProductRow01R01
public import Glennie.Compact.NativeWordProductRow02R01
public import Glennie.Compact.NativeWordProductRow03R01
public import Glennie.Compact.NativeWordProductRow04R01
public import Glennie.Compact.NativeWordProductRow05R01
public import Glennie.Compact.NativeWordProductRow06R01
public import Glennie.Compact.NativeWordProductRow07R01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeffRow7 : Fin 27 → Fin 27 → ℝ := ![productCoeff_00_07, productCoeff_01_07, productCoeff_02_07, productCoeff_03_07, productCoeff_04_07, productCoeff_05_07, productCoeff_06_07, productCoeff_07_07, productCoeff_07_08, productCoeff_07_09, productCoeff_07_10, productCoeff_07_11, productCoeff_07_12, productCoeff_07_13, productCoeff_07_14, productCoeff_07_15, productCoeff_07_16, productCoeff_07_17, productCoeff_07_18, productCoeff_07_19, productCoeff_07_20, productCoeff_07_21, productCoeff_07_22, productCoeff_07_23, productCoeff_07_24, productCoeff_07_25, productCoeff_07_26]

theorem native_product_row7 (j : Fin 27) :
    jordan (nativeWords 7) (nativeWords j) =
      ∑ k : Fin 27, productCoeffRow7 j k • nativeWords k := by
  fin_cases j
  · exact (jordan_comm (nativeWords 7) (nativeWords 0)).trans native_product_00_07
  · exact (jordan_comm (nativeWords 7) (nativeWords 1)).trans native_product_01_07
  · exact (jordan_comm (nativeWords 7) (nativeWords 2)).trans native_product_02_07
  · exact (jordan_comm (nativeWords 7) (nativeWords 3)).trans native_product_03_07
  · exact (jordan_comm (nativeWords 7) (nativeWords 4)).trans native_product_04_07
  · exact (jordan_comm (nativeWords 7) (nativeWords 5)).trans native_product_05_07
  · exact (jordan_comm (nativeWords 7) (nativeWords 6)).trans native_product_06_07
  · exact native_product_07_07
  · exact native_product_07_08
  · exact native_product_07_09
  · exact native_product_07_10
  · exact native_product_07_11
  · exact native_product_07_12
  · exact native_product_07_13
  · exact native_product_07_14
  · exact native_product_07_15
  · exact native_product_07_16
  · exact native_product_07_17
  · exact native_product_07_18
  · exact native_product_07_19
  · exact native_product_07_20
  · exact native_product_07_21
  · exact native_product_07_22
  · exact native_product_07_23
  · exact native_product_07_24
  · exact native_product_07_25
  · exact native_product_07_26

end
end Glennie.Compact.NativeWordTableR01
