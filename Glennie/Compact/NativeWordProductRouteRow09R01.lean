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
public import Glennie.Compact.NativeWordProductRow08R01
public import Glennie.Compact.NativeWordProductRow09R01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeffRow9 : Fin 27 → Fin 27 → ℝ := ![productCoeff_00_09, productCoeff_01_09, productCoeff_02_09, productCoeff_03_09, productCoeff_04_09, productCoeff_05_09, productCoeff_06_09, productCoeff_07_09, productCoeff_08_09, productCoeff_09_09, productCoeff_09_10, productCoeff_09_11, productCoeff_09_12, productCoeff_09_13, productCoeff_09_14, productCoeff_09_15, productCoeff_09_16, productCoeff_09_17, productCoeff_09_18, productCoeff_09_19, productCoeff_09_20, productCoeff_09_21, productCoeff_09_22, productCoeff_09_23, productCoeff_09_24, productCoeff_09_25, productCoeff_09_26]

theorem native_product_row9 (j : Fin 27) :
    jordan (nativeWords 9) (nativeWords j) =
      ∑ k : Fin 27, productCoeffRow9 j k • nativeWords k := by
  fin_cases j
  · exact (jordan_comm (nativeWords 9) (nativeWords 0)).trans native_product_00_09
  · exact (jordan_comm (nativeWords 9) (nativeWords 1)).trans native_product_01_09
  · exact (jordan_comm (nativeWords 9) (nativeWords 2)).trans native_product_02_09
  · exact (jordan_comm (nativeWords 9) (nativeWords 3)).trans native_product_03_09
  · exact (jordan_comm (nativeWords 9) (nativeWords 4)).trans native_product_04_09
  · exact (jordan_comm (nativeWords 9) (nativeWords 5)).trans native_product_05_09
  · exact (jordan_comm (nativeWords 9) (nativeWords 6)).trans native_product_06_09
  · exact (jordan_comm (nativeWords 9) (nativeWords 7)).trans native_product_07_09
  · exact (jordan_comm (nativeWords 9) (nativeWords 8)).trans native_product_08_09
  · exact native_product_09_09
  · exact native_product_09_10
  · exact native_product_09_11
  · exact native_product_09_12
  · exact native_product_09_13
  · exact native_product_09_14
  · exact native_product_09_15
  · exact native_product_09_16
  · exact native_product_09_17
  · exact native_product_09_18
  · exact native_product_09_19
  · exact native_product_09_20
  · exact native_product_09_21
  · exact native_product_09_22
  · exact native_product_09_23
  · exact native_product_09_24
  · exact native_product_09_25
  · exact native_product_09_26

end
end Glennie.Compact.NativeWordTableR01
