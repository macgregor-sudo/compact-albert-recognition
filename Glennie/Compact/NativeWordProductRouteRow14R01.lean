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
public import Glennie.Compact.NativeWordProductRow10R01
public import Glennie.Compact.NativeWordProductRow11R01
public import Glennie.Compact.NativeWordProductRow12R01
public import Glennie.Compact.NativeWordProductRow13R01
public import Glennie.Compact.NativeWordProductRow14R01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeffRow14 : Fin 27 → Fin 27 → ℝ := ![productCoeff_00_14, productCoeff_01_14, productCoeff_02_14, productCoeff_03_14, productCoeff_04_14, productCoeff_05_14, productCoeff_06_14, productCoeff_07_14, productCoeff_08_14, productCoeff_09_14, productCoeff_10_14, productCoeff_11_14, productCoeff_12_14, productCoeff_13_14, productCoeff_14_14, productCoeff_14_15, productCoeff_14_16, productCoeff_14_17, productCoeff_14_18, productCoeff_14_19, productCoeff_14_20, productCoeff_14_21, productCoeff_14_22, productCoeff_14_23, productCoeff_14_24, productCoeff_14_25, productCoeff_14_26]

theorem native_product_row14 (j : Fin 27) :
    jordan (nativeWords 14) (nativeWords j) =
      ∑ k : Fin 27, productCoeffRow14 j k • nativeWords k := by
  fin_cases j
  · exact (jordan_comm (nativeWords 14) (nativeWords 0)).trans native_product_00_14
  · exact (jordan_comm (nativeWords 14) (nativeWords 1)).trans native_product_01_14
  · exact (jordan_comm (nativeWords 14) (nativeWords 2)).trans native_product_02_14
  · exact (jordan_comm (nativeWords 14) (nativeWords 3)).trans native_product_03_14
  · exact (jordan_comm (nativeWords 14) (nativeWords 4)).trans native_product_04_14
  · exact (jordan_comm (nativeWords 14) (nativeWords 5)).trans native_product_05_14
  · exact (jordan_comm (nativeWords 14) (nativeWords 6)).trans native_product_06_14
  · exact (jordan_comm (nativeWords 14) (nativeWords 7)).trans native_product_07_14
  · exact (jordan_comm (nativeWords 14) (nativeWords 8)).trans native_product_08_14
  · exact (jordan_comm (nativeWords 14) (nativeWords 9)).trans native_product_09_14
  · exact (jordan_comm (nativeWords 14) (nativeWords 10)).trans native_product_10_14
  · exact (jordan_comm (nativeWords 14) (nativeWords 11)).trans native_product_11_14
  · exact (jordan_comm (nativeWords 14) (nativeWords 12)).trans native_product_12_14
  · exact (jordan_comm (nativeWords 14) (nativeWords 13)).trans native_product_13_14
  · exact native_product_14_14
  · exact native_product_14_15
  · exact native_product_14_16
  · exact native_product_14_17
  · exact native_product_14_18
  · exact native_product_14_19
  · exact native_product_14_20
  · exact native_product_14_21
  · exact native_product_14_22
  · exact native_product_14_23
  · exact native_product_14_24
  · exact native_product_14_25
  · exact native_product_14_26

end
end Glennie.Compact.NativeWordTableR01
