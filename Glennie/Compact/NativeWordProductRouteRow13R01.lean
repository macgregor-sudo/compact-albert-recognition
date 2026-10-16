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

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeffRow13 : Fin 27 → Fin 27 → ℝ := ![productCoeff_00_13, productCoeff_01_13, productCoeff_02_13, productCoeff_03_13, productCoeff_04_13, productCoeff_05_13, productCoeff_06_13, productCoeff_07_13, productCoeff_08_13, productCoeff_09_13, productCoeff_10_13, productCoeff_11_13, productCoeff_12_13, productCoeff_13_13, productCoeff_13_14, productCoeff_13_15, productCoeff_13_16, productCoeff_13_17, productCoeff_13_18, productCoeff_13_19, productCoeff_13_20, productCoeff_13_21, productCoeff_13_22, productCoeff_13_23, productCoeff_13_24, productCoeff_13_25, productCoeff_13_26]

theorem native_product_row13 (j : Fin 27) :
    jordan (nativeWords 13) (nativeWords j) =
      ∑ k : Fin 27, productCoeffRow13 j k • nativeWords k := by
  fin_cases j
  · exact (jordan_comm (nativeWords 13) (nativeWords 0)).trans native_product_00_13
  · exact (jordan_comm (nativeWords 13) (nativeWords 1)).trans native_product_01_13
  · exact (jordan_comm (nativeWords 13) (nativeWords 2)).trans native_product_02_13
  · exact (jordan_comm (nativeWords 13) (nativeWords 3)).trans native_product_03_13
  · exact (jordan_comm (nativeWords 13) (nativeWords 4)).trans native_product_04_13
  · exact (jordan_comm (nativeWords 13) (nativeWords 5)).trans native_product_05_13
  · exact (jordan_comm (nativeWords 13) (nativeWords 6)).trans native_product_06_13
  · exact (jordan_comm (nativeWords 13) (nativeWords 7)).trans native_product_07_13
  · exact (jordan_comm (nativeWords 13) (nativeWords 8)).trans native_product_08_13
  · exact (jordan_comm (nativeWords 13) (nativeWords 9)).trans native_product_09_13
  · exact (jordan_comm (nativeWords 13) (nativeWords 10)).trans native_product_10_13
  · exact (jordan_comm (nativeWords 13) (nativeWords 11)).trans native_product_11_13
  · exact (jordan_comm (nativeWords 13) (nativeWords 12)).trans native_product_12_13
  · exact native_product_13_13
  · exact native_product_13_14
  · exact native_product_13_15
  · exact native_product_13_16
  · exact native_product_13_17
  · exact native_product_13_18
  · exact native_product_13_19
  · exact native_product_13_20
  · exact native_product_13_21
  · exact native_product_13_22
  · exact native_product_13_23
  · exact native_product_13_24
  · exact native_product_13_25
  · exact native_product_13_26

end
end Glennie.Compact.NativeWordTableR01
