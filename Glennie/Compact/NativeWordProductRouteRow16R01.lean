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
public import Glennie.Compact.NativeWordProductRow15R01
public import Glennie.Compact.NativeWordProductRow16R01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeffRow16 : Fin 27 → Fin 27 → ℝ := ![productCoeff_00_16, productCoeff_01_16, productCoeff_02_16, productCoeff_03_16, productCoeff_04_16, productCoeff_05_16, productCoeff_06_16, productCoeff_07_16, productCoeff_08_16, productCoeff_09_16, productCoeff_10_16, productCoeff_11_16, productCoeff_12_16, productCoeff_13_16, productCoeff_14_16, productCoeff_15_16, productCoeff_16_16, productCoeff_16_17, productCoeff_16_18, productCoeff_16_19, productCoeff_16_20, productCoeff_16_21, productCoeff_16_22, productCoeff_16_23, productCoeff_16_24, productCoeff_16_25, productCoeff_16_26]

theorem native_product_row16 (j : Fin 27) :
    jordan (nativeWords 16) (nativeWords j) =
      ∑ k : Fin 27, productCoeffRow16 j k • nativeWords k := by
  fin_cases j
  · exact (jordan_comm (nativeWords 16) (nativeWords 0)).trans native_product_00_16
  · exact (jordan_comm (nativeWords 16) (nativeWords 1)).trans native_product_01_16
  · exact (jordan_comm (nativeWords 16) (nativeWords 2)).trans native_product_02_16
  · exact (jordan_comm (nativeWords 16) (nativeWords 3)).trans native_product_03_16
  · exact (jordan_comm (nativeWords 16) (nativeWords 4)).trans native_product_04_16
  · exact (jordan_comm (nativeWords 16) (nativeWords 5)).trans native_product_05_16
  · exact (jordan_comm (nativeWords 16) (nativeWords 6)).trans native_product_06_16
  · exact (jordan_comm (nativeWords 16) (nativeWords 7)).trans native_product_07_16
  · exact (jordan_comm (nativeWords 16) (nativeWords 8)).trans native_product_08_16
  · exact (jordan_comm (nativeWords 16) (nativeWords 9)).trans native_product_09_16
  · exact (jordan_comm (nativeWords 16) (nativeWords 10)).trans native_product_10_16
  · exact (jordan_comm (nativeWords 16) (nativeWords 11)).trans native_product_11_16
  · exact (jordan_comm (nativeWords 16) (nativeWords 12)).trans native_product_12_16
  · exact (jordan_comm (nativeWords 16) (nativeWords 13)).trans native_product_13_16
  · exact (jordan_comm (nativeWords 16) (nativeWords 14)).trans native_product_14_16
  · exact (jordan_comm (nativeWords 16) (nativeWords 15)).trans native_product_15_16
  · exact native_product_16_16
  · exact native_product_16_17
  · exact native_product_16_18
  · exact native_product_16_19
  · exact native_product_16_20
  · exact native_product_16_21
  · exact native_product_16_22
  · exact native_product_16_23
  · exact native_product_16_24
  · exact native_product_16_25
  · exact native_product_16_26

end
end Glennie.Compact.NativeWordTableR01
