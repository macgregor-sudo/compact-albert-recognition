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

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeffRow15 : Fin 27 → Fin 27 → ℝ := ![productCoeff_00_15, productCoeff_01_15, productCoeff_02_15, productCoeff_03_15, productCoeff_04_15, productCoeff_05_15, productCoeff_06_15, productCoeff_07_15, productCoeff_08_15, productCoeff_09_15, productCoeff_10_15, productCoeff_11_15, productCoeff_12_15, productCoeff_13_15, productCoeff_14_15, productCoeff_15_15, productCoeff_15_16, productCoeff_15_17, productCoeff_15_18, productCoeff_15_19, productCoeff_15_20, productCoeff_15_21, productCoeff_15_22, productCoeff_15_23, productCoeff_15_24, productCoeff_15_25, productCoeff_15_26]

theorem native_product_row15 (j : Fin 27) :
    jordan (nativeWords 15) (nativeWords j) =
      ∑ k : Fin 27, productCoeffRow15 j k • nativeWords k := by
  fin_cases j
  · exact (jordan_comm (nativeWords 15) (nativeWords 0)).trans native_product_00_15
  · exact (jordan_comm (nativeWords 15) (nativeWords 1)).trans native_product_01_15
  · exact (jordan_comm (nativeWords 15) (nativeWords 2)).trans native_product_02_15
  · exact (jordan_comm (nativeWords 15) (nativeWords 3)).trans native_product_03_15
  · exact (jordan_comm (nativeWords 15) (nativeWords 4)).trans native_product_04_15
  · exact (jordan_comm (nativeWords 15) (nativeWords 5)).trans native_product_05_15
  · exact (jordan_comm (nativeWords 15) (nativeWords 6)).trans native_product_06_15
  · exact (jordan_comm (nativeWords 15) (nativeWords 7)).trans native_product_07_15
  · exact (jordan_comm (nativeWords 15) (nativeWords 8)).trans native_product_08_15
  · exact (jordan_comm (nativeWords 15) (nativeWords 9)).trans native_product_09_15
  · exact (jordan_comm (nativeWords 15) (nativeWords 10)).trans native_product_10_15
  · exact (jordan_comm (nativeWords 15) (nativeWords 11)).trans native_product_11_15
  · exact (jordan_comm (nativeWords 15) (nativeWords 12)).trans native_product_12_15
  · exact (jordan_comm (nativeWords 15) (nativeWords 13)).trans native_product_13_15
  · exact (jordan_comm (nativeWords 15) (nativeWords 14)).trans native_product_14_15
  · exact native_product_15_15
  · exact native_product_15_16
  · exact native_product_15_17
  · exact native_product_15_18
  · exact native_product_15_19
  · exact native_product_15_20
  · exact native_product_15_21
  · exact native_product_15_22
  · exact native_product_15_23
  · exact native_product_15_24
  · exact native_product_15_25
  · exact native_product_15_26

end
end Glennie.Compact.NativeWordTableR01
