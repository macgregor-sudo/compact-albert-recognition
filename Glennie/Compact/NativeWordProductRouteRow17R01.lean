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
public import Glennie.Compact.NativeWordProductRow17R01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeffRow17 : Fin 27 → Fin 27 → ℝ := ![productCoeff_00_17, productCoeff_01_17, productCoeff_02_17, productCoeff_03_17, productCoeff_04_17, productCoeff_05_17, productCoeff_06_17, productCoeff_07_17, productCoeff_08_17, productCoeff_09_17, productCoeff_10_17, productCoeff_11_17, productCoeff_12_17, productCoeff_13_17, productCoeff_14_17, productCoeff_15_17, productCoeff_16_17, productCoeff_17_17, productCoeff_17_18, productCoeff_17_19, productCoeff_17_20, productCoeff_17_21, productCoeff_17_22, productCoeff_17_23, productCoeff_17_24, productCoeff_17_25, productCoeff_17_26]

theorem native_product_row17 (j : Fin 27) :
    jordan (nativeWords 17) (nativeWords j) =
      ∑ k : Fin 27, productCoeffRow17 j k • nativeWords k := by
  fin_cases j
  · exact (jordan_comm (nativeWords 17) (nativeWords 0)).trans native_product_00_17
  · exact (jordan_comm (nativeWords 17) (nativeWords 1)).trans native_product_01_17
  · exact (jordan_comm (nativeWords 17) (nativeWords 2)).trans native_product_02_17
  · exact (jordan_comm (nativeWords 17) (nativeWords 3)).trans native_product_03_17
  · exact (jordan_comm (nativeWords 17) (nativeWords 4)).trans native_product_04_17
  · exact (jordan_comm (nativeWords 17) (nativeWords 5)).trans native_product_05_17
  · exact (jordan_comm (nativeWords 17) (nativeWords 6)).trans native_product_06_17
  · exact (jordan_comm (nativeWords 17) (nativeWords 7)).trans native_product_07_17
  · exact (jordan_comm (nativeWords 17) (nativeWords 8)).trans native_product_08_17
  · exact (jordan_comm (nativeWords 17) (nativeWords 9)).trans native_product_09_17
  · exact (jordan_comm (nativeWords 17) (nativeWords 10)).trans native_product_10_17
  · exact (jordan_comm (nativeWords 17) (nativeWords 11)).trans native_product_11_17
  · exact (jordan_comm (nativeWords 17) (nativeWords 12)).trans native_product_12_17
  · exact (jordan_comm (nativeWords 17) (nativeWords 13)).trans native_product_13_17
  · exact (jordan_comm (nativeWords 17) (nativeWords 14)).trans native_product_14_17
  · exact (jordan_comm (nativeWords 17) (nativeWords 15)).trans native_product_15_17
  · exact (jordan_comm (nativeWords 17) (nativeWords 16)).trans native_product_16_17
  · exact native_product_17_17
  · exact native_product_17_18
  · exact native_product_17_19
  · exact native_product_17_20
  · exact native_product_17_21
  · exact native_product_17_22
  · exact native_product_17_23
  · exact native_product_17_24
  · exact native_product_17_25
  · exact native_product_17_26

end
end Glennie.Compact.NativeWordTableR01
