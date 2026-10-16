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
public import Glennie.Compact.NativeWordProductRow18R01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeffRow18 : Fin 27 → Fin 27 → ℝ := ![productCoeff_00_18, productCoeff_01_18, productCoeff_02_18, productCoeff_03_18, productCoeff_04_18, productCoeff_05_18, productCoeff_06_18, productCoeff_07_18, productCoeff_08_18, productCoeff_09_18, productCoeff_10_18, productCoeff_11_18, productCoeff_12_18, productCoeff_13_18, productCoeff_14_18, productCoeff_15_18, productCoeff_16_18, productCoeff_17_18, productCoeff_18_18, productCoeff_18_19, productCoeff_18_20, productCoeff_18_21, productCoeff_18_22, productCoeff_18_23, productCoeff_18_24, productCoeff_18_25, productCoeff_18_26]

theorem native_product_row18 (j : Fin 27) :
    jordan (nativeWords 18) (nativeWords j) =
      ∑ k : Fin 27, productCoeffRow18 j k • nativeWords k := by
  fin_cases j
  · exact (jordan_comm (nativeWords 18) (nativeWords 0)).trans native_product_00_18
  · exact (jordan_comm (nativeWords 18) (nativeWords 1)).trans native_product_01_18
  · exact (jordan_comm (nativeWords 18) (nativeWords 2)).trans native_product_02_18
  · exact (jordan_comm (nativeWords 18) (nativeWords 3)).trans native_product_03_18
  · exact (jordan_comm (nativeWords 18) (nativeWords 4)).trans native_product_04_18
  · exact (jordan_comm (nativeWords 18) (nativeWords 5)).trans native_product_05_18
  · exact (jordan_comm (nativeWords 18) (nativeWords 6)).trans native_product_06_18
  · exact (jordan_comm (nativeWords 18) (nativeWords 7)).trans native_product_07_18
  · exact (jordan_comm (nativeWords 18) (nativeWords 8)).trans native_product_08_18
  · exact (jordan_comm (nativeWords 18) (nativeWords 9)).trans native_product_09_18
  · exact (jordan_comm (nativeWords 18) (nativeWords 10)).trans native_product_10_18
  · exact (jordan_comm (nativeWords 18) (nativeWords 11)).trans native_product_11_18
  · exact (jordan_comm (nativeWords 18) (nativeWords 12)).trans native_product_12_18
  · exact (jordan_comm (nativeWords 18) (nativeWords 13)).trans native_product_13_18
  · exact (jordan_comm (nativeWords 18) (nativeWords 14)).trans native_product_14_18
  · exact (jordan_comm (nativeWords 18) (nativeWords 15)).trans native_product_15_18
  · exact (jordan_comm (nativeWords 18) (nativeWords 16)).trans native_product_16_18
  · exact (jordan_comm (nativeWords 18) (nativeWords 17)).trans native_product_17_18
  · exact native_product_18_18
  · exact native_product_18_19
  · exact native_product_18_20
  · exact native_product_18_21
  · exact native_product_18_22
  · exact native_product_18_23
  · exact native_product_18_24
  · exact native_product_18_25
  · exact native_product_18_26

end
end Glennie.Compact.NativeWordTableR01
