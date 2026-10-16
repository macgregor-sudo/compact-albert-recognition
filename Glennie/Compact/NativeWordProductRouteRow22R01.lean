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
public import Glennie.Compact.NativeWordProductRow19R01
public import Glennie.Compact.NativeWordProductRow20R01
public import Glennie.Compact.NativeWordProductRow21R01
public import Glennie.Compact.NativeWordProductRow22R01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeffRow22 : Fin 27 → Fin 27 → ℝ := ![productCoeff_00_22, productCoeff_01_22, productCoeff_02_22, productCoeff_03_22, productCoeff_04_22, productCoeff_05_22, productCoeff_06_22, productCoeff_07_22, productCoeff_08_22, productCoeff_09_22, productCoeff_10_22, productCoeff_11_22, productCoeff_12_22, productCoeff_13_22, productCoeff_14_22, productCoeff_15_22, productCoeff_16_22, productCoeff_17_22, productCoeff_18_22, productCoeff_19_22, productCoeff_20_22, productCoeff_21_22, productCoeff_22_22, productCoeff_22_23, productCoeff_22_24, productCoeff_22_25, productCoeff_22_26]

theorem native_product_row22 (j : Fin 27) :
    jordan (nativeWords 22) (nativeWords j) =
      ∑ k : Fin 27, productCoeffRow22 j k • nativeWords k := by
  fin_cases j
  · exact (jordan_comm (nativeWords 22) (nativeWords 0)).trans native_product_00_22
  · exact (jordan_comm (nativeWords 22) (nativeWords 1)).trans native_product_01_22
  · exact (jordan_comm (nativeWords 22) (nativeWords 2)).trans native_product_02_22
  · exact (jordan_comm (nativeWords 22) (nativeWords 3)).trans native_product_03_22
  · exact (jordan_comm (nativeWords 22) (nativeWords 4)).trans native_product_04_22
  · exact (jordan_comm (nativeWords 22) (nativeWords 5)).trans native_product_05_22
  · exact (jordan_comm (nativeWords 22) (nativeWords 6)).trans native_product_06_22
  · exact (jordan_comm (nativeWords 22) (nativeWords 7)).trans native_product_07_22
  · exact (jordan_comm (nativeWords 22) (nativeWords 8)).trans native_product_08_22
  · exact (jordan_comm (nativeWords 22) (nativeWords 9)).trans native_product_09_22
  · exact (jordan_comm (nativeWords 22) (nativeWords 10)).trans native_product_10_22
  · exact (jordan_comm (nativeWords 22) (nativeWords 11)).trans native_product_11_22
  · exact (jordan_comm (nativeWords 22) (nativeWords 12)).trans native_product_12_22
  · exact (jordan_comm (nativeWords 22) (nativeWords 13)).trans native_product_13_22
  · exact (jordan_comm (nativeWords 22) (nativeWords 14)).trans native_product_14_22
  · exact (jordan_comm (nativeWords 22) (nativeWords 15)).trans native_product_15_22
  · exact (jordan_comm (nativeWords 22) (nativeWords 16)).trans native_product_16_22
  · exact (jordan_comm (nativeWords 22) (nativeWords 17)).trans native_product_17_22
  · exact (jordan_comm (nativeWords 22) (nativeWords 18)).trans native_product_18_22
  · exact (jordan_comm (nativeWords 22) (nativeWords 19)).trans native_product_19_22
  · exact (jordan_comm (nativeWords 22) (nativeWords 20)).trans native_product_20_22
  · exact (jordan_comm (nativeWords 22) (nativeWords 21)).trans native_product_21_22
  · exact native_product_22_22
  · exact native_product_22_23
  · exact native_product_22_24
  · exact native_product_22_25
  · exact native_product_22_26

end
end Glennie.Compact.NativeWordTableR01
