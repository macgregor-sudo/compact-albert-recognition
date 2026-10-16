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
public import Glennie.Compact.NativeWordProductRow23R01
public import Glennie.Compact.NativeWordProductRow24R01
public import Glennie.Compact.NativeWordProductRow25R01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeffRow25 : Fin 27 → Fin 27 → ℝ := ![productCoeff_00_25, productCoeff_01_25, productCoeff_02_25, productCoeff_03_25, productCoeff_04_25, productCoeff_05_25, productCoeff_06_25, productCoeff_07_25, productCoeff_08_25, productCoeff_09_25, productCoeff_10_25, productCoeff_11_25, productCoeff_12_25, productCoeff_13_25, productCoeff_14_25, productCoeff_15_25, productCoeff_16_25, productCoeff_17_25, productCoeff_18_25, productCoeff_19_25, productCoeff_20_25, productCoeff_21_25, productCoeff_22_25, productCoeff_23_25, productCoeff_24_25, productCoeff_25_25, productCoeff_25_26]

theorem native_product_row25 (j : Fin 27) :
    jordan (nativeWords 25) (nativeWords j) =
      ∑ k : Fin 27, productCoeffRow25 j k • nativeWords k := by
  fin_cases j
  · exact (jordan_comm (nativeWords 25) (nativeWords 0)).trans native_product_00_25
  · exact (jordan_comm (nativeWords 25) (nativeWords 1)).trans native_product_01_25
  · exact (jordan_comm (nativeWords 25) (nativeWords 2)).trans native_product_02_25
  · exact (jordan_comm (nativeWords 25) (nativeWords 3)).trans native_product_03_25
  · exact (jordan_comm (nativeWords 25) (nativeWords 4)).trans native_product_04_25
  · exact (jordan_comm (nativeWords 25) (nativeWords 5)).trans native_product_05_25
  · exact (jordan_comm (nativeWords 25) (nativeWords 6)).trans native_product_06_25
  · exact (jordan_comm (nativeWords 25) (nativeWords 7)).trans native_product_07_25
  · exact (jordan_comm (nativeWords 25) (nativeWords 8)).trans native_product_08_25
  · exact (jordan_comm (nativeWords 25) (nativeWords 9)).trans native_product_09_25
  · exact (jordan_comm (nativeWords 25) (nativeWords 10)).trans native_product_10_25
  · exact (jordan_comm (nativeWords 25) (nativeWords 11)).trans native_product_11_25
  · exact (jordan_comm (nativeWords 25) (nativeWords 12)).trans native_product_12_25
  · exact (jordan_comm (nativeWords 25) (nativeWords 13)).trans native_product_13_25
  · exact (jordan_comm (nativeWords 25) (nativeWords 14)).trans native_product_14_25
  · exact (jordan_comm (nativeWords 25) (nativeWords 15)).trans native_product_15_25
  · exact (jordan_comm (nativeWords 25) (nativeWords 16)).trans native_product_16_25
  · exact (jordan_comm (nativeWords 25) (nativeWords 17)).trans native_product_17_25
  · exact (jordan_comm (nativeWords 25) (nativeWords 18)).trans native_product_18_25
  · exact (jordan_comm (nativeWords 25) (nativeWords 19)).trans native_product_19_25
  · exact (jordan_comm (nativeWords 25) (nativeWords 20)).trans native_product_20_25
  · exact (jordan_comm (nativeWords 25) (nativeWords 21)).trans native_product_21_25
  · exact (jordan_comm (nativeWords 25) (nativeWords 22)).trans native_product_22_25
  · exact (jordan_comm (nativeWords 25) (nativeWords 23)).trans native_product_23_25
  · exact (jordan_comm (nativeWords 25) (nativeWords 24)).trans native_product_24_25
  · exact native_product_25_25
  · exact native_product_25_26

end
end Glennie.Compact.NativeWordTableR01
