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
public import Glennie.Compact.NativeWordProductRow26R01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeffRow26 : Fin 27 → Fin 27 → ℝ := ![productCoeff_00_26, productCoeff_01_26, productCoeff_02_26, productCoeff_03_26, productCoeff_04_26, productCoeff_05_26, productCoeff_06_26, productCoeff_07_26, productCoeff_08_26, productCoeff_09_26, productCoeff_10_26, productCoeff_11_26, productCoeff_12_26, productCoeff_13_26, productCoeff_14_26, productCoeff_15_26, productCoeff_16_26, productCoeff_17_26, productCoeff_18_26, productCoeff_19_26, productCoeff_20_26, productCoeff_21_26, productCoeff_22_26, productCoeff_23_26, productCoeff_24_26, productCoeff_25_26, productCoeff_26_26]

theorem native_product_row26 (j : Fin 27) :
    jordan (nativeWords 26) (nativeWords j) =
      ∑ k : Fin 27, productCoeffRow26 j k • nativeWords k := by
  fin_cases j
  · exact (jordan_comm (nativeWords 26) (nativeWords 0)).trans native_product_00_26
  · exact (jordan_comm (nativeWords 26) (nativeWords 1)).trans native_product_01_26
  · exact (jordan_comm (nativeWords 26) (nativeWords 2)).trans native_product_02_26
  · exact (jordan_comm (nativeWords 26) (nativeWords 3)).trans native_product_03_26
  · exact (jordan_comm (nativeWords 26) (nativeWords 4)).trans native_product_04_26
  · exact (jordan_comm (nativeWords 26) (nativeWords 5)).trans native_product_05_26
  · exact (jordan_comm (nativeWords 26) (nativeWords 6)).trans native_product_06_26
  · exact (jordan_comm (nativeWords 26) (nativeWords 7)).trans native_product_07_26
  · exact (jordan_comm (nativeWords 26) (nativeWords 8)).trans native_product_08_26
  · exact (jordan_comm (nativeWords 26) (nativeWords 9)).trans native_product_09_26
  · exact (jordan_comm (nativeWords 26) (nativeWords 10)).trans native_product_10_26
  · exact (jordan_comm (nativeWords 26) (nativeWords 11)).trans native_product_11_26
  · exact (jordan_comm (nativeWords 26) (nativeWords 12)).trans native_product_12_26
  · exact (jordan_comm (nativeWords 26) (nativeWords 13)).trans native_product_13_26
  · exact (jordan_comm (nativeWords 26) (nativeWords 14)).trans native_product_14_26
  · exact (jordan_comm (nativeWords 26) (nativeWords 15)).trans native_product_15_26
  · exact (jordan_comm (nativeWords 26) (nativeWords 16)).trans native_product_16_26
  · exact (jordan_comm (nativeWords 26) (nativeWords 17)).trans native_product_17_26
  · exact (jordan_comm (nativeWords 26) (nativeWords 18)).trans native_product_18_26
  · exact (jordan_comm (nativeWords 26) (nativeWords 19)).trans native_product_19_26
  · exact (jordan_comm (nativeWords 26) (nativeWords 20)).trans native_product_20_26
  · exact (jordan_comm (nativeWords 26) (nativeWords 21)).trans native_product_21_26
  · exact (jordan_comm (nativeWords 26) (nativeWords 22)).trans native_product_22_26
  · exact (jordan_comm (nativeWords 26) (nativeWords 23)).trans native_product_23_26
  · exact (jordan_comm (nativeWords 26) (nativeWords 24)).trans native_product_24_26
  · exact (jordan_comm (nativeWords 26) (nativeWords 25)).trans native_product_25_26
  · exact native_product_26_26

end
end Glennie.Compact.NativeWordTableR01
