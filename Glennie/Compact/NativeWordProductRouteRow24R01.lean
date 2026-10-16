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

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeffRow24 : Fin 27 → Fin 27 → ℝ := ![productCoeff_00_24, productCoeff_01_24, productCoeff_02_24, productCoeff_03_24, productCoeff_04_24, productCoeff_05_24, productCoeff_06_24, productCoeff_07_24, productCoeff_08_24, productCoeff_09_24, productCoeff_10_24, productCoeff_11_24, productCoeff_12_24, productCoeff_13_24, productCoeff_14_24, productCoeff_15_24, productCoeff_16_24, productCoeff_17_24, productCoeff_18_24, productCoeff_19_24, productCoeff_20_24, productCoeff_21_24, productCoeff_22_24, productCoeff_23_24, productCoeff_24_24, productCoeff_24_25, productCoeff_24_26]

theorem native_product_row24 (j : Fin 27) :
    jordan (nativeWords 24) (nativeWords j) =
      ∑ k : Fin 27, productCoeffRow24 j k • nativeWords k := by
  fin_cases j
  · exact (jordan_comm (nativeWords 24) (nativeWords 0)).trans native_product_00_24
  · exact (jordan_comm (nativeWords 24) (nativeWords 1)).trans native_product_01_24
  · exact (jordan_comm (nativeWords 24) (nativeWords 2)).trans native_product_02_24
  · exact (jordan_comm (nativeWords 24) (nativeWords 3)).trans native_product_03_24
  · exact (jordan_comm (nativeWords 24) (nativeWords 4)).trans native_product_04_24
  · exact (jordan_comm (nativeWords 24) (nativeWords 5)).trans native_product_05_24
  · exact (jordan_comm (nativeWords 24) (nativeWords 6)).trans native_product_06_24
  · exact (jordan_comm (nativeWords 24) (nativeWords 7)).trans native_product_07_24
  · exact (jordan_comm (nativeWords 24) (nativeWords 8)).trans native_product_08_24
  · exact (jordan_comm (nativeWords 24) (nativeWords 9)).trans native_product_09_24
  · exact (jordan_comm (nativeWords 24) (nativeWords 10)).trans native_product_10_24
  · exact (jordan_comm (nativeWords 24) (nativeWords 11)).trans native_product_11_24
  · exact (jordan_comm (nativeWords 24) (nativeWords 12)).trans native_product_12_24
  · exact (jordan_comm (nativeWords 24) (nativeWords 13)).trans native_product_13_24
  · exact (jordan_comm (nativeWords 24) (nativeWords 14)).trans native_product_14_24
  · exact (jordan_comm (nativeWords 24) (nativeWords 15)).trans native_product_15_24
  · exact (jordan_comm (nativeWords 24) (nativeWords 16)).trans native_product_16_24
  · exact (jordan_comm (nativeWords 24) (nativeWords 17)).trans native_product_17_24
  · exact (jordan_comm (nativeWords 24) (nativeWords 18)).trans native_product_18_24
  · exact (jordan_comm (nativeWords 24) (nativeWords 19)).trans native_product_19_24
  · exact (jordan_comm (nativeWords 24) (nativeWords 20)).trans native_product_20_24
  · exact (jordan_comm (nativeWords 24) (nativeWords 21)).trans native_product_21_24
  · exact (jordan_comm (nativeWords 24) (nativeWords 22)).trans native_product_22_24
  · exact (jordan_comm (nativeWords 24) (nativeWords 23)).trans native_product_23_24
  · exact native_product_24_24
  · exact native_product_24_25
  · exact native_product_24_26

end
end Glennie.Compact.NativeWordTableR01
