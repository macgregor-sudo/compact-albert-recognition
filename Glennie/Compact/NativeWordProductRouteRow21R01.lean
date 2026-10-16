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

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeffRow21 : Fin 27 → Fin 27 → ℝ := ![productCoeff_00_21, productCoeff_01_21, productCoeff_02_21, productCoeff_03_21, productCoeff_04_21, productCoeff_05_21, productCoeff_06_21, productCoeff_07_21, productCoeff_08_21, productCoeff_09_21, productCoeff_10_21, productCoeff_11_21, productCoeff_12_21, productCoeff_13_21, productCoeff_14_21, productCoeff_15_21, productCoeff_16_21, productCoeff_17_21, productCoeff_18_21, productCoeff_19_21, productCoeff_20_21, productCoeff_21_21, productCoeff_21_22, productCoeff_21_23, productCoeff_21_24, productCoeff_21_25, productCoeff_21_26]

theorem native_product_row21 (j : Fin 27) :
    jordan (nativeWords 21) (nativeWords j) =
      ∑ k : Fin 27, productCoeffRow21 j k • nativeWords k := by
  fin_cases j
  · exact (jordan_comm (nativeWords 21) (nativeWords 0)).trans native_product_00_21
  · exact (jordan_comm (nativeWords 21) (nativeWords 1)).trans native_product_01_21
  · exact (jordan_comm (nativeWords 21) (nativeWords 2)).trans native_product_02_21
  · exact (jordan_comm (nativeWords 21) (nativeWords 3)).trans native_product_03_21
  · exact (jordan_comm (nativeWords 21) (nativeWords 4)).trans native_product_04_21
  · exact (jordan_comm (nativeWords 21) (nativeWords 5)).trans native_product_05_21
  · exact (jordan_comm (nativeWords 21) (nativeWords 6)).trans native_product_06_21
  · exact (jordan_comm (nativeWords 21) (nativeWords 7)).trans native_product_07_21
  · exact (jordan_comm (nativeWords 21) (nativeWords 8)).trans native_product_08_21
  · exact (jordan_comm (nativeWords 21) (nativeWords 9)).trans native_product_09_21
  · exact (jordan_comm (nativeWords 21) (nativeWords 10)).trans native_product_10_21
  · exact (jordan_comm (nativeWords 21) (nativeWords 11)).trans native_product_11_21
  · exact (jordan_comm (nativeWords 21) (nativeWords 12)).trans native_product_12_21
  · exact (jordan_comm (nativeWords 21) (nativeWords 13)).trans native_product_13_21
  · exact (jordan_comm (nativeWords 21) (nativeWords 14)).trans native_product_14_21
  · exact (jordan_comm (nativeWords 21) (nativeWords 15)).trans native_product_15_21
  · exact (jordan_comm (nativeWords 21) (nativeWords 16)).trans native_product_16_21
  · exact (jordan_comm (nativeWords 21) (nativeWords 17)).trans native_product_17_21
  · exact (jordan_comm (nativeWords 21) (nativeWords 18)).trans native_product_18_21
  · exact (jordan_comm (nativeWords 21) (nativeWords 19)).trans native_product_19_21
  · exact (jordan_comm (nativeWords 21) (nativeWords 20)).trans native_product_20_21
  · exact native_product_21_21
  · exact native_product_21_22
  · exact native_product_21_23
  · exact native_product_21_24
  · exact native_product_21_25
  · exact native_product_21_26

end
end Glennie.Compact.NativeWordTableR01
