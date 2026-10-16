/- Finite 27-branch product routing for this row. -/
module
public import Glennie.Compact.NativeWordProductRow00R01
public import Glennie.Compact.NativeWordProductRow01R01
public import Glennie.Compact.NativeWordProductRow02R01
public import Glennie.Compact.NativeWordProductRow03R01
public import Glennie.Compact.NativeWordProductRow04R01
public import Glennie.Compact.NativeWordProductRow05R01
public import Glennie.Compact.NativeWordProductRow06R01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeffRow6 : Fin 27 → Fin 27 → ℝ := ![productCoeff_00_06, productCoeff_01_06, productCoeff_02_06, productCoeff_03_06, productCoeff_04_06, productCoeff_05_06, productCoeff_06_06, productCoeff_06_07, productCoeff_06_08, productCoeff_06_09, productCoeff_06_10, productCoeff_06_11, productCoeff_06_12, productCoeff_06_13, productCoeff_06_14, productCoeff_06_15, productCoeff_06_16, productCoeff_06_17, productCoeff_06_18, productCoeff_06_19, productCoeff_06_20, productCoeff_06_21, productCoeff_06_22, productCoeff_06_23, productCoeff_06_24, productCoeff_06_25, productCoeff_06_26]

theorem native_product_row6 (j : Fin 27) :
    jordan (nativeWords 6) (nativeWords j) =
      ∑ k : Fin 27, productCoeffRow6 j k • nativeWords k := by
  fin_cases j
  · exact (jordan_comm (nativeWords 6) (nativeWords 0)).trans native_product_00_06
  · exact (jordan_comm (nativeWords 6) (nativeWords 1)).trans native_product_01_06
  · exact (jordan_comm (nativeWords 6) (nativeWords 2)).trans native_product_02_06
  · exact (jordan_comm (nativeWords 6) (nativeWords 3)).trans native_product_03_06
  · exact (jordan_comm (nativeWords 6) (nativeWords 4)).trans native_product_04_06
  · exact (jordan_comm (nativeWords 6) (nativeWords 5)).trans native_product_05_06
  · exact native_product_06_06
  · exact native_product_06_07
  · exact native_product_06_08
  · exact native_product_06_09
  · exact native_product_06_10
  · exact native_product_06_11
  · exact native_product_06_12
  · exact native_product_06_13
  · exact native_product_06_14
  · exact native_product_06_15
  · exact native_product_06_16
  · exact native_product_06_17
  · exact native_product_06_18
  · exact native_product_06_19
  · exact native_product_06_20
  · exact native_product_06_21
  · exact native_product_06_22
  · exact native_product_06_23
  · exact native_product_06_24
  · exact native_product_06_25
  · exact native_product_06_26

end
end Glennie.Compact.NativeWordTableR01
