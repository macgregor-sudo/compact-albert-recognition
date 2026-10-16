/- product moments from the literal native product and Gram matrices. -/
module
public import Glennie.Compact.NativeWordRawGramR01
public import Glennie.Compact.NativeWordProductTableR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Module Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

/-- Exact product pairings computed from literal checked C and G. -/
def productPairingData (i j k : Fin 27) : ℝ :=
  ∑ r, productCoefficients i j r * rawGramData r k

/-- Exact product-square moments computed from literal checked C and G. -/
def productNormSqData (i j : Fin 27) : ℝ :=
  ∑ r, ∑ s, productCoefficients i j r * productCoefficients i j s * rawGramData r s

theorem productPairingData_native (i j k : Fin 27) :
    inner (jordan (nativeWords i) (nativeWords j)) (nativeWords k) =
      productPairingData i j k := by
  rw [native_product_table, raw_inner_sum_left]
  simp only [rawGram_native, productPairingData]

theorem productNormSqData_native (i j : Fin 27) :
    inner (jordan (nativeWords i) (nativeWords j))
      (jordan (nativeWords i) (nativeWords j)) = productNormSqData i j := by
  simp only [native_product_table]
  exact raw_inner_word_sums _ _

theorem native_product_residual_zero (i j : Fin 27) :
    jordan (nativeWords i) (nativeWords j) -
      ∑ k, productCoefficients i j k • nativeWords k = 0 := by
  rw [native_product_table, sub_self]

end
end Glennie.Compact.NativeWordTableR01
