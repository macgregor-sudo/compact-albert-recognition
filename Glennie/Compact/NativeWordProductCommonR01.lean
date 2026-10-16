/- Finite coefficient sums transported through the actual native coordinate map. -/
module
public import Glennie.Compact.NativeWordTableCoordinatesR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

/-- The actual ordered coordinate equivalence transports each finite sum.
    This lemma does not require the basis/inverse certificate. -/
theorem decode_sum_columns (c : Fin 27 → ℝ) :
    decode (∑ k : Fin 27, c k • columns k) =
      ∑ k : Fin 27, c k • nativeWords k := by
  change flatCoordinates.symm (∑ k : Fin 27, c k • columns k) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_smul]
  change c k • decode (columns k) = c k • nativeWords k
  rw [← nativeWords_decode]

end
end Glennie.Compact.NativeWordTableR01
