/- Composition of the geometric and finite-word entrances.
The literal scalar observation contract is explicit. -/
module
public import Glennie.Compact.ExceptionalFrameworkR01
public import Glennie.Compact.LiteralWordTableBindingR01

@[expose] public section
namespace Glennie.Compact.ExceptionalFiniteWordCapstoneR01
open Glennie.Compact.MarkedModelConsumerCandidate
open Glennie.Compact.NativeWordTableR01
open scoped BigOperators
noncomputable section
set_option autoImplicit false

/-- Literal raw Gram, mixed-product, and product-square data recognize exactly
 the generated marked subalgebra. The unit/product/raw-metric equivalence is
 unique as a map for these fixed marks; the ambient carrier may be larger. -/
theorem literal_generated_unique_recognition
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E) (a : Fin 3 → E) (j : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (h : LiteralMatch27 e a j) :
    wordSpan e a j = generated e a j ∧
    ∃ I : MarkedModelEquiv (wordSpan e a j) (spanUnit e a j)
      (fun x y => spanProduct e a j (literalMatch27_to_match27 e a j h) x y)
      (Inner.inner ℝ) (spanMarks e a j) marks,
      ∀ J : MarkedModelEquiv (wordSpan e a j) (spanUnit e a j)
        (fun x y => spanProduct e a j (literalMatch27_to_match27 e a j h) x y)
        (Inner.inner ℝ) (spanMarks e a j) marks,
        J.A = I.A := by
  exact unique_generated_marked_recognition e a j (literalMatch27_to_match27 e a j h)

end
end Glennie.Compact.ExceptionalFiniteWordCapstoneR01
