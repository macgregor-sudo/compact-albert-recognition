module
public import Glennie.Compact.GeneratedRecognitionR01
public import Glennie.Compact.NativeWordProductTableR01
public import Glennie.Compact.NativeWordMomentAggregationR01

/- Literal finite scalar observations using the proved native table and raw Gram.
No native table, Gram, or positivity premise is added to the consumer. -/
@[expose] public section
namespace Glennie.Compact.MarkedModelConsumerCandidate
open Module Glennie Glennie.Compact.NativeWordTableR01
open Glennie.Compact.NativeWordTableR01.ClosureCandidate
open scoped BigOperators
noncomputable section
set_option autoImplicit false

 /-- The computed literal coefficients equal the actual native basis coordinates. -/
 theorem referenceCoeff_eq_productCoefficients (i j k : Fin 27) :
    referenceCoeff i j k = productCoefficients i j k := by
  unfold referenceCoeff
  rw [native_product_table]
  simpa only [wordBasis_eq_nativeWords] using
    congrFun (wordBasis.repr_sum_self (productCoefficients i j)) k

section LiteralConsumer
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

 /-- C=productCoefficients; G=rawGramData; b=productPairingData;
h=productNormSqData. These are only finite scalar observations. -/
 structure LiteralMatch27 (e : E) (a : Fin 3 → E)
    (j : E →ₗ[ℝ] E →ₗ[ℝ] E) : Prop where
  gram : ∀ i k,
    Inner.inner ℝ (candidateWords e a j i) (candidateWords e a j k) = rawGramData i k
  mixed : ∀ i k l,
    Inner.inner ℝ (j (candidateWords e a j i) (candidateWords e a j k))
      (candidateWords e a j l) = productPairingData i k l
  product_sq : ∀ i k,
    Inner.inner ℝ (j (candidateWords e a j i) (candidateWords e a j k))
      (j (candidateWords e a j i) (candidateWords e a j k)) = productNormSqData i k

 theorem literalMatch27_to_match27 (e : E) (a : Fin 3 → E)
    (j : E →ₗ[ℝ] E →ₗ[ℝ] E) (h : LiteralMatch27 e a j) : Match27 e a j := by
  refine ⟨?_, ?_, ?_⟩
  · intro i k
    exact (h.gram i k).trans (rawGram_native i k).symm
  · intro i k l
    exact (h.mixed i k l).trans (productPairingData_native i k l).symm
  · intro i k
    exact (h.product_sq i k).trans (productNormSqData_native i k).symm

 theorem match27_iff_literalMatch27 (e : E) (a : Fin 3 → E)
    (j : E →ₗ[ℝ] E →ₗ[ℝ] E) : Match27 e a j ↔ LiteralMatch27 e a j := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i k
      exact (h.gram i k).trans (rawGram_native i k)
    · intro i k l
      exact (h.mixed i k l).trans (productPairingData_native i k l)
    · intro i k
      exact (h.product_sq i k).trans (productNormSqData_native i k)
  · exact literalMatch27_to_match27 e a j

 /-- Direct literal C table closure from literal G,b,h matching, without extra premises. -/
 theorem literal_matched_products (e : E) (a : Fin 3 → E)
    (j : E →ₗ[ℝ] E →ₗ[ℝ] E) (h : LiteralMatch27 e a j) (i k : Fin 27) :
    j (candidateWords e a j i) (candidateWords e a j k) =
      ∑ l, productCoefficients i k l • candidateWords e a j l := by
  have hMatch := literalMatch27_to_match27 e a j h
  have ht := candidate_scaled_table_of_scalar_data (candidateWords e a j) j 1
    productCoefficients
    (by intro r s; simpa only [one_smul] using native_product_table r s)
    hMatch.gram hMatch.mixed hMatch.product_sq
  simpa only [one_smul] using ht i k

 /-- The existing one-A generated-subalgebra recognition producer consumes the
literal arrays through an equivalent scalar predicate. Ambient directions remain allowed. -/
 theorem literal_generated_marked_recognition (e : E) (a : Fin 3 → E)
    (j : E →ₗ[ℝ] E →ₗ[ℝ] E) (h : LiteralMatch27 e a j) :
    wordSpan e a j = generated e a j ∧
    Nonempty (MarkedModelEquiv (wordSpan e a j) (spanUnit e a j)
      (fun x y => spanProduct e a j (literalMatch27_to_match27 e a j h) x y)
      (Inner.inner ℝ) (spanMarks e a j) marks) :=
  generated_marked_recognition e a j (literalMatch27_to_match27 e a j h)

end LiteralConsumer
end
end Glennie.Compact.MarkedModelConsumerCandidate
