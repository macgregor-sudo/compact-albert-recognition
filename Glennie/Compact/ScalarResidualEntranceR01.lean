module
public import Glennie.Compact.WordTableClosureR01
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.Ring

/- Division-free finite scalar entrance from raw Gram and product moments. -/
@[expose] public section
namespace Glennie.Compact.NativeWordTableR01.ClosureCandidate
open Module Glennie Glennie.Compact.NativeWordTableR01
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

 /-- Exact scalar expression for the norm square of the denominator-cleared residual. -/
 def residualScalar (v : Fin 27 → E) (p : E) (D : ℝ) (c : Fin 27 → ℝ) : ℝ :=
    D^2 * Inner.inner ℝ p p -
    2*D*(∑ k, c k * Inner.inner ℝ p (v k)) +
    ∑ k, ∑ l, c k*c l * Inner.inner ℝ (v k) (v l)

 theorem residual_norm_sq (v : Fin 27 → E) (p : E) (D : ℝ) (c : Fin 27 → ℝ) :
    ‖D • p - ∑ k, c k • v k‖^2 = residualScalar v p D c := by
  have hp : Inner.inner ℝ p (∑ k, c k • v k) =
      ∑ k, c k * Inner.inner ℝ p (v k) := by
    simp only [inner_sum, real_inner_smul_right]
  have hs : ‖∑ k, c k • v k‖^2 =
      ∑ k, ∑ l, c k*c l * Inner.inner ℝ (v k) (v l) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [sum_inner, inner_sum, real_inner_smul_left,
      real_inner_smul_right, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    rw [real_inner_comm (v l) (v k)]
    ring
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_left, hp, hs]
  rw [← real_inner_self_eq_norm_sq p]
  dsimp [residualScalar]
  ring

 /-- Positive definite Hilbert geometry turns a nonpositive scalar residual into closure. -/
 theorem residual_zero_of_scalar_nonpos (v : Fin 27 → E) (p : E)
    (D : ℝ) (c : Fin 27 → ℝ) (h : residualScalar v p D c ≤ 0) :
    D • p = ∑ k, c k • v k := by
  have hn : ‖D • p-∑ k, c k • v k‖^2 = 0 :=
    le_antisymm ((residual_norm_sq v p D c).trans_le h) (sq_nonneg _)
  have hz : D • p-∑ k, c k • v k = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  exact sub_eq_zero.mp hz

 theorem native_word_gram_positive : (Matrix.gram ℝ nativeWords).PosDef :=
  Matrix.posDef_gram_of_linearIndependent nativeWords_linearIndependent

 /-- The candidate family is independent because its Gram equals a proved positive Gram. -/
 theorem candidate_words_linearIndependent (v : Fin 27 → E)
    (hGram : ∀ i j, Inner.inner ℝ (v i) (v j) =
      Inner.inner ℝ (nativeWords i) (nativeWords j)) : LinearIndependent ℝ v := by
  have hg : Matrix.gram ℝ v = Matrix.gram ℝ nativeWords := by
    ext i j
    exact hGram i j
  apply Matrix.linearIndependent_of_posDef_gram
  rw [hg]
  exact native_word_gram_positive

 /-- Whole-carrier spanning uses the honest 27-dimensional hypothesis.
Without it the same Gram argument establishes only a basis of the 27-word span. -/
 def gramDerivedBasis [FiniteDimensional ℝ E] (v : Fin 27 → E)
    (hGram : ∀ i j, Inner.inner ℝ (v i) (v j) =
      Inner.inner ℝ (nativeWords i) (nativeWords j))
    (hDim : Module.finrank ℝ E = 27) : Basis (Fin 27) ℝ E :=
  basisOfLinearIndependentOfCardEqFinrank (candidate_words_linearIndependent v hGram)
    (by simpa using hDim.symm)

 theorem gramDerivedBasis_apply [FiniteDimensional ℝ E] (v : Fin 27 → E)
    (hGram : ∀ i j, Inner.inner ℝ (v i) (v j) =
      Inner.inner ℝ (nativeWords i) (nativeWords j))
    (hDim : Module.finrank ℝ E = 27) (i : Fin 27) :
    gramDerivedBasis v hGram hDim i = v i := by
  simp [gramDerivedBasis]

 /-- Matching finite Gram, product-pairing and squared-product data forces each
cleared product residual to vanish. No candidate table equality is assumed. -/
 theorem candidate_scaled_table_of_scalar_data
    (v : Fin 27 → E) (jE : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (D : ℝ) (C : Fin 27 → Fin 27 → Fin 27 → ℝ)
    (hNative : ∀ i j, D • jordan (nativeWords i) (nativeWords j) =
      ∑ k, C i j k • nativeWords k)
    (hGram : ∀ k l, Inner.inner ℝ (v k) (v l) =
      Inner.inner ℝ (nativeWords k) (nativeWords l))
    (hPair : ∀ i j k, Inner.inner ℝ (jE (v i) (v j)) (v k) =
      Inner.inner ℝ (jordan (nativeWords i) (nativeWords j)) (nativeWords k))
    (hSquare : ∀ i j, Inner.inner ℝ (jE (v i) (v j)) (jE (v i) (v j)) =
      Inner.inner ℝ (jordan (nativeWords i) (nativeWords j))
        (jordan (nativeWords i) (nativeWords j))) :
    ∀ i j, D • jE (v i) (v j) = ∑ k, C i j k • v k := by
  intro i j
  have hRef : residualScalar nativeWords (jordan (nativeWords i) (nativeWords j)) D (C i j) = 0 := by
    rw [← residual_norm_sq, hNative i j, sub_self, norm_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0)]
  have hEq : residualScalar v (jE (v i) (v j)) D (C i j) =
      residualScalar nativeWords (jordan (nativeWords i) (nativeWords j)) D (C i j) := by
    simp only [residualScalar, hGram, hPair, hSquare]
  exact residual_zero_of_scalar_nonpos v (jE (v i) (v j)) D (C i j)
    (by rw [hEq, hRef])

 /-- Closed finite scalar entrance to a marked, unital native product equivalence.
The candidate basis is produced from positive Gram and dimension, not assumed. -/
 theorem marked_product_equiv_of_scalar_data [FiniteDimensional ℝ E]
    (v : Fin 27 → E) (jE : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (e : E) (a : Fin 3 → E)
    (he : v 0 = e) (hx : v 1 = a 0) (hy : v 2 = a 1) (hz : v 3 = a 2)
    (hDim : Module.finrank ℝ E = 27)
    (D : ℝ) (hD : D ≠ 0) (C : Fin 27 → Fin 27 → Fin 27 → ℝ)
    (hNative : ∀ i j, D • jordan (nativeWords i) (nativeWords j) =
      ∑ k, C i j k • nativeWords k)
    (hGram : ∀ k l, Inner.inner ℝ (v k) (v l) =
      Inner.inner ℝ (nativeWords k) (nativeWords l))
    (hPair : ∀ i j k, Inner.inner ℝ (jE (v i) (v j)) (v k) =
      Inner.inner ℝ (jordan (nativeWords i) (nativeWords j)) (nativeWords k))
    (hSquare : ∀ i j, Inner.inner ℝ (jE (v i) (v j)) (jE (v i) (v j)) =
      Inner.inner ℝ (jordan (nativeWords i) (nativeWords j))
        (jordan (nativeWords i) (nativeWords j))) :
    ∃ A : E ≃ₗ[ℝ] Albert, A e = 1 ∧
      (∀ x y, A (jE x y) = jordan (A x) (A y)) ∧
      (∀ x y, Inner.inner ℝ x y = Glennie.inner (A x) (A y)) ∧
      A (a 0) = witnessX ∧ A (a 1) = witnessY ∧ A (a 2) = witnessZ := by
  let b := gramDerivedBasis v hGram hDim
  have hb : ∀ i, b i = v i := gramDerivedBasis_apply v hGram hDim
  have ht := candidate_scaled_table_of_scalar_data v jE D C hNative hGram hPair hSquare
  have hTable : ∀ i j, D • jE (b i) (b j) = ∑ k, C i j k • b k := by
    simpa only [hb] using ht
  refine ⟨markedLinearEquiv b, ?_, map_product_of_scaled_table b jE D hD C hNative hTable,
    ?_, ?_, ?_, ?_⟩
  · rw [← he, ← hb 0, markedLinearEquiv_basis, nativeWords_unit]
  · exact map_metric_of_basis b
      (_root_.innerₗ E)
      (_root_.innerₗ Albert)
      (by intro i j; change Inner.inner ℝ (b i) (b j) = _; rw [hb i, hb j]; exact hGram i j)
  · rw [← hx, ← hb 1, markedLinearEquiv_basis, nativeWords_markX]
  · rw [← hy, ← hb 2, markedLinearEquiv_basis, nativeWords_markY]
  · rw [← hz, ← hb 3, markedLinearEquiv_basis, nativeWords_markZ]

end
end Glennie.Compact.NativeWordTableR01.ClosureCandidate
