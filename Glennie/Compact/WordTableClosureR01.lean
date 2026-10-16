module
public import Glennie.Compact.NativeWordTableBasisR01
public import Glennie.Hilbert
public import Mathlib.LinearAlgebra.BilinearMap

/- Finite-basis closure kernel; no determinant inverse or division by candidate data. -/
@[expose] public section
namespace Glennie.Compact.NativeWordTableR01.ClosureCandidate
open Module Glennie Glennie.Compact.NativeWordTableR01
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

 /-- Small closure kernel: a bilinear residual zero on basis pairs is zero everywhere. -/
 theorem bilinear_residual_zero (b : Basis (Fin 27) ℝ E)
    (r : E →ₗ[ℝ] E →ₗ[ℝ] F) (hr : ∀ i j, r (b i) (b j) = 0) : r = 0 := by
  apply b.ext
  intro i
  apply b.ext
  intro j
  exact hr i j

 theorem bilinear_eq_of_basis (b : Basis (Fin 27) ℝ E)
    (p q : E →ₗ[ℝ] E →ₗ[ℝ] F)
    (h : ∀ i j, p (b i) (b j) = q (b i) (b j)) : p = q := by
  apply b.ext
  intro i
  apply b.ext
  intro j
  exact h i j

 def markedLinearEquiv (b : Basis (Fin 27) ℝ E) : E ≃ₗ[ℝ] Albert :=
  b.equiv wordBasis (Equiv.refl (Fin 27))

 theorem markedLinearEquiv_basis (b : Basis (Fin 27) ℝ E) (i : Fin 27) :
    markedLinearEquiv b (b i) = nativeWords i := by
  rw [markedLinearEquiv, Basis.equiv_apply]
  exact wordBasis_eq_nativeWords i

 /-- Full denominator-cleared table agreement forces product preservation.
D is a fixed nonzero certificate scale; no D inverse appears in the proof. -/
 theorem map_product_of_scaled_table
    (b : Basis (Fin 27) ℝ E) (jE : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (D : ℝ) (hD : D ≠ 0) (C : Fin 27 → Fin 27 → Fin 27 → ℝ)
    (hNative : ∀ i j, D • jordan (nativeWords i) (nativeWords j) =
      ∑ k, C i j k • nativeWords k)
    (hCandidate : ∀ i j, D • jE (b i) (b j) = ∑ k, C i j k • b k) :
    ∀ x y, markedLinearEquiv b (jE x y) =
      jordan (markedLinearEquiv b x) (markedLinearEquiv b y) := by
  let A := markedLinearEquiv b
  have hBasis : ∀ i j, A (jE (b i) (b j)) = jordan (A (b i)) (A (b j)) := by
    intro i j
    have hs : D • A (jE (b i) (b j)) = D • jordan (A (b i)) (A (b j)) := by
      calc
        _ = A (D • jE (b i) (b j)) := (map_smul A D _).symm
        _ = A (∑ k, C i j k • b k) := congrArg A (hCandidate i j)
        _ = ∑ k, C i j k • nativeWords k := by
          simp only [map_sum, map_smul, A, markedLinearEquiv_basis]
        _ = D • jordan (nativeWords i) (nativeWords j) := (hNative i j).symm
        _ = _ := by simp only [A, markedLinearEquiv_basis]
    have hz : D • (A (jE (b i) (b j)) - jordan (A (b i)) (A (b j))) = 0 := by
      rw [smul_sub, hs, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left hD)
  have he : jE.compr₂ A.toLinearMap =
      jordanLinear.compl₁₂ A.toLinearMap A.toLinearMap := by
    apply bilinear_eq_of_basis b
    exact hBasis
  intro x y
  exact congrArg (fun r : E →ₗ[ℝ] E →ₗ[ℝ] Albert => r x y) he

 /-- Matching bilinear forms on the same ordered basis extends with the same A. -/
 theorem map_metric_of_basis
    (b : Basis (Fin 27) ℝ E)
    (BE : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (BA : Albert →ₗ[ℝ] Albert →ₗ[ℝ] ℝ)
    (hGram : ∀ i j, BE (b i) (b j) = BA (nativeWords i) (nativeWords j)) :
    ∀ x y, BE x y = BA (markedLinearEquiv b x) (markedLinearEquiv b y) := by
  have he : BE = BA.compl₁₂ (markedLinearEquiv b).toLinearMap
      (markedLinearEquiv b).toLinearMap := by
    apply bilinear_eq_of_basis b
    intro i j
    change BE (b i) (b j) = BA (markedLinearEquiv b (b i)) (markedLinearEquiv b (b j))
    rw [markedLinearEquiv_basis, markedLinearEquiv_basis]
    exact hGram i j
  intro x y
  exact congrArg (fun r : E →ₗ[ℝ] E →ₗ[ℝ] ℝ => r x y) he

 /-- Marked, unital product equivalence from the full finite table.
The output is the existing linear-equivalence-plus-map-laws interface, not a new structure. -/
 theorem exists_marked_product_equiv_of_scaled_table
    (b : Basis (Fin 27) ℝ E) (jE : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (e : E) (a : Fin 3 → E)
    (he : b 0 = e) (hx : b 1 = a 0) (hy : b 2 = a 1) (hz : b 3 = a 2)
    (D : ℝ) (hD : D ≠ 0) (C : Fin 27 → Fin 27 → Fin 27 → ℝ)
    (hNative : ∀ i j, D • jordan (nativeWords i) (nativeWords j) =
      ∑ k, C i j k • nativeWords k)
    (hCandidate : ∀ i j, D • jE (b i) (b j) = ∑ k, C i j k • b k) :
    ∃ A : E ≃ₗ[ℝ] Albert, A e = 1 ∧
      (∀ x y, A (jE x y) = jordan (A x) (A y)) ∧
      A (a 0) = witnessX ∧ A (a 1) = witnessY ∧ A (a 2) = witnessZ := by
  refine ⟨markedLinearEquiv b, ?_, map_product_of_scaled_table b jE D hD C hNative hCandidate,
    ?_, ?_, ?_⟩
  · rw [← he, markedLinearEquiv_basis, nativeWords_unit]
  · rw [← hx, markedLinearEquiv_basis, nativeWords_markX]
  · rw [← hy, markedLinearEquiv_basis, nativeWords_markY]
  · rw [← hz, markedLinearEquiv_basis, nativeWords_markZ]

end
end Glennie.Compact.NativeWordTableR01.ClosureCandidate
