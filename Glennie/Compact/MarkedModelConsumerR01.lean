/- Common linear/unit/product/raw-pairing consumer interface.
The geometric normalization adapter uses raw B = 3 logHessian. -/
module
public import AlbertGeometry.IntrinsicLocalReconstruction
public import Glennie.NativeGenerationEndpointR01
public import Glennie.Compact.NativeWordTableBasisR01
public import Glennie.Compact.CyclicTraceNullR01

@[expose] public section
namespace Glennie.Compact.MarkedModelConsumerCandidate
noncomputable section
open Glennie
open Glennie.Compact.CyclicTraceNullR01
open Glennie.Compact.NativeWordTableR01
open AlbertGeometry.Cubic AlbertGeometry.BasedNormAdjointTransport
open AlbertGeometry.IntrinsicLocalTransport
open scoped BigOperators
set_option autoImplicit false

/-- Exactly the existing downstream linear/unit/product/metric boundary,
with the source metric written in the native raw normalization. -/
structure ModelEquiv (E : Type*) [AddCommGroup E] [Module ℝ E]
    (e : E) (j : E → E → E) (B : E → E → ℝ) where
  A : E ≃ₗ[ℝ] Albert
  map_unit : A e = 1
  map_product : ∀ x y, A (j x y) = jordan (A x) (A y)
  map_metric : ∀ x y, B x y = inner (A x) (A y)

/-- Optional marks supplement the same common equivalence interface. -/
structure MarkedModelEquiv (E : Type*) [AddCommGroup E] [Module ℝ E]
    (e : E) (j : E → E → E) (B : E → E → ℝ)
    (a : Fin 3 → E) (b : Fin 3 → Albert) extends ModelEquiv E e j B where
  map_marks : ∀ i, A (a i) = b i

section Consumers
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {e : E} {j : E → E → E} {B : E → E → ℝ}

/-- Ordered frames use raw trace B(x,e), the source unit, and source product. -/
structure ModelFrame (p : Fin 3 → E) : Prop where
  trace_one : ∀ i, B (p i) e = 1
  idempotent : ∀ i, j (p i) (p i) = p i
  orthogonal : ∀ i k, i ≠ k → j (p i) (p k) = 0
  sum_unit : p 0 + p 1 + p 2 = e

 theorem map_trace (I : ModelEquiv E e j B) (x : E) : B x e = trace (I.A x) := by
  rw [I.map_metric, I.map_unit, inner_unit_right]

 theorem frame_iff (I : ModelEquiv E e j B) (p : Fin 3 → E) :
    ModelFrame (e := e) (j := j) (B := B) p ↔ Frame (fun i => I.A (p i)) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      rw [← map_trace I]
      exact h.trace_one i
    · intro i
      rw [← I.map_product, h.idempotent]
    · intro i k hik
      rw [← I.map_product, h.orthogonal i k hik, map_zero]
    · simpa only [← map_add, h.sum_unit, I.map_unit]
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      rw [map_trace I]
      exact h.trace_one i
    · intro i
      apply I.A.injective
      rw [I.map_product]
      exact h.idempotent i
    · intro i k hik
      apply I.A.injective
      rw [I.map_product, map_zero]
      exact h.orthogonal i k hik
    · apply I.A.injective
      simpa only [map_add, I.map_unit] using h.sum_unit

 theorem map_quadratic (I : ModelEquiv E e j B) (x z : E) :
    I.A (quadraticWith j x z) = U (I.A x) (I.A z) := by
  simp only [quadraticWith, map_sub, map_smul, I.map_product, U]

 theorem map_response (I : ModelEquiv E e j B) (x y z : E) :
    phiWith j B x y z = phi (I.A x) (I.A y) (I.A z) := by
  simp only [phiWith, I.map_metric, map_sub, map_quadratic, I.map_product, phi]

/-- The generic equivalence consumer needs no ambient recognition route,
frame, spectral, generation, or spanning premise. Generation stays unital. -/
 theorem unital_generation_of_response_ne_zero (I : ModelEquiv E e j B)
    (x y z : E) (hn : phiWith j B x y z ≠ 0)
    (K : Submodule ℝ E) (heK : e ∈ K)
    (hK : ∀ p ∈ K, ∀ q ∈ K, j p q ∈ K)
    (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K) : K = ⊤ := by
  let L := K.map I.A.toLinearMap
  have h1 : (1 : Albert) ∈ L := ⟨e, heK, I.map_unit⟩
  have hJ : ∀ p ∈ L, ∀ q ∈ L, jordan p q ∈ L := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    exact ⟨j p q, hK p hp q hq, I.map_product p q⟩
  have hn' : phi (I.A x) (I.A y) (I.A z) ≠ 0 := by
    rw [← map_response I x y z]
    exact hn
  have hL : L = ⊤ := Glennie.NativeGenerationEndpointR01.eq_top_of_phi_ne_zero
    L h1 hJ (I.A x) (I.A y) (I.A z)
    ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩ hn'
  apply top_unique
  intro t _
  have ht : I.A t ∈ L := by rw [hL]; trivial
  obtain ⟨s, hs, hst⟩ := ht
  have heq : s = t := I.A.injective hst
  exact heq ▸ hs
end Consumers

section GeometricAdapter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
variable (P : SymmetricTrilinearForm E) (e : E)
  (he : diagonalCubic P.form e = 1)
  (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u)

/-- Raw source B; the recognized geometric metric was B/3. -/
def rawMetric (x y : E) : ℝ := 3 * logHessianForm P e x y

/-- Consume the actual geometric producer's fields, without adding a norm,
curvature, determinant, or equivalence assumption to that producer. -/
def ofGeometricData (d : AlbertGeometry.IntrinsicLocalReconstruction.Data P e he hp) :
    ModelEquiv E e (sourceProduct P e he hp) (rawMetric P e) where
  A := d.A
  map_unit := d.map_unit
  map_product := d.map_product
  map_metric := by
    intro x y
    change 3 * logHessianForm P e x y = trace (jordan (d.A x) (d.A y))
    rw [d.map_metric x y]
    ring

/-- Recover exactly the existing metric input expected by intrinsic consumers. -/
theorem metric_for_existing_consumer
    (I : ModelEquiv E e (sourceProduct P e he hp) (rawMetric P e)) (x y : E) :
    logHessianForm P e x y = trace (jordan (I.A x) (I.A y)) / 3 := by
  have h := I.map_metric x y
  change 3 * logHessianForm P e x y = trace (jordan (I.A x) (I.A y)) at h
  linarith
end GeometricAdapter

section MatchingData
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The selected exact 27 syntactic Jordan words evaluated in the candidate.
The ambient product is bilinear, with no Jordan identity or classification input. -/
def candidateWords (e : E) (a : Fin 3 → E) (j : E →ₗ[ℝ] E →ₗ[ℝ] E) :
    Fin 27 → E := fun i => eval e a (fun x y => j x y) (words i)

theorem candidateWords_unit (e : E) (a : Fin 3 → E)
    (j : E →ₗ[ℝ] E →ₗ[ℝ] E) : candidateWords e a j 0 = e := rfl

theorem candidateWords_mark0 (e : E) (a : Fin 3 → E)
    (j : E →ₗ[ℝ] E →ₗ[ℝ] E) : candidateWords e a j 1 = a 0 := rfl

theorem candidateWords_mark1 (e : E) (a : Fin 3 → E)
    (j : E →ₗ[ℝ] E →ₗ[ℝ] E) : candidateWords e a j 2 = a 1 := rfl

theorem candidateWords_mark2 (e : E) (a : Fin 3 → E)
    (j : E →ₗ[ℝ] E →ₗ[ℝ] E) : candidateWords e a j 3 = a 2 := rfl

/-- These are finite scalar observations; none supplies span/closure/recognition. -/
structure Match27 (e : E) (a : Fin 3 → E) (j : E →ₗ[ℝ] E →ₗ[ℝ] E) : Prop where
  gram : ∀ i k,
    Inner.inner ℝ (candidateWords e a j i) (candidateWords e a j k) =
      inner (nativeWords i) (nativeWords k)
  mixed : ∀ i k l,
    Inner.inner ℝ (j (candidateWords e a j i) (candidateWords e a j k))
      (candidateWords e a j l) =
      inner (jordan (nativeWords i) (nativeWords k)) (nativeWords l)
  product_sq : ∀ i k,
    Inner.inner ℝ (j (candidateWords e a j i) (candidateWords e a j k))
      (j (candidateWords e a j i) (candidateWords e a j k)) =
      inner (jordan (nativeWords i) (nativeWords k))
        (jordan (nativeWords i) (nativeWords k))

/-- The intended output carrier, allowing unused ambient directions. -/
def wordSpan (e : E) (a : Fin 3 → E) (j : E →ₗ[ℝ] E →ₗ[ℝ] E) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range (candidateWords e a j))

/-- The generated unital product-closed submodule, independently of the word list. -/
def generated (e : E) (a : Fin 3 → E) (j : E →ₗ[ℝ] E →ₗ[ℝ] E) : Submodule ℝ E :=
  sInf {K : Submodule ℝ E | e ∈ K ∧ (∀ i, a i ∈ K) ∧
    (∀ x ∈ K, ∀ y ∈ K, j x y ∈ K)}

/- Closure, generation, and fixed-mark uniqueness from Match27 are proved in
GeneratedRecognitionR01; these definitions contain no recognition premise. -/
end MatchingData
end
end Glennie.Compact.MarkedModelConsumerCandidate
