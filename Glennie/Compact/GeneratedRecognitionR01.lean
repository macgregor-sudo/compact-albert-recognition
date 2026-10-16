/- Generated-span marked recognition from finite scalar observations. -/
module
public import Glennie.Compact.MarkedModelConsumerR01
public import Glennie.Compact.ScalarResidualEntranceR01

@[expose] public section
namespace Glennie.Compact.MarkedModelConsumerCandidate
noncomputable section
open Module Glennie Glennie.Compact.NativeWordTableR01
open Glennie.Compact.NativeWordTableR01.ClosureCandidate
open scoped BigOperators
set_option autoImplicit false

section GeneratedRecognition
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (e : E) (a : Fin 3 → E) (j : E →ₗ[ℝ] E →ₗ[ℝ] E)

/-- Symbolic exact coefficients are produced by the actual native word basis.
Literal array binding is provided separately. -/
def referenceCoeff (i k l : Fin 27) : ℝ :=
  wordBasis.repr (jordan (nativeWords i) (nativeWords k)) l

theorem reference_table (i k : Fin 27) :
    (1 : ℝ) • jordan (nativeWords i) (nativeWords k) =
      ∑ l, referenceCoeff i k l • nativeWords l := by
  simpa only [one_smul, referenceCoeff, wordBasis_eq_nativeWords] using
    (wordBasis.sum_repr (jordan (nativeWords i) (nativeWords k))).symm

/-- Matching scalar observations produce actual vector-valued products. -/
theorem matched_products (h : Match27 e a j) (i k : Fin 27) :
    j (candidateWords e a j i) (candidateWords e a j k) =
      ∑ l, referenceCoeff i k l • candidateWords e a j l := by
  have ht := candidate_scaled_table_of_scalar_data
    (candidateWords e a j) j 1 referenceCoeff reference_table h.gram h.mixed h.product_sq
  simpa only [one_smul] using ht i k

theorem words_mem (i : Fin 27) : candidateWords e a j i ∈ wordSpan e a j :=
  Submodule.subset_span ⟨i, rfl⟩

theorem unit_mem : e ∈ wordSpan e a j := by
  simpa only [candidateWords_unit] using words_mem e a j 0

theorem marks_mem (i : Fin 3) : a i ∈ wordSpan e a j := by
  fin_cases i
  · change a 0 ∈ wordSpan e a j
    simpa only [candidateWords_mark0] using words_mem e a j 1
  · change a 1 ∈ wordSpan e a j
    simpa only [candidateWords_mark1] using words_mem e a j 2
  · change a 2 ∈ wordSpan e a j
    simpa only [candidateWords_mark2] using words_mem e a j 3

theorem wordSpan_closed (h : Match27 e a j) :
    ∀ x ∈ wordSpan e a j, ∀ y ∈ wordSpan e a j, j x y ∈ wordSpan e a j := by
  have hpair (i k : Fin 27) :
      j (candidateWords e a j i) (candidateWords e a j k) ∈ wordSpan e a j := by
    rw [matched_products e a j h i k]
    exact Submodule.sum_mem _ fun l _ =>
      Submodule.smul_mem _ _ (words_mem e a j l)
  have hleft (i : Fin 27) (y : E) (hy : y ∈ wordSpan e a j) :
      j (candidateWords e a j i) y ∈ wordSpan e a j := by
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      exact hpair i k
    | zero => simpa only [map_zero] using (wordSpan e a j).zero_mem
    | add y z hy hz ihy ihz =>
      simpa only [map_add] using (wordSpan e a j).add_mem ihy ihz
    | smul r y hy ih =>
      simpa only [map_smul] using (wordSpan e a j).smul_mem r ih
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact hleft i y hy
  | zero => simpa only [map_zero, LinearMap.zero_apply] using (wordSpan e a j).zero_mem
  | add x z hx hz ihx ihz =>
    simpa only [map_add, LinearMap.add_apply] using (wordSpan e a j).add_mem ihx ihz
  | smul r x hx ih =>
    simpa only [map_smul, LinearMap.smul_apply] using (wordSpan e a j).smul_mem r ih

/-- Every syntactic word lies in every unital marked product-closed submodule. -/
theorem eval_mem (K : Submodule ℝ E) (he : e ∈ K) (ha : ∀ i, a i ∈ K)
    (hj : ∀ x ∈ K, ∀ y ∈ K, j x y ∈ K) (w : Word) :
    eval e a (fun x y => j x y) w ∈ K := by
  induction w with
  | unit => exact he
  | mark i => exact ha i
  | mul u v ihu ihv => exact hj _ ihu _ ihv

theorem wordSpan_eq_generated (h : Match27 e a j) :
    wordSpan e a j = generated e a j := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨i, rfl⟩ := hx
    apply Submodule.mem_sInf.mpr
    intro K hK
    exact eval_mem e a j K hK.1 hK.2.1 hK.2.2 (words i)
  · apply sInf_le
    exact ⟨unit_mem e a j, marks_mem e a j, wordSpan_closed e a j h⟩

def spanUnit : wordSpan e a j := ⟨e, unit_mem e a j⟩
def spanMarks (i : Fin 3) : wordSpan e a j := ⟨a i, marks_mem e a j i⟩

def spanProduct (h : Match27 e a j) :
    wordSpan e a j →ₗ[ℝ] wordSpan e a j →ₗ[ℝ] wordSpan e a j where
  toFun x := {
    toFun y := ⟨j x.1 y.1, wordSpan_closed e a j h _ x.2 _ y.2⟩
    map_add' y z := by apply Subtype.ext; exact (j x.1).map_add y.1 z.1
    map_smul' r y := by apply Subtype.ext; exact (j x.1).map_smul r y.1
  }
  map_add' x z := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    exact LinearMap.congr_fun (j.map_add x.1 z.1) y.1
  map_smul' r x := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    exact LinearMap.congr_fun (j.map_smul r x.1) y.1

@[simp] theorem spanProduct_val (h : Match27 e a j) (x y : wordSpan e a j) :
    ((spanProduct e a j h x y : wordSpan e a j) : E) = j x.1 y.1 := rfl

def spanBasis (h : Match27 e a j) : Basis (Fin 27) ℝ (wordSpan e a j) :=
  Basis.span (candidate_words_linearIndependent (candidateWords e a j) h.gram)

@[simp] theorem spanBasis_val (h : Match27 e a j) (i : Fin 27) :
    ((spanBasis e a j h i : wordSpan e a j) : E) = candidateWords e a j i := by
  exact Basis.coe_span_apply _ i

def recognitionA (h : Match27 e a j) : wordSpan e a j ≃ₗ[ℝ] Albert :=
  markedLinearEquiv (spanBasis e a j h)

theorem recognitionA_basis (h : Match27 e a j) (i : Fin 27) :
    recognitionA e a j h (spanBasis e a j h i) = nativeWords i :=
  markedLinearEquiv_basis _ i

theorem span_table (h : Match27 e a j) (i k : Fin 27) :
    (1 : ℝ) • spanProduct e a j h (spanBasis e a j h i) (spanBasis e a j h k) =
      ∑ l, referenceCoeff i k l • spanBasis e a j h l := by
  simp only [one_smul]
  apply Subtype.ext
  change j ((spanBasis e a j h i : wordSpan e a j) : E)
    ((spanBasis e a j h k : wordSpan e a j) : E) =
    (wordSpan e a j).subtype (∑ l, referenceCoeff i k l • spanBasis e a j h l)
  simp only [map_sum, map_smul, Submodule.subtype_apply, spanBasis_val]
  exact matched_products e a j h i k

def recognizedModel (h : Match27 e a j) :
    MarkedModelEquiv (wordSpan e a j) (spanUnit e a j)
      (fun x y => spanProduct e a j h x y) (Inner.inner ℝ) (spanMarks e a j) marks where
  A := recognitionA e a j h
  map_unit := by
    have he : spanUnit e a j = spanBasis e a j h 0 := by
      apply Subtype.ext
      simpa only [spanBasis_val, spanUnit] using (candidateWords_unit e a j).symm
    rw [he, recognitionA_basis, nativeWords_unit]
  map_product := map_product_of_scaled_table (spanBasis e a j h) (spanProduct e a j h)
    1 one_ne_zero referenceCoeff reference_table (span_table e a j h)
  map_metric := map_metric_of_basis (spanBasis e a j h) (_root_.innerₗ (wordSpan e a j))
    (_root_.innerₗ Albert) (by
      intro i k
      change Inner.inner ℝ ((spanBasis e a j h i : wordSpan e a j) : E)
        ((spanBasis e a j h k : wordSpan e a j) : E) = _
      rw [spanBasis_val, spanBasis_val]
      exact h.gram i k)
  map_marks := by
    intro i
    fin_cases i
    · have he : spanMarks e a j 0 = spanBasis e a j h 1 := by
        apply Subtype.ext
        simpa only [spanBasis_val, spanMarks] using (candidateWords_mark0 e a j).symm
      change (recognitionA e a j h) (spanMarks e a j 0) = marks 0
      rw [he, recognitionA_basis, nativeWords_markX]
      rfl
    · have he : spanMarks e a j 1 = spanBasis e a j h 2 := by
        apply Subtype.ext
        simpa only [spanBasis_val, spanMarks] using (candidateWords_mark1 e a j).symm
      change (recognitionA e a j h) (spanMarks e a j 1) = marks 1
      rw [he, recognitionA_basis, nativeWords_markY]
      rfl
    · have he : spanMarks e a j 2 = spanBasis e a j h 3 := by
        apply Subtype.ext
        simpa only [spanBasis_val, spanMarks] using (candidateWords_mark2 e a j).symm
      change (recognitionA e a j h) (spanMarks e a j 2) = marks 2
      rw [he, recognitionA_basis, nativeWords_markZ]
      rfl

/-- The endpoint is an actual constructor from scalar matching on ambient E,
with no ambient dimension, closure, equivalence, or generation premise. -/
theorem generated_marked_recognition (h : Match27 e a j) :
    wordSpan e a j = generated e a j ∧
    Nonempty (MarkedModelEquiv (wordSpan e a j) (spanUnit e a j)
      (fun x y => spanProduct e a j h x y) (Inner.inner ℝ) (spanMarks e a j) marks) :=
  ⟨wordSpan_eq_generated e a j h, ⟨recognizedModel e a j h⟩⟩
end GeneratedRecognition

section Uniqueness
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {e : E} {j : E → E → E} {B : E → E → ℝ} {a : Fin 3 → E}

theorem map_eval_marked (I : MarkedModelEquiv E e j B a marks) (w : Word) :
    I.A (eval e a j w) = nativeEval w := by
  induction w with
  | unit => exact I.map_unit
  | mark i => exact I.map_marks i
  | mul u v ihu ihv =>
    change I.A (j (eval e a j u) (eval e a j v)) =
      jordan (nativeEval u) (nativeEval v)
    rw [I.map_product, ihu, ihv]
end Uniqueness

section SameA
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (e : E) (a : Fin 3 → E) (j : E →ₗ[ℝ] E →ₗ[ℝ] E)

theorem span_eval_val (h : Match27 e a j) (w : Word) :
    ((eval (spanUnit e a j) (spanMarks e a j)
      (fun x y => spanProduct e a j h x y) w : wordSpan e a j) : E) =
    eval e a (fun x y => j x y) w := by
  induction w with
  | unit => rfl
  | mark i => rfl
  | mul u v ihu ihv =>
    change j
      ((eval (spanUnit e a j) (spanMarks e a j)
        (fun x y => spanProduct e a j h x y) u : wordSpan e a j) : E)
      ((eval (spanUnit e a j) (spanMarks e a j)
        (fun x y => spanProduct e a j h x y) v : wordSpan e a j) : E) = _
    rw [ihu, ihv]
    rfl

theorem span_eval_word_eq_basis (h : Match27 e a j) (i : Fin 27) :
    eval (spanUnit e a j) (spanMarks e a j)
      (fun x y => spanProduct e a j h x y) (words i) = spanBasis e a j h i := by
  apply Subtype.ext
  rw [span_eval_val, spanBasis_val]
  rfl

/-- Uniqueness uses actual evaluations and all unit/mark/product laws,
not merely uniqueness of an unconstrained basis-matching map. -/
theorem marked_same_A (h : Match27 e a j)
    (I J : MarkedModelEquiv (wordSpan e a j) (spanUnit e a j)
      (fun x y => spanProduct e a j h x y) (Inner.inner ℝ) (spanMarks e a j) marks) :
    I.A = J.A := by
  have he : I.A.toLinearMap = J.A.toLinearMap := by
    apply (spanBasis e a j h).ext
    intro i
    change I.A (spanBasis e a j h i) = J.A (spanBasis e a j h i)
    rw [← span_eval_word_eq_basis e a j h i, map_eval_marked I, map_eval_marked J]
  apply LinearEquiv.ext
  intro x
  exact LinearMap.congr_fun he x

/-- Generated-span identity and uniqueness of the marked equivalence map. -/
theorem unique_generated_marked_recognition (h : Match27 e a j) :
    wordSpan e a j = generated e a j ∧
    ∃ I : MarkedModelEquiv (wordSpan e a j) (spanUnit e a j)
      (fun x y => spanProduct e a j h x y) (Inner.inner ℝ) (spanMarks e a j) marks,
      ∀ J : MarkedModelEquiv (wordSpan e a j) (spanUnit e a j)
        (fun x y => spanProduct e a j h x y) (Inner.inner ℝ) (spanMarks e a j) marks,
        J.A = I.A := by
  exact ⟨wordSpan_eq_generated e a j h, recognizedModel e a j h,
    fun J => marked_same_A e a j h J (recognizedModel e a j h)⟩
end SameA

end
end Glennie.Compact.MarkedModelConsumerCandidate
