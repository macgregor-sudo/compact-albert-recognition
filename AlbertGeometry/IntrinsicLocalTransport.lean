module

public import AlbertGeometry.ActualU2NativeGeometry
public import Glennie.Compact.LocalReconstruction

@[expose] public section
namespace AlbertGeometry.IntrinsicLocalTransport
noncomputable section

open Glennie
open AlbertGeometry.Cubic AlbertGeometry.BasedNormAdjointTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
variable (P : SymmetricTrilinearForm E) (e : E)
  (he : diagonalCubic P.form e = 1)
  (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u)

/-- The trace of the recovered algebra, specified by the actual based metric. -/
def sourceTrace (x : E) : ℝ := 3 * logHessianForm P e x e

/-- The recovered product from the based cubic and its nondegenerate trace form. -/
def sourceProduct (x y : E) : E :=
  intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y

/-- Ordered source frames use the recovered trace, product, and unit. -/
structure SourceFrame (p : Fin 3 → E) : Prop where
  trace_one : ∀ i, sourceTrace P e (p i) = 1
  idempotent : ∀ i, sourceProduct P e he hp (p i) (p i) = p i
  orthogonal : ∀ i j, i ≠ j → sourceProduct P e he hp (p i) (p j) = 0
  sum_unit : p 0 + p 1 + p 2 = e

abbrev SourceTriple (E : Type*) := Fin 3 → Fin 3 → E

def mapTriple (A : E ≃ₗ[ℝ] Albert) (T : SourceTriple E) :
    Glennie.Compact.Affine20.Triple := fun a i => A (T a i)

def pullTriple (A : E ≃ₗ[ℝ] Albert)
    (T : Glennie.Compact.Affine20.Triple) : SourceTriple E :=
  fun a i => A.symm (T a i)

theorem mapTriple_pullTriple (A : E ≃ₗ[ℝ] Albert)
    (T : Glennie.Compact.Affine20.Triple) :
    mapTriple A (pullTriple A T) = T := by
  funext a i
  exact A.apply_symm_apply _

theorem pullTriple_mapTriple (A : E ≃ₗ[ℝ] Albert)
    (T : SourceTriple E) : pullTriple A (mapTriple A T) = T := by
  funext a i
  exact A.symm_apply_apply _

theorem sourceTrace_eq (A : E ≃ₗ[ℝ] Albert) (hunit : A e = 1)
    (hmetric : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (A x) (A y)) / 3)
    (x : E) : sourceTrace P e x = trace (A x) := by
  rw [sourceTrace, hmetric x e, hunit, jordan_unit_right]
  ring

theorem sourceProduct_map (A : E ≃ₗ[ℝ] Albert)
    (hproduct : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y)) (x y : E) :
    A (sourceProduct P e he hp x y) = jordan (A x) (A y) :=
  hproduct x y

theorem sourceFrame_iff (A : E ≃ₗ[ℝ] Albert) (hunit : A e = 1)
    (hmetric : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (A x) (A y)) / 3)
    (hproduct : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y)) (p : Fin 3 → E) :
    SourceFrame P e he hp p ↔ Frame (fun i => A (p i)) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      rw [← sourceTrace_eq P e A hunit hmetric]
      exact h.trace_one i
    · intro i
      rw [← sourceProduct_map P e he hp A hproduct, h.idempotent]
    · intro i j hij
      rw [← sourceProduct_map P e he hp A hproduct, h.orthogonal i j hij, map_zero]
    · simpa only [← map_add, h.sum_unit, hunit]
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      rw [sourceTrace_eq P e A hunit hmetric]
      exact h.trace_one i
    · intro i
      apply A.injective
      rw [sourceProduct_map P e he hp A hproduct]
      exact h.idempotent i
    · intro i j hij
      apply A.injective
      rw [sourceProduct_map P e he hp A hproduct, map_zero]
      exact h.orthogonal i j hij
    · apply A.injective
      simpa only [map_add, hunit] using h.sum_unit

theorem sourceTriple_frames_iff (A : E ≃ₗ[ℝ] Albert) (hunit : A e = 1)
    (hmetric : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (A x) (A y)) / 3)
    (hproduct : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y)) (T : SourceTriple E) :
    (∀ a, SourceFrame P e he hp (T a)) ↔
      (∀ a, Frame (mapTriple A T a)) := by
  constructor
  · intro h a
    exact (sourceFrame_iff P e he hp A hunit hmetric hproduct (T a)).mp (h a)
  · intro h a
    exact (sourceFrame_iff P e he hp A hunit hmetric hproduct (T a)).mpr (h a)

/-- The fixed frame encoder uses slot 2 minus slot 0. -/
def sourceEncoder (p : Fin 3 → E) : E := p 2 - p 0

theorem sourceEncoder_map (A : E ≃ₗ[ℝ] Albert) (p : Fin 3 → E) :
    A (sourceEncoder p) = encoder (fun i => A (p i)) := by
  simp only [sourceEncoder, encoder, map_sub]

/-- The pairing of the recovered algebra. -/
def sourceInner (x y : E) : ℝ :=
  sourceTrace P e (sourceProduct P e he hp x y)

theorem sourceInner_eq (A : E ≃ₗ[ℝ] Albert) (hunit : A e = 1)
    (hmetric : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (A x) (A y)) / 3)
    (hproduct : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y)) (x y : E) :
    sourceInner P e he hp x y = inner (A x) (A y) := by
  rw [sourceInner, sourceTrace_eq P e A hunit hmetric,
    sourceProduct_map P e he hp A hproduct]
  rfl

/-- The quadratic representation in the recovered algebra. -/
def sourceU (x z : E) : E :=
  (2 : ℝ) • sourceProduct P e he hp x (sourceProduct P e he hp x z) -
    sourceProduct P e he hp (sourceProduct P e he hp x x) z

theorem sourceU_map (A : E ≃ₗ[ℝ] Albert)
    (hproduct : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y)) (x z : E) :
    A (sourceU P e he hp x z) = U (A x) (A z) := by
  simp only [sourceU, U, map_sub, map_smul,
    sourceProduct_map P e he hp A hproduct]

/-- The signed degree-nine scalar formed entirely from the recovered product and pairing. -/
def sourcePhi (x y z : E) : ℝ :=
  sourceInner P e he hp
    (sourceU P e he hp x (sourceU P e he hp y z) -
      sourceU P e he hp y (sourceU P e he hp x z))
    (sourceU P e he hp z (sourceProduct P e he hp x y))

theorem sourcePhi_eq (A : E ≃ₗ[ℝ] Albert) (hunit : A e = 1)
    (hmetric : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (A x) (A y)) / 3)
    (hproduct : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y)) (x y z : E) :
    sourcePhi P e he hp x y z = phi (A x) (A y) (A z) := by
  simp only [sourcePhi, sourceInner_eq P e he hp A hunit hmetric hproduct,
    map_sub, sourceU_map P e he hp A hproduct,
    sourceProduct_map P e he hp A hproduct, phi]

/-- The complete ordered overlap ledger formed from the recovered algebra. -/
def sourceLedger54 (T : SourceTriple E) : Glennie.Compact.Affine20.Ledger54 :=
  (fun i j k => sourceTrace P e
      (sourceProduct P e he hp
        (sourceProduct P e he hp (T 0 i) (T 1 j)) (T 2 k)),
    fun i j => sourceInner P e he hp (T 0 i) (T 1 j),
    fun j k => sourceInner P e he hp (T 1 j) (T 2 k),
    fun k i => sourceInner P e he hp (T 2 k) (T 0 i))

theorem sourceLedger54_eq (A : E ≃ₗ[ℝ] Albert) (hunit : A e = 1)
    (hmetric : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (A x) (A y)) / 3)
    (hproduct : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y)) (T : SourceTriple E) :
    sourceLedger54 P e he hp T = Glennie.Compact.Affine20.ledger54 (mapTriple A T) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext i j k
    change sourceTrace P e
      (sourceProduct P e he hp
        (sourceProduct P e he hp (T 0 i) (T 1 j)) (T 2 k)) =
      trace (jordan (jordan (A (T 0 i)) (A (T 1 j))) (A (T 2 k)))
    rw [sourceTrace_eq P e A hunit hmetric,
      sourceProduct_map P e he hp A hproduct,
      sourceProduct_map P e he hp A hproduct]
  · funext i j
    exact sourceInner_eq P e he hp A hunit hmetric hproduct (T 0 i) (T 1 j)
  · funext j k
    exact sourceInner_eq P e he hp A hunit hmetric hproduct (T 1 j) (T 2 k)
  · funext k i
    exact sourceInner_eq P e he hp A hunit hmetric hproduct (T 2 k) (T 0 i)

/-- The two fixed encoder powers used by the 26-value script. -/
def sourceFramePower (p : Fin 3 → E) (s : Fin 2) : E :=
  if s = 0 then sourceEncoder p
  else sourceProduct P e he hp (sourceEncoder p) (sourceEncoder p)

theorem sourceFramePower_map (A : E ≃ₗ[ℝ] Albert)
    (hproduct : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y)) (p : Fin 3 → E) (s : Fin 2) :
    A (sourceFramePower P e he hp p s) =
      Glennie.Compact.NativeQFamilyLedger.framePower (fun i => A (p i)) s := by
  by_cases hs : s = 0
  · simp only [sourceFramePower, Glennie.Compact.NativeQFamilyLedger.framePower,
      hs, ↓reduceIte, sourceEncoder_map]
  · simp only [sourceFramePower, Glennie.Compact.NativeQFamilyLedger.framePower,
      hs, ↓reduceIte, sourceProduct_map P e he hp A hproduct, sourceEncoder_map]

def sourceQSingle (T : SourceTriple E) (v : Fin 3) (s : Fin 2) : ℝ :=
  sourceInner P e he hp (sourceFramePower P e he hp (T v) 0)
    (sourceFramePower P e he hp (T v) s)

def sourceQPair (T : SourceTriple E) (v w : Fin 3) (s t : Fin 2) : ℝ :=
  sourceInner P e he hp (sourceFramePower P e he hp (T v) s)
    (sourceFramePower P e he hp (T w) t)

def sourceQTriple (T : SourceTriple E) (s t u : Fin 2) : ℝ :=
  sourceTrace P e
    (sourceProduct P e he hp
      (sourceProduct P e he hp
        (sourceFramePower P e he hp (T 0) s)
        (sourceFramePower P e he hp (T 1) t))
      (sourceFramePower P e he hp (T 2) u))

/-- The explicit order of the native 26 scalar expressions, in source operations. -/
def sourceQ26 (T : SourceTriple E) : Fin 26 → ℝ := ![
  sourceQSingle P e he hp T 0 0, sourceQSingle P e he hp T 0 1,
  sourceQSingle P e he hp T 1 0, sourceQSingle P e he hp T 1 1,
  sourceQSingle P e he hp T 2 0, sourceQSingle P e he hp T 2 1,
  sourceQPair P e he hp T 0 1 0 0, sourceQPair P e he hp T 0 1 0 1,
  sourceQPair P e he hp T 0 1 1 0, sourceQPair P e he hp T 0 1 1 1,
  sourceQPair P e he hp T 1 2 0 0, sourceQPair P e he hp T 1 2 0 1,
  sourceQPair P e he hp T 1 2 1 0, sourceQPair P e he hp T 1 2 1 1,
  sourceQPair P e he hp T 2 0 0 0, sourceQPair P e he hp T 2 0 0 1,
  sourceQPair P e he hp T 2 0 1 0, sourceQPair P e he hp T 2 0 1 1,
  sourceQTriple P e he hp T 0 0 0, sourceQTriple P e he hp T 0 0 1,
  sourceQTriple P e he hp T 0 1 0, sourceQTriple P e he hp T 0 1 1,
  sourceQTriple P e he hp T 1 0 0, sourceQTriple P e he hp T 1 0 1,
  sourceQTriple P e he hp T 1 1 0, sourceQTriple P e he hp T 1 1 1]

theorem sourceQSingle_eq (A : E ≃ₗ[ℝ] Albert) (hunit : A e = 1)
    (hmetric : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (A x) (A y)) / 3)
    (hproduct : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y)) (T : SourceTriple E) (v : Fin 3) (s : Fin 2) :
    sourceQSingle P e he hp T v s =
      Glennie.Compact.NativeQFamilyLedger.qSingle (mapTriple A T) v s := by
  rw [sourceQSingle, sourceInner_eq P e he hp A hunit hmetric hproduct,
    sourceFramePower_map P e he hp A hproduct,
    sourceFramePower_map P e he hp A hproduct]
  rfl

theorem sourceQPair_eq (A : E ≃ₗ[ℝ] Albert) (hunit : A e = 1)
    (hmetric : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (A x) (A y)) / 3)
    (hproduct : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y)) (T : SourceTriple E)
    (v w : Fin 3) (s t : Fin 2) :
    sourceQPair P e he hp T v w s t =
      Glennie.Compact.NativeQFamilyLedger.qPair (mapTriple A T) v w s t := by
  rw [sourceQPair, sourceInner_eq P e he hp A hunit hmetric hproduct,
    sourceFramePower_map P e he hp A hproduct,
    sourceFramePower_map P e he hp A hproduct]
  rfl

theorem sourceQTriple_eq (A : E ≃ₗ[ℝ] Albert) (hunit : A e = 1)
    (hmetric : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (A x) (A y)) / 3)
    (hproduct : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y)) (T : SourceTriple E)
    (s t u : Fin 2) :
    sourceQTriple P e he hp T s t u =
      Glennie.Compact.NativeQFamilyLedger.qTriple (mapTriple A T) s t u := by
  rw [sourceQTriple, sourceTrace_eq P e A hunit hmetric,
    sourceProduct_map P e he hp A hproduct,
    sourceProduct_map P e he hp A hproduct,
    sourceFramePower_map P e he hp A hproduct,
    sourceFramePower_map P e he hp A hproduct,
    sourceFramePower_map P e he hp A hproduct]
  rfl

theorem sourceQ26_eq (A : E ≃ₗ[ℝ] Albert) (hunit : A e = 1)
    (hmetric : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (A x) (A y)) / 3)
    (hproduct : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y)) (T : SourceTriple E) :
    sourceQ26 P e he hp T = Glennie.Compact.NativeQFamilyLedger.q26 (mapTriple A T) := by
  funext i
  fin_cases i <;>
    simp only [sourceQ26, Glennie.Compact.NativeQFamilyLedger.q26,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      sourceQSingle_eq P e he hp A hunit hmetric hproduct,
      sourceQPair_eq P e he hp A hunit hmetric hproduct,
      sourceQTriple_eq P e he hp A hunit hmetric hproduct]

/-- Q26 and the full ledger have identical equality data on actual source frames. -/
theorem sourceQ26_eq_iff_ledger54_eq (A : E ≃ₗ[ℝ] Albert) (hunit : A e = 1)
    (hmetric : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (A x) (A y)) / 3)
    (hproduct : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y)) (T S : SourceTriple E)
    (hT : ∀ a, SourceFrame P e he hp (T a))
    (hS : ∀ a, SourceFrame P e he hp (S a)) :
    sourceQ26 P e he hp T = sourceQ26 P e he hp S ↔
      sourceLedger54 P e he hp T = sourceLedger54 P e he hp S := by
  rw [sourceQ26_eq P e he hp A hunit hmetric hproduct,
    sourceQ26_eq P e he hp A hunit hmetric hproduct,
    sourceLedger54_eq P e he hp A hunit hmetric hproduct,
    sourceLedger54_eq P e he hp A hunit hmetric hproduct]
  exact Glennie.Compact.NativeQFamilyLedger.q26_eq_iff_ledger54_eq
    (mapTriple A T) (mapTriple A S)
    ((sourceTriple_frames_iff P e he hp A hunit hmetric hproduct T).mp hT)
    ((sourceTriple_frames_iff P e he hp A hunit hmetric hproduct S).mp hS)

/-- The unnormalized half amplitude in the recovered algebra. -/
def sourceHalfAmplitude (x : E) : E := (1 / 2 : ℝ) • (e + x)

theorem sourceHalfAmplitude_map (A : E ≃ₗ[ℝ] Albert) (hunit : A e = 1)
    (x : E) :
    A (sourceHalfAmplitude e x) = Glennie.Compact.OperationalPhi.halfAmplitude (A x) := by
  simp only [sourceHalfAmplitude, Glennie.Compact.OperationalPhi.halfAmplitude,
    map_smul, map_add, hunit]

def sourceContrast (x y z v : E) : ℝ :=
  sourceInner P e he hp z
    (sourceU P e he hp y (sourceU P e he hp x (sourceU P e he hp z v)) -
      sourceU P e he hp x (sourceU P e he hp y (sourceU P e he hp z v)))

theorem sourceContrast_eq (A : E ≃ₗ[ℝ] Albert) (hunit : A e = 1)
    (hmetric : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (A x) (A y)) / 3)
    (hproduct : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y)) (x y z v : E) :
    sourceContrast P e he hp x y z v =
      Glennie.Compact.OperationalPhi.contrast (A x) (A y) (A z) (A v) := by
  simp only [sourceContrast, sourceInner_eq P e he hp A hunit hmetric hproduct,
    map_sub, sourceU_map P e he hp A hproduct,
    Glennie.Compact.OperationalPhi.contrast]

def sourceDelta (x y z a rho : E) : ℝ :=
  sourceContrast P e he hp x y z (sourceU P e he hp a rho)

theorem sourceDelta_eq (A : E ≃ₗ[ℝ] Albert) (hunit : A e = 1)
    (hmetric : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (A x) (A y)) / 3)
    (hproduct : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y)) (x y z a rho : E) :
    sourceDelta P e he hp x y z a rho =
      Glennie.Compact.OperationalPhi.delta (A x) (A y) (A z) (A a) (A rho) := by
  rw [sourceDelta, sourceContrast_eq P e he hp A hunit hmetric hproduct,
    sourceU_map P e he hp A hproduct]
  rfl

/-- The three fixed-orientation algebraic contrasts on the trace-zero encoders. -/
def sourceScore (T : SourceTriple E) : ℝ :=
  let x := sourceEncoder (T 0)
  let y := sourceEncoder (T 1)
  let z := sourceEncoder (T 2)
  4 * sourceDelta P e he hp x y z (sourceHalfAmplitude e x) y -
    sourceDelta P e he hp x y z x y - sourceDelta P e he hp x y z e y

theorem sourceScore_eq (A : E ≃ₗ[ℝ] Albert) (hunit : A e = 1)
    (hmetric : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (A x) (A y)) / 3)
    (hproduct : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y)) (T : SourceTriple E) :
    sourceScore P e he hp T =
      Glennie.Compact.LocalContrast.score (mapTriple A T) := by
  simp only [sourceScore, Glennie.Compact.LocalContrast.score,
    sourceDelta_eq P e he hp A hunit hmetric hproduct,
    sourceHalfAmplitude_map e A hunit, sourceEncoder_map, hunit]
  rfl

theorem sourceScore_eq_twoPhi (A : E ≃ₗ[ℝ] Albert) (hunit : A e = 1)
    (hmetric : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (A x) (A y)) / 3)
    (hproduct : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y)) (T : SourceTriple E) :
    sourceScore P e he hp T =
      2 * sourcePhi P e he hp (sourceEncoder (T 0))
        (sourceEncoder (T 1)) (sourceEncoder (T 2)) := by
  rw [sourceScore_eq P e he hp A hunit hmetric hproduct,
    Glennie.Compact.LocalContrast.score_eq_two_phi,
    sourcePhi_eq P e he hp A hunit hmetric hproduct]
  simp only [Glennie.Compact.Sections.phiOf, sourceEncoder_map]
  rfl

/-- Any two recognizing maps differ by a native product-and-trace automorphism. -/
def nativeTransition (A B : E ≃ₗ[ℝ] Albert)
    (hAu : A e = 1) (hBu : B e = 1)
    (hAm : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (A x) (A y)) / 3)
    (hBm : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (B x) (B y)) / 3)
    (hAp : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y))
    (hBp : ∀ x y : E,
      B (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (B x) (B y)) : CompactAutomorphism where
  equiv := A.symm.trans B
  map_jordan := by
    intro x y
    have hpre : A.symm (jordan x y) =
        sourceProduct P e he hp (A.symm x) (A.symm y) := by
      apply A.injective
      simp only [A.apply_symm_apply, sourceProduct_map P e he hp A hAp]
    change B (A.symm (jordan x y)) =
      jordan (B (A.symm x)) (B (A.symm y))
    rw [hpre, sourceProduct_map P e he hp B hBp]
  map_trace := by
    intro x
    change trace (B (A.symm x)) = trace x
    calc
      trace (B (A.symm x)) = sourceTrace P e (A.symm x) :=
        (sourceTrace_eq P e B hBu hBm _).symm
      _ = trace x := by rw [sourceTrace_eq P e A hAu hAm, A.apply_symm_apply]

theorem mapTriple_transition (A B : E ≃ₗ[ℝ] Albert)
    (hAu : A e = 1) (hBu : B e = 1)
    (hAm : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (A x) (A y)) / 3)
    (hBm : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (B x) (B y)) / 3)
    (hAp : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y))
    (hBp : ∀ x y : E,
      B (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (B x) (B y)) (T : SourceTriple E) :
    mapTriple B T = Glennie.Compact.Affine20.mapAtoms
      (nativeTransition P e he hp A B hAu hBu hAm hBm hAp hBp) (mapTriple A T) := by
  funext a i
  change B (T a i) = B (A.symm (A (T a i)))
  rw [A.symm_apply_apply]

/-- The complete source product-and-trace automorphism group. -/
structure SourceAutomorphism where
  equiv : E ≃ₗ[ℝ] E
  map_product : ∀ x y,
    equiv (sourceProduct P e he hp x y) =
      sourceProduct P e he hp (equiv x) (equiv y)
  map_trace : ∀ x, sourceTrace P e (equiv x) = sourceTrace P e x

def sourceMapAtoms (g : SourceAutomorphism P e he hp)
    (T : SourceTriple E) : SourceTriple E := fun a i => g.equiv (T a i)

def sourceAutOrbit (T : SourceTriple E) : Set (SourceTriple E) :=
  {S | ∃ g : SourceAutomorphism P e he hp, sourceMapAtoms P e he hp g T = S}

def sourceAutToNative (A : E ≃ₗ[ℝ] Albert) (hunit : A e = 1)
    (hmetric : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (A x) (A y)) / 3)
    (hproduct : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y))
    (g : SourceAutomorphism P e he hp) : CompactAutomorphism where
  equiv := (A.symm.trans g.equiv).trans A
  map_jordan := by
    intro x y
    have hpre : A.symm (jordan x y) =
        sourceProduct P e he hp (A.symm x) (A.symm y) := by
      apply A.injective
      simp only [A.apply_symm_apply, sourceProduct_map P e he hp A hproduct]
    change A (g.equiv (A.symm (jordan x y))) =
      jordan (A (g.equiv (A.symm x))) (A (g.equiv (A.symm y)))
    rw [hpre, g.map_product, sourceProduct_map P e he hp A hproduct]
  map_trace := by
    intro x
    change trace (A (g.equiv (A.symm x))) = trace x
    calc
      trace (A (g.equiv (A.symm x))) = sourceTrace P e (g.equiv (A.symm x)) :=
        (sourceTrace_eq P e A hunit hmetric _).symm
      _ = sourceTrace P e (A.symm x) := g.map_trace _
      _ = trace x := by rw [sourceTrace_eq P e A hunit hmetric, A.apply_symm_apply]

def nativeAutToSource (A : E ≃ₗ[ℝ] Albert) (hunit : A e = 1)
    (hmetric : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (A x) (A y)) / 3)
    (hproduct : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y))
    (k : CompactAutomorphism) : SourceAutomorphism P e he hp where
  equiv := (A.trans k.equiv).trans A.symm
  map_product := by
    intro x y
    apply A.injective
    simp only [LinearEquiv.trans_apply, A.apply_symm_apply]
    rw [sourceProduct_map P e he hp A hproduct, k.map_jordan,
      sourceProduct_map P e he hp A hproduct,
      A.apply_symm_apply, A.apply_symm_apply]
  map_trace := by
    intro x
    rw [sourceTrace_eq P e A hunit hmetric,
      sourceTrace_eq P e A hunit hmetric]
    simp only [LinearEquiv.trans_apply, A.apply_symm_apply]
    exact k.map_trace _

theorem sourceOrbit_iff_native (A : E ≃ₗ[ℝ] Albert) (hunit : A e = 1)
    (hmetric : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (A x) (A y)) / 3)
    (hproduct : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y)) (T S : SourceTriple E) :
    S ∈ sourceAutOrbit P e he hp T ↔
      mapTriple A S ∈ Glennie.Compact.FlatOrbit.autOrbit (mapTriple A T) := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨sourceAutToNative P e he hp A hunit hmetric hproduct g, ?_⟩
    funext a i
    simp only [Glennie.Compact.Affine20.mapAtoms_apply, mapTriple,
      sourceAutToNative, LinearEquiv.trans_apply, A.symm_apply_apply]
    exact congrArg A (congrFun (congrFun hg a) i)
  · rintro ⟨k, hk⟩
    refine ⟨nativeAutToSource P e he hp A hunit hmetric hproduct k, ?_⟩
    funext a i
    apply A.injective
    simp only [sourceMapAtoms, nativeAutToSource,
      LinearEquiv.trans_apply, A.apply_symm_apply]
    exact congrFun (congrFun hk a) i

/-- The native orbit relation is independent of which geometric recognition
map is used. This compares orbits, not pointwise section representatives. -/
theorem recognition_choice_orbit_iff (A B : E ≃ₗ[ℝ] Albert)
    (hAu : A e = 1) (hBu : B e = 1)
    (hAm : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (A x) (A y)) / 3)
    (hBm : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (B x) (B y)) / 3)
    (hAp : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y))
    (hBp : ∀ x y : E,
      B (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (B x) (B y)) (T S : SourceTriple E) :
    mapTriple A S ∈ Glennie.Compact.FlatOrbit.autOrbit (mapTriple A T) ↔
      mapTriple B S ∈ Glennie.Compact.FlatOrbit.autOrbit (mapTriple B T) :=
  (sourceOrbit_iff_native P e he hp A hAu hAm hAp T S).symm.trans
    (sourceOrbit_iff_native P e he hp B hBu hBm hBp T S)

/-- Actual ordered-frame fibres in the source algebra, at the decoded chart ledger. -/
def sourceFibre54 (b : Fin 20 → ℝ) : Set (SourceTriple E) :=
  {T | (∀ a, SourceFrame P e he hp (T a)) ∧
    sourceLedger54 P e he hp T = Glennie.Compact.Affine20.decode20 b}

def sourceFibre20 (b : Fin 20 → ℝ) : Set (SourceTriple E) :=
  {T | (∀ a, SourceFrame P e he hp (T a)) ∧
    Glennie.Compact.Affine20.encode20 (sourceLedger54 P e he hp T) = b}

theorem sourceFibre54_iff_native (A : E ≃ₗ[ℝ] Albert) (hunit : A e = 1)
    (hmetric : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (A x) (A y)) / 3)
    (hproduct : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y)) (b : Fin 20 → ℝ) (T : SourceTriple E) :
    T ∈ sourceFibre54 P e he hp b ↔
      mapTriple A T ∈ Glennie.Compact.NearbyOrbits.fibre54 b := by
  change ((∀ a, SourceFrame P e he hp (T a)) ∧
    sourceLedger54 P e he hp T = Glennie.Compact.Affine20.decode20 b) ↔
    ((∀ a, Frame (mapTriple A T a)) ∧
      Glennie.Compact.Affine20.ledger54 (mapTriple A T) =
        Glennie.Compact.Affine20.decode20 b)
  rw [sourceTriple_frames_iff P e he hp A hunit hmetric hproduct,
    sourceLedger54_eq P e he hp A hunit hmetric hproduct]

theorem sourceFibre20_iff_native (A : E ≃ₗ[ℝ] Albert) (hunit : A e = 1)
    (hmetric : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (A x) (A y)) / 3)
    (hproduct : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y)) (b : Fin 20 → ℝ) (T : SourceTriple E) :
    T ∈ sourceFibre20 P e he hp b ↔
      mapTriple A T ∈ Glennie.Compact.NearbyOrbits.fibre20 b := by
  change ((∀ a, SourceFrame P e he hp (T a)) ∧
    Glennie.Compact.Affine20.encode20 (sourceLedger54 P e he hp T) = b) ↔
    ((∀ a, Frame (mapTriple A T a)) ∧
      Glennie.Compact.Affine20.encode20
        (Glennie.Compact.Affine20.ledger54 (mapTriple A T)) = b)
  rw [sourceTriple_frames_iff P e he hp A hunit hmetric hproduct,
    sourceLedger54_eq P e he hp A hunit hmetric hproduct]

theorem continuous_pullTriple (A : E ≃ₗ[ℝ] Albert) :
    Continuous (fun T : Glennie.Compact.Affine20.Triple => pullTriple A T) := by
  have hA : Continuous (fun x : Albert => A.symm x) :=
    A.symm.toLinearMap.continuous_of_finiteDimensional
  refine continuous_pi fun a => continuous_pi fun i => ?_
  simpa only [Function.comp_def, pullTriple] using
    hA.comp (Glennie.Compact.FrameTopology.continuous_entry a i)

def SameSourceScoreSign (T S : SourceTriple E) : Prop :=
  (sourceScore P e he hp T < 0 ∧ sourceScore P e he hp S < 0) ∨
    (0 < sourceScore P e he hp T ∧ 0 < sourceScore P e he hp S)

/-- Finite data and the division-free sign classify source triples locally. -/
theorem local_q26_score_complete_of_equiv (A : E ≃ₗ[ℝ] Albert)
    (hunit : A e = 1)
    (hmetric : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (A x) (A y)) / 3)
    (hproduct : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y)) :
    ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧
      Glennie.Compact.Affine20.encode20
        (sourceLedger54 P e he hp
          (pullTriple A Glennie.Compact.Sections.flatBase)) ∈ V ∧
      ∀ T S : SourceTriple E,
        (∀ a, SourceFrame P e he hp (T a)) →
        (∀ a, SourceFrame P e he hp (S a)) →
        Glennie.Compact.Affine20.encode20 (sourceLedger54 P e he hp T) ∈ V →
        sourceScore P e he hp T ≠ 0 ∧
        ((T ∈ sourceAutOrbit P e he hp S) ↔
          sourceQ26 P e he hp T = sourceQ26 P e he hp S ∧
            SameSourceScoreSign P e he hp T S) := by
  obtain ⟨V, hVopen, hbase, hclass⟩ :=
    Glennie.Compact.LocalReconstruction.nearby_q26_score_complete
  refine ⟨V, hVopen, ?_, ?_⟩
  · rw [sourceLedger54_eq P e he hp A hunit hmetric hproduct,
      mapTriple_pullTriple]
    exact hbase
  · intro T S hT hS hb
    have hTn := (sourceTriple_frames_iff P e he hp A hunit hmetric hproduct T).mp hT
    have hSn := (sourceTriple_frames_iff P e he hp A hunit hmetric hproduct S).mp hS
    have hbN : Glennie.Compact.Affine20.encode20
        (Glennie.Compact.Affine20.ledger54 (mapTriple A T)) ∈ V := by
      rwa [sourceLedger54_eq P e he hp A hunit hmetric hproduct] at hb
    obtain ⟨hnz, hiff⟩ := hclass (mapTriple A T) (mapTriple A S) hTn hSn hbN
    refine ⟨?_, ?_⟩
    · rw [sourceScore_eq P e he hp A hunit hmetric hproduct]
      exact hnz
    · rw [sourceOrbit_iff_native P e he hp A hunit hmetric hproduct,
        sourceQ26_eq P e he hp A hunit hmetric hproduct,
        sourceQ26_eq P e he hp A hunit hmetric hproduct]
      change (mapTriple A T ∈ Glennie.Compact.FlatOrbit.autOrbit (mapTriple A S)) ↔
        Glennie.Compact.NativeQFamilyLedger.q26 (mapTriple A T) =
          Glennie.Compact.NativeQFamilyLedger.q26 (mapTriple A S) ∧
          SameSourceScoreSign P e he hp T S
      rw [SameSourceScoreSign,
        sourceScore_eq P e he hp A hunit hmetric hproduct,
        sourceScore_eq P e he hp A hunit hmetric hproduct]
      exact hiff

/-- The entire nearby fibre consists of two source-automorphism orbits,
with continuous pulled-back sections and opposite nonzero algebraic scores. -/
theorem local_two_orbits_of_equiv (A : E ≃ₗ[ℝ] Albert)
    (hunit : A e = 1)
    (hmetric : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (A x) (A y)) / 3)
    (hproduct : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y)) :
    ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧
      Glennie.Compact.Affine20.encode20
        (sourceLedger54 P e he hp
          (pullTriple A Glennie.Compact.Sections.flatBase)) ∈ V ∧
      ∃ secPos secNeg : (Fin 20 → ℝ) → SourceTriple E,
        ContinuousOn secPos V ∧ ContinuousOn secNeg V ∧
        (∀ b ∈ V, ∀ a, SourceFrame P e he hp (secPos b a)) ∧
        (∀ b ∈ V, ∀ a, SourceFrame P e he hp (secNeg b a)) ∧
        (∀ b ∈ V, sourceLedger54 P e he hp (secPos b) =
          Glennie.Compact.Affine20.decode20 b) ∧
        (∀ b ∈ V, sourceLedger54 P e he hp (secNeg b) =
          Glennie.Compact.Affine20.decode20 b) ∧
        (∀ b ∈ V, 0 < sourceScore P e he hp (secPos b)) ∧
        (∀ b ∈ V, sourceScore P e he hp (secNeg b) < 0) ∧
        (∀ b ∈ V, sourceFibre54 P e he hp b =
          sourceAutOrbit P e he hp (secNeg b) ∪
            sourceAutOrbit P e he hp (secPos b)) ∧
        (∀ b ∈ V, Disjoint
          (sourceAutOrbit P e he hp (secNeg b))
          (sourceAutOrbit P e he hp (secPos b))) ∧
        (∀ b ∈ V, sourceFibre20 P e he hp b = sourceFibre54 P e he hp b) := by
  obtain ⟨V, hVopen, hbase, pos, neg, hcP, hcN, hfP, hfN,
      _heP, _heN, hlP, hlN, hpP, hpN, hcover, hdisj, h20⟩ :=
    Glennie.Compact.NearbyOrbitsClosed.nearby_fibres_two_orbits_unconditional
  let secPos : (Fin 20 → ℝ) → SourceTriple E := fun b => pullTriple A (pos b)
  let secNeg : (Fin 20 → ℝ) → SourceTriple E := fun b => pullTriple A (neg b)
  refine ⟨V, hVopen, ?_, secPos, secNeg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sourceLedger54_eq P e he hp A hunit hmetric hproduct,
      mapTriple_pullTriple]
    exact hbase
  · exact (continuous_pullTriple A).comp_continuousOn hcP
  · exact (continuous_pullTriple A).comp_continuousOn hcN
  · intro b hb a
    exact (sourceTriple_frames_iff P e he hp A hunit hmetric hproduct (secPos b)).mpr
      (by simpa only [secPos, mapTriple_pullTriple] using hfP b hb) a
  · intro b hb a
    exact (sourceTriple_frames_iff P e he hp A hunit hmetric hproduct (secNeg b)).mpr
      (by simpa only [secNeg, mapTriple_pullTriple] using hfN b hb) a
  · intro b hb
    rw [sourceLedger54_eq P e he hp A hunit hmetric hproduct,
      show mapTriple A (secPos b) = pos b from mapTriple_pullTriple A (pos b)]
    exact hlP b hb
  · intro b hb
    rw [sourceLedger54_eq P e he hp A hunit hmetric hproduct,
      show mapTriple A (secNeg b) = neg b from mapTriple_pullTriple A (neg b)]
    exact hlN b hb
  · intro b hb
    rw [sourceScore_eq P e he hp A hunit hmetric hproduct,
      show mapTriple A (secPos b) = pos b from mapTriple_pullTriple A (pos b),
      Glennie.Compact.LocalContrast.score_eq_two_phi]
    linarith [hpP b hb]
  · intro b hb
    rw [sourceScore_eq P e he hp A hunit hmetric hproduct,
      show mapTriple A (secNeg b) = neg b from mapTriple_pullTriple A (neg b),
      Glennie.Compact.LocalContrast.score_eq_two_phi]
    linarith [hpN b hb]
  · intro b hb
    apply Set.ext
    intro T
    change (T ∈ sourceFibre54 P e he hp b) ↔
      (T ∈ sourceAutOrbit P e he hp (secNeg b) ∨
        T ∈ sourceAutOrbit P e he hp (secPos b))
    rw [sourceFibre54_iff_native P e he hp A hunit hmetric hproduct,
      sourceOrbit_iff_native P e he hp A hunit hmetric hproduct,
      sourceOrbit_iff_native P e he hp A hunit hmetric hproduct,
      show mapTriple A (secNeg b) = neg b from mapTriple_pullTriple A (neg b),
      show mapTriple A (secPos b) = pos b from mapTriple_pullTriple A (pos b),
      hcover b hb]
    rfl
  · intro b hb
    rw [Set.disjoint_left]
    intro T hN hP
    have hN' := (sourceOrbit_iff_native P e he hp A hunit hmetric hproduct
      (secNeg b) T).mp hN
    have hP' := (sourceOrbit_iff_native P e he hp A hunit hmetric hproduct
      (secPos b) T).mp hP
    rw [show mapTriple A (secNeg b) = neg b from mapTriple_pullTriple A (neg b)] at hN'
    rw [show mapTriple A (secPos b) = pos b from mapTriple_pullTriple A (pos b)] at hP'
    exact Set.disjoint_left.mp (hdisj b hb) hN' hP'
  · intro b hb
    apply Set.ext
    intro T
    rw [sourceFibre20_iff_native P e he hp A hunit hmetric hproduct,
      sourceFibre54_iff_native P e he hp A hunit hmetric hproduct,
      h20 b hb]

/-- Exact source-side local fibre and section conclusion. -/
def TwoOrbitSections (V : Set (Fin 20 → ℝ)) : Prop :=
  ∃ secPos secNeg : (Fin 20 → ℝ) → SourceTriple E,
    ContinuousOn secPos V ∧ ContinuousOn secNeg V ∧
    (∀ b ∈ V, ∀ a, SourceFrame P e he hp (secPos b a)) ∧
    (∀ b ∈ V, ∀ a, SourceFrame P e he hp (secNeg b a)) ∧
    (∀ b ∈ V, sourceLedger54 P e he hp (secPos b) =
      Glennie.Compact.Affine20.decode20 b) ∧
    (∀ b ∈ V, sourceLedger54 P e he hp (secNeg b) =
      Glennie.Compact.Affine20.decode20 b) ∧
    (∀ b ∈ V, 0 < sourceScore P e he hp (secPos b)) ∧
    (∀ b ∈ V, sourceScore P e he hp (secNeg b) < 0) ∧
    (∀ b ∈ V, sourceFibre54 P e he hp b =
      sourceAutOrbit P e he hp (secNeg b) ∪
        sourceAutOrbit P e he hp (secPos b)) ∧
    (∀ b ∈ V, Disjoint
      (sourceAutOrbit P e he hp (secNeg b))
      (sourceAutOrbit P e he hp (secPos b))) ∧
    (∀ b ∈ V, sourceFibre20 P e he hp b = sourceFibre54 P e he hp b)

/-- Exact source-side finite-observation orbit test on actual ordered frames. -/
def ScoreComplete (V : Set (Fin 20 → ℝ)) : Prop :=
  ∀ T S : SourceTriple E,
    (∀ a, SourceFrame P e he hp (T a)) →
    (∀ a, SourceFrame P e he hp (S a)) →
    Glennie.Compact.Affine20.encode20 (sourceLedger54 P e he hp T) ∈ V →
    sourceScore P e he hp T ≠ 0 ∧
    ((T ∈ sourceAutOrbit P e he hp S) ↔
      sourceQ26 P e he hp T = sourceQ26 P e he hp S ∧
        SameSourceScoreSign P e he hp T S)

/-- The chart, two-section classification, and score test hold on one open domain. -/
theorem common_local_reconstruction_of_equiv (A : E ≃ₗ[ℝ] Albert)
    (hunit : A e = 1)
    (hmetric : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (A x) (A y)) / 3)
    (hproduct : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y)) :
    ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧
      Glennie.Compact.Affine20.encode20
        (sourceLedger54 P e he hp
          (pullTriple A Glennie.Compact.Sections.flatBase)) ∈ V ∧
      TwoOrbitSections P e he hp V ∧ ScoreComplete P e he hp V := by
  obtain ⟨V1, hV1, hbase1, pos, neg,
      hcP, hcN, hfP, hfN, hlP, hlN, hpP, hpN, hcover, hdisj, h20⟩ :=
    local_two_orbits_of_equiv P e he hp A hunit hmetric hproduct
  obtain ⟨V2, hV2, hbase2, hclass⟩ :=
    local_q26_score_complete_of_equiv P e he hp A hunit hmetric hproduct
  let V := V1 ∩ V2
  refine ⟨V, hV1.inter hV2, ⟨hbase1, hbase2⟩, ?_, ?_⟩
  · exact ⟨pos, neg, hcP.mono (fun b hb => hb.1),
      hcN.mono (fun b hb => hb.1),
      (fun b hb a => hfP b hb.1 a),
      (fun b hb a => hfN b hb.1 a),
      (fun b hb => hlP b hb.1),
      (fun b hb => hlN b hb.1),
      (fun b hb => hpP b hb.1),
      (fun b hb => hpN b hb.1),
      (fun b hb => hcover b hb.1),
      (fun b hb => hdisj b hb.1),
      (fun b hb => h20 b hb.1)⟩
  · intro T S hT hS hb
    exact hclass T S hT hS hb.2

end
end AlbertGeometry.IntrinsicLocalTransport
