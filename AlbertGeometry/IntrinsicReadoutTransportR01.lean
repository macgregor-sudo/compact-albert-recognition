/- Six raw division-free readouts in the recovered algebra, transported entrywise
through an actual recognizing equivalence. -/
module
public import AlbertGeometry.IntrinsicLocalTransport
public import Glennie.Compact.ReadoutRobustnessR01

@[expose] public section
namespace AlbertGeometry.IntrinsicReadoutTransportR01
noncomputable section
open Glennie
open Glennie.Compact.ReadoutRobustnessR01
open AlbertGeometry.Cubic AlbertGeometry.BasedNormAdjointTransport
open AlbertGeometry.IntrinsicLocalTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
variable (P : SymmetricTrilinearForm E) (e : E)
  (he : diagonalCubic P.form e = 1)
  (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u)

def sourceRawPlus (x y z a : E) : ℝ :=
  sourceInner P e he hp z
    (sourceU P e he hp y
      (sourceU P e he hp x
        (sourceU P e he hp z (sourceU P e he hp a y))))

def sourceRawMinus (x y z a : E) : ℝ :=
  sourceInner P e he hp z
    (sourceU P e he hp x
      (sourceU P e he hp y
        (sourceU P e he hp z (sourceU P e he hp a y))))

theorem sourceRawPlus_eq (A : E ≃ₗ[ℝ] Albert) (hunit : A e = 1)
    (hmetric : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (A x) (A y)) / 3)
    (hproduct : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y)) (x y z a : E) :
    sourceRawPlus P e he hp x y z a = rawPlus (A x) (A y) (A z) (A a) := by
  simp only [sourceRawPlus, rawPlus,
    sourceInner_eq P e he hp A hunit hmetric hproduct,
    sourceU_map P e he hp A hproduct]

theorem sourceRawMinus_eq (A : E ≃ₗ[ℝ] Albert) (hunit : A e = 1)
    (hmetric : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (A x) (A y)) / 3)
    (hproduct : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y)) (x y z a : E) :
    sourceRawMinus P e he hp x y z a = rawMinus (A x) (A y) (A z) (A a) := by
  simp only [sourceRawMinus, rawMinus,
    sourceInner_eq P e he hp A hunit hmetric hproduct,
    sourceU_map P e he hp A hproduct]

/-- Exact six-field tuple in source operations, ordered h+, h-, x+, x-, 1+, 1-. -/
def sourceReadouts (T : SourceTriple E) : Readouts :=
  let x := sourceEncoder (T 0)
  let y := sourceEncoder (T 1)
  let z := sourceEncoder (T 2)
  ⟨sourceRawPlus P e he hp x y z (sourceHalfAmplitude e x),
   sourceRawMinus P e he hp x y z (sourceHalfAmplitude e x),
   sourceRawPlus P e he hp x y z x,
   sourceRawMinus P e he hp x y z x,
   sourceRawPlus P e he hp x y z e,
   sourceRawMinus P e he hp x y z e⟩

/-- Every raw source reading agrees with the native reading after recognition. -/
theorem sourceReadouts_eq (A : E ≃ₗ[ℝ] Albert) (hunit : A e = 1)
    (hmetric : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (A x) (A y)) / 3)
    (hproduct : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y)) (T : SourceTriple E) :
    sourceReadouts P e he hp T = exactReadouts (mapTriple A T) := by
  simp only [sourceReadouts, exactReadouts,
    sourceRawPlus_eq P e he hp A hunit hmetric hproduct,
    sourceRawMinus_eq P e he hp A hunit hmetric hproduct,
    sourceHalfAmplitude_map e A hunit, sourceEncoder_map, hunit]
  rfl

/-- The six native coefficients reproduce the intrinsic division-free score. -/
theorem sourceWeightedScore_eq (A : E ≃ₗ[ℝ] Albert) (hunit : A e = 1)
    (hmetric : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (A x) (A y)) / 3)
    (hproduct : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y)) (T : SourceTriple E) :
    weightedScore (sourceReadouts P e he hp T) = sourceScore P e he hp T := by
  rw [sourceReadouts_eq P e he hp A hunit hmetric hproduct,
    weightedScore_exact, sourceScore_eq P e he hp A hunit hmetric hproduct]

/-- The actual source scalar, evaluated on the fixed three ordered encoders. -/
def sourcePhiOf (T : SourceTriple E) : ℝ :=
  sourcePhi P e he hp (sourceEncoder (T 0))
    (sourceEncoder (T 1)) (sourceEncoder (T 2))

theorem sourcePhiOf_eq (A : E ≃ₗ[ℝ] Albert) (hunit : A e = 1)
    (hmetric : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (A x) (A y)) / 3)
    (hproduct : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y)) (T : SourceTriple E) :
    sourcePhiOf P e he hp T = Glennie.Compact.Sections.phiOf (mapTriple A T) := by
  simp only [sourcePhiOf,
    sourcePhi_eq P e he hp A hunit hmetric hproduct,
    Glennie.Compact.Sections.phiOf, sourceEncoder_map]
  rfl

/-- A posteriori source-sign certificate with no assumption on noisy-readout signs. -/
theorem source_sign_certificate (A : E ≃ₗ[ℝ] Albert) (hunit : A e = 1)
    (hmetric : ∀ x y : E,
      logHessianForm P e x y = trace (jordan (A x) (A y)) / 3)
    (hproduct : ∀ x y : E,
      A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) =
        jordan (A x) (A y)) (T : SourceTriple E)
    (noisy : Readouts) (ε : ℝ) (hε : 0 ≤ ε)
    (hErr : ErrorsAtMost noisy (sourceReadouts P e he hp T) ε)
    (hMargin : 12 * ε < |weightedScore noisy|) :
    (weightedScore noisy < 0 ∧ sourcePhiOf P e he hp T < 0) ∨
    (0 < weightedScore noisy ∧ 0 < sourcePhiOf P e he hp T) := by
  have hNative : ErrorsAtMost noisy (exactReadouts (mapTriple A T)) ε := by
    rwa [sourceReadouts_eq P e he hp A hunit hmetric hproduct] at hErr
  have hs := sign_certificate (mapTriple A T) noisy ε hε hNative hMargin
  rw [sourcePhiOf_eq P e he hp A hunit hmetric hproduct]
  exact hs

end
end AlbertGeometry.IntrinsicReadoutTransportR01
