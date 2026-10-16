/-
Intrinsic adjoint exists through the actual nondegenerate
DN/D2N form; its covariance and the literal half-product covariance are derived
from norm/unit alone. Nondegeneracy is proved from genuine base metric positivity.
No unknown Jordan law, native correspondence or recognition map existence is
assumed as a replacement for the endpoint. Full geometry and native binding
remain separately required. No product or adjoint preservation field is stored.
-/
module

public import AlbertGeometry.BasedNormDerivativeTransport
public import Mathlib.LinearAlgebra.BilinearForm.Properties

@[expose] public section
namespace AlbertGeometry.BasedNormAdjointTransport
noncomputable section
open AlbertGeometry.Cubic
open AlbertGeometry.BasedNormDerivativeTransport
open AlbertGeometry.BasedNormDerivativeTransport.BasedNormIso

variable {E G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

/-- Algebraic projection of the ACTUAL raw continuous bilinear form. No new
pairing is substituted for its derivative-defined values. -/
def rawBilinearForm (P : SymmetricTrilinearForm E) (e : E) :
    LinearMap.BilinForm ℝ E where
  toFun := fun x => (rawTraceForm P e x).toLinearMap
  map_add' := by
    intro x y
    ext z
    change rawTraceForm P e (x + y) z = rawTraceForm P e x z + rawTraceForm P e y z
    simp only [map_add, ContinuousLinearMap.add_apply]
  map_smul' := by
    intro t x
    ext z
    change rawTraceForm P e (t • x) z = t * rawTraceForm P e x z
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]

@[simp] theorem rawBilinearForm_apply (P : SymmetricTrilinearForm E) (e x y : E) :
    rawBilinearForm P e x y = rawTraceForm P e x y := rfl

/-- Both left and right separation follow by testing the same vector. The
normalization and positivity are the actual endpoint's base hypotheses. -/
theorem rawBilinearForm_nondegenerate (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1)
    (hpos : ∀ x : E, x ≠ 0 → 0 < logHessianForm P e x x) :
    (rawBilinearForm P e).Nondegenerate := by
  constructor
  · intro x hx
    by_contra hne
    have hp := hpos x hne
    have hz : rawTraceForm P e x x = 0 := hx x
    rw [rawTraceForm_eq_three_logMetric P e he x x] at hz
    linarith
  · intro x hx
    by_contra hne
    have hp := hpos x hne
    have hz : rawTraceForm P e x x = 0 := hx x
    rw [rawTraceForm_eq_three_logMetric P e he x x] at hz
    linarith

/-- Inverse of the actual finite-dimensional raw B dual equivalence applied to
actual DN_x. Existence is supplied by toDual, not by a chosen desired adjoint. -/
def intrinsicAdjoint (P : SymmetricTrilinearForm E) (e : E)
    (hB : (rawBilinearForm P e).Nondegenerate) (x : E) : E :=
  ((rawBilinearForm P e).toDual hB).symm
    (fderiv ℝ (diagonalCubic P.form) x).toLinearMap

theorem intrinsicAdjoint_pairing (P : SymmetricTrilinearForm E) (e : E)
    (hB : (rawBilinearForm P e).Nondegenerate) (x y : E) :
    rawTraceForm P e (intrinsicAdjoint P e hB x) y =
      fderiv ℝ (diagonalCubic P.form) x y := by
  change rawBilinearForm P e
    (((rawBilinearForm P e).toDual hB).symm
      (fderiv ℝ (diagonalCubic P.form) x).toLinearMap) y = _
  exact LinearMap.BilinForm.apply_toDual_symm_apply _ y

theorem intrinsicAdjoint_unique (P : SymmetricTrilinearForm E) (e : E)
    (hB : (rawBilinearForm P e).Nondegenerate) (x z : E)
    (hz : ∀ y : E, rawTraceForm P e z y = fderiv ℝ (diagonalCubic P.form) x y) :
    z = intrinsicAdjoint P e hB x := by
  apply ((rawBilinearForm P e).toDual hB).injective
  ext y
  change rawTraceForm P e z y = rawTraceForm P e (intrinsicAdjoint P e hB x) y
  rw [hz, intrinsicAdjoint_pairing]

/-- Unhalved polarization of the actual quadratic adjoint. -/
def intrinsicCross (P : SymmetricTrilinearForm E) (e : E)
    (hB : (rawBilinearForm P e).Nondegenerate) (x y : E) : E :=
  intrinsicAdjoint P e hB (x + y) - intrinsicAdjoint P e hB x - intrinsicAdjoint P e hB y

def intrinsicS (P : SymmetricTrilinearForm E) (e x y : E) : ℝ :=
  normTrace P e x * normTrace P e y - rawTraceForm P e x y

/-- The prescribed native HALVED reconstruction, formed intrinsically from
actual norm derivatives. Native equality and algebra laws are later theorems. -/
def intrinsicProduct (P : SymmetricTrilinearForm E) (e : E)
    (hB : (rawBilinearForm P e).Nondegenerate) (x y : E) : E :=
  (1 / 2 : ℝ) • (intrinsicCross P e hB x y + normTrace P e x • y +
    normTrace P e y • x - intrinsicS P e x y • e)

variable {P : SymmetricTrilinearForm E} {e : E}
  {Q : SymmetricTrilinearForm G} {f : G}

theorem intrinsicAdjoint_pull (I : BasedNormIso P e Q f)
    (hB : (rawBilinearForm P e).Nondegenerate)
    (hC : (rawBilinearForm Q f).Nondegenerate) (x : E) :
    I.equiv (intrinsicAdjoint P e hB x) = intrinsicAdjoint Q f hC (I.equiv x) := by
  apply intrinsicAdjoint_unique Q f hC
  intro y
  obtain ⟨v, rfl⟩ := I.equiv.surjective y
  rw [← I.rawTraceForm_pull, intrinsicAdjoint_pairing, I.fderiv_norm_pull_apply]

theorem intrinsicCross_pull (I : BasedNormIso P e Q f)
    (hB : (rawBilinearForm P e).Nondegenerate)
    (hC : (rawBilinearForm Q f).Nondegenerate) (x y : E) :
    I.equiv (intrinsicCross P e hB x y) = intrinsicCross Q f hC (I.equiv x) (I.equiv y) := by
  simp only [intrinsicCross, map_sub, map_add, intrinsicAdjoint_pull I hB hC]

theorem intrinsicS_pull (I : BasedNormIso P e Q f) (x y : E) :
    intrinsicS P e x y = intrinsicS Q f (I.equiv x) (I.equiv y) := by
  simp only [intrinsicS, I.normTrace_pull, I.rawTraceForm_pull]

/-- Product preservation is a derived theorem, not a based-map premise. -/
theorem intrinsicProduct_pull (I : BasedNormIso P e Q f)
    (hB : (rawBilinearForm P e).Nondegenerate)
    (hC : (rawBilinearForm Q f).Nondegenerate) (x y : E) :
    I.equiv (intrinsicProduct P e hB x y) =
      intrinsicProduct Q f hC (I.equiv x) (I.equiv y) := by
  simp only [intrinsicProduct, map_smul, map_add, map_sub,
    intrinsicCross_pull I hB hC, I.normTrace_pull, intrinsicS_pull I, I.map_unit]

/-- Both transported native products equal the SAME derivative-defined product.
No normality of automorphisms in the unpointed norm group is used. -/
theorem pullbackProduct_choice_independent (I J : BasedNormIso P e Q f)
    (hB : (rawBilinearForm P e).Nondegenerate)
    (hC : (rawBilinearForm Q f).Nondegenerate) (x y : E) :
    I.equiv.symm (intrinsicProduct Q f hC (I.equiv x) (I.equiv y)) =
      J.equiv.symm (intrinsicProduct Q f hC (J.equiv x) (J.equiv y)) := by
  rw [← intrinsicProduct_pull I hB hC, ← intrinsicProduct_pull J hB hC]
  simp only [ContinuousLinearEquiv.symm_apply_apply]

end
end AlbertGeometry.BasedNormAdjointTransport
