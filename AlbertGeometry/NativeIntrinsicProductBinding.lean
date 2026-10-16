/-
Native norm/unit roundtrip. The raw pairing is the ACTUAL
DN/D2N pairing and is identified with literal native inner through the proved
coordinate derivatives. Its nondegeneracy is derived from native positive
separation and the algebraic delta equivalence. The generic toDual adjoint is
identified by its genuine derivative pairing, not by defining it to be native.
Unhalved cross and halved intrinsic product then return literal native jordan.
All normed objects live on existing Euclidean coordinates; no norm on Albert,
unknown Jordan premise, assumed adjoint identity, or recognition map is input.
-/
module

public import AlbertGeometry.NativeCoordinateDerivatives
public import AlbertGeometry.BasedNormAdjointTransport

@[expose] public section
namespace AlbertGeometry.NativeIntrinsicProductBinding
noncomputable section
open Module Glennie
open AlbertGeometry.Cubic AlbertGeometry.NativeNormAlgebra
open AlbertGeometry.CubicPolynomialRepresentation AlbertGeometry.NativeEuclideanNormBinding
open AlbertGeometry.NativeCoordinateDerivatives
open AlbertGeometry.BasedNormDerivativeTransport
open AlbertGeometry.BasedNormDerivativeTransport.BasedNormIso
open AlbertGeometry.BasedNormAdjointTransport

/-- Actual DN at the actual native unit is native trace in algebraic coordinates. -/
theorem native_normTrace (x : Coordinates) :
    normTrace nativeEuclideanRepresentation nativeCoordinateUnit x = Glennie.trace (delta x) := by
  change fderiv ℝ (diagonalCubic nativeEuclideanRepresentation.form) nativeCoordinateUnit x = _
  rw [← coordinateNewton_eq_diagonal]
  exact fderiv_coordinateNewton_at_unit x

/-- Genuine second derivative, already proved from actual scalar differentiation. -/
theorem native_cubicHessian_unit (x y : Coordinates) :
    cubicHessian nativeEuclideanRepresentation nativeCoordinateUnit x y =
      Glennie.trace (delta x) * Glennie.trace (delta y) - Glennie.inner (delta x) (delta y) := by
  rw [← coordinateNewtonHessian_eq_cubicHessian]
  exact coordinateNewtonHessian_at_unit x y

/-- Full27 ACTUAL raw derivative pairing, not an installed native inner product. -/
theorem native_rawTraceForm (x y : Coordinates) :
    rawTraceForm nativeEuclideanRepresentation nativeCoordinateUnit x y =
      Glennie.inner (delta x) (delta y) := by
  rw [rawTraceForm_apply, native_normTrace, native_normTrace, native_cubicHessian_unit]
  ring

/-- Algebraic projection of the actual raw continuous form for its genuine dual. -/
def nativeRawBilinear : LinearMap.BilinForm ℝ Coordinates :=
  rawBilinearForm nativeEuclideanRepresentation nativeCoordinateUnit

@[simp] theorem nativeRawBilinear_apply (x y : Coordinates) :
    nativeRawBilinear x y = Glennie.inner (delta x) (delta y) := native_rawTraceForm x y

theorem native_rawTraceForm_symm (x y : Coordinates) :
    rawTraceForm nativeEuclideanRepresentation nativeCoordinateUnit x y =
      rawTraceForm nativeEuclideanRepresentation nativeCoordinateUnit y x := by
  rw [native_rawTraceForm, native_rawTraceForm, inner_comm]

/-- No base positivity hypothesis is added: separation is a native theorem. -/
theorem nativeRawBilinear_nondegenerate : nativeRawBilinear.Nondegenerate := by
  constructor
  · intro x hx
    have hzero : Glennie.inner (delta x) (delta x) = 0 := by
      simpa only [nativeRawBilinear_apply] using hx x
    apply delta.injective
    simpa only [map_zero] using (inner_self_eq_zero (delta x)).mp hzero
  · intro x hx
    have hzero : Glennie.inner (delta x) (delta x) = 0 := by
      simpa only [nativeRawBilinear_apply] using hx x
    apply delta.injective
    simpa only [map_zero] using (inner_self_eq_zero (delta x)).mp hzero

/-- The actual finite-dimensional toDual equivalence, with derived certificate. -/
def nativeRawDual : Coordinates ≃ₗ[ℝ] Module.Dual ℝ Coordinates :=
  nativeRawBilinear.toDual nativeRawBilinear_nondegenerate

@[simp] theorem nativeRawDual_apply (x y : Coordinates) :
    nativeRawDual x y = Glennie.inner (delta x) (delta y) := nativeRawBilinear_apply x y

/-- Intrinsic producer supplied by actual DN and actual raw toDual inversion. -/
def nativeIntrinsicAdjoint (x : Coordinates) : Coordinates :=
  intrinsicAdjoint nativeEuclideanRepresentation nativeCoordinateUnit
    nativeRawBilinear_nondegenerate x

/-- Existence/uniqueness pairing identifies the genuine intrinsic adjoint with
literal native adjoint; the native formula is not its definition. -/
theorem nativeIntrinsicAdjoint_eq (x : Coordinates) :
    nativeIntrinsicAdjoint x = delta.symm (nativeAdjoint (delta x)) := by
  symm
  apply intrinsicAdjoint_unique nativeEuclideanRepresentation nativeCoordinateUnit
    nativeRawBilinear_nondegenerate
  intro y
  rw [native_rawTraceForm, LinearEquiv.apply_symm_apply, ← coordinateNewton_eq_diagonal]
  exact (fderiv_coordinateNewton_apply x y).symm

theorem delta_nativeIntrinsicAdjoint (x : Coordinates) :
    delta (nativeIntrinsicAdjoint x) = nativeAdjoint (delta x) := by
  rw [nativeIntrinsicAdjoint_eq, LinearEquiv.apply_symm_apply]

/-- Generic actual unhalved polarization, as an actual coordinate function. -/
def nativeIntrinsicCross (x y : Coordinates) : Coordinates :=
  intrinsicCross nativeEuclideanRepresentation nativeCoordinateUnit
    nativeRawBilinear_nondegenerate x y

theorem delta_nativeIntrinsicCross (x y : Coordinates) :
    delta (nativeIntrinsicCross x y) = nativeCross (delta x) (delta y) := by
  change delta (nativeIntrinsicAdjoint (x + y) - nativeIntrinsicAdjoint x -
    nativeIntrinsicAdjoint y) = _
  simp only [map_sub, delta_nativeIntrinsicAdjoint, map_add, nativeCross]

theorem native_intrinsicS (x y : Coordinates) :
    intrinsicS nativeEuclideanRepresentation nativeCoordinateUnit x y =
      Glennie.trace (delta x) * Glennie.trace (delta y) - Glennie.inner (delta x) (delta y) := by
  simp only [intrinsicS, native_normTrace, native_rawTraceForm]

/-- Genuine generic half-product computed from actual norm/unit derivatives. -/
def nativeIntrinsicProduct (x y : Coordinates) : Coordinates :=
  intrinsicProduct nativeEuclideanRepresentation nativeCoordinateUnit
    nativeRawBilinear_nondegenerate x y

/-- The decisive literal roundtrip, for all full27 coordinate vectors. -/
theorem delta_nativeIntrinsicProduct (x y : Coordinates) :
    delta (nativeIntrinsicProduct x y) = jordan (delta x) (delta y) := by
  calc
    delta (nativeIntrinsicProduct x y) = nativeRecoveredProduct (delta x) (delta y) := by
      change delta ((1/2 : ℝ) • (nativeIntrinsicCross x y +
        normTrace nativeEuclideanRepresentation nativeCoordinateUnit x • y +
        normTrace nativeEuclideanRepresentation nativeCoordinateUnit y • x -
        intrinsicS nativeEuclideanRepresentation nativeCoordinateUnit x y • nativeCoordinateUnit)) = _
      simp only [map_smul, map_add, map_sub, delta_nativeIntrinsicCross,
        native_normTrace, native_intrinsicS, delta_nativeCoordinateUnit, nativeRecoveredProduct]
      module
    _ = jordan (delta x) (delta y) := nativeRecoveredProduct_eq _ _

theorem nativeIntrinsicProduct_eq (x y : Coordinates) :
    nativeIntrinsicProduct x y = delta.symm (jordan (delta x) (delta y)) := by
  apply delta.injective
  rw [delta_nativeIntrinsicProduct, LinearEquiv.apply_symm_apply]

theorem nativeIntrinsicProduct_one_left (x : Coordinates) :
    nativeIntrinsicProduct nativeCoordinateUnit x = x := by
  apply delta.injective
  rw [delta_nativeIntrinsicProduct, delta_nativeCoordinateUnit, jordan_unit_left]

theorem nativeIntrinsicProduct_one_right (x : Coordinates) :
    nativeIntrinsicProduct x nativeCoordinateUnit = x := by
  apply delta.injective
  rw [delta_nativeIntrinsicProduct, delta_nativeCoordinateUnit, jordan_unit_right]

theorem nativeIntrinsicProduct_comm (x y : Coordinates) :
    nativeIntrinsicProduct x y = nativeIntrinsicProduct y x := by
  apply delta.injective
  rw [delta_nativeIntrinsicProduct, delta_nativeIntrinsicProduct, jordan_comm]

theorem nativeIntrinsicProduct_add_left (x y z : Coordinates) :
    nativeIntrinsicProduct (x + y) z = nativeIntrinsicProduct x z + nativeIntrinsicProduct y z := by
  apply delta.injective
  simp only [delta_nativeIntrinsicProduct, map_add, jordan_add_left]

theorem nativeIntrinsicProduct_add_right (x y z : Coordinates) :
    nativeIntrinsicProduct x (y + z) = nativeIntrinsicProduct x y + nativeIntrinsicProduct x z := by
  apply delta.injective
  simp only [delta_nativeIntrinsicProduct, map_add, jordan_add_right]

theorem nativeIntrinsicProduct_smul_left (t : ℝ) (x y : Coordinates) :
    nativeIntrinsicProduct (t • x) y = t • nativeIntrinsicProduct x y := by
  apply delta.injective
  simp only [delta_nativeIntrinsicProduct, map_smul, jordan_smul_left]

theorem nativeIntrinsicProduct_smul_right (t : ℝ) (x y : Coordinates) :
    nativeIntrinsicProduct x (t • y) = t • nativeIntrinsicProduct x y := by
  apply delta.injective
  simp only [delta_nativeIntrinsicProduct, map_smul, jordan_smul_right]

/-- Positive separation is proved on the actual derivative pairing. -/
theorem native_rawTraceForm_positive (x : Coordinates) (hx : x ≠ 0) :
    0 < rawTraceForm nativeEuclideanRepresentation nativeCoordinateUnit x x := by
  rw [native_rawTraceForm]
  rcases lt_or_eq_of_le (inner_self_nonneg (delta x)) with hp | hz
  · exact hp
  · exfalso
    apply hx
    apply delta.injective
    simpa only [map_zero] using (inner_self_eq_zero (delta x)).mp hz.symm

/-- Genuine base log-metric positivity follows with its mandatory factor3. -/
theorem native_logMetric_positive (x : Coordinates) (hx : x ≠ 0) :
    0 < logHessianForm nativeEuclideanRepresentation nativeCoordinateUnit x x := by
  have he : diagonalCubic nativeEuclideanRepresentation.form nativeCoordinateUnit = 1 := by
    rw [← coordinateNewton_eq_diagonal]
    exact coordinateNewton_at_unit
  have hp := native_rawTraceForm_positive x hx
  rw [rawTraceForm_eq_three_logMetric nativeEuclideanRepresentation nativeCoordinateUnit he] at hp
  linarith

end
end AlbertGeometry.NativeIntrinsicProductBinding
