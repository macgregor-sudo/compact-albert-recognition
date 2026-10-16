/-
Thin native consumer of the actual ambient connection
producer and the preserved actual intrinsic-product binding. No dictionary,
curvature recognition or product-equivalence converse is needed in this leaf.
Metric remains actual trace/3; native Albert receives no normed-space instance.
-/
module

public import AlbertGeometry.AmbientLeviCivitaProduct
public import AlbertGeometry.NativeIntrinsicProductBinding

@[expose] public section
namespace AlbertGeometry.NativeAmbientConnectionBridge
noncomputable section
open Module Glennie
open AlbertGeometry.Cubic AlbertGeometry.CubicPolynomialRepresentation
open AlbertGeometry.BasedNormDerivativeTransport
open AlbertGeometry.BasedNormDerivativeTransport.BasedNormIso
open AlbertGeometry.BasedNormAdjointTransport
open AlbertGeometry.NativeEuclideanNormBinding AlbertGeometry.NativeNormAlgebra
open AlbertGeometry.NativeCoordinateDerivatives AlbertGeometry.NativeIntrinsicProductBinding
open AlbertGeometry.AmbientLeviCivitaProduct

local notation "QN" => nativeEuclideanRepresentation
local notation "en" => nativeCoordinateUnit

/-- Existing actual native norm producer supplies normalization. -/
theorem nativeAmbientNormalization : diagonalCubic nativeEuclideanRepresentation.form en = 1 := by
  rw [diagonal_nativeEuclideanRepresentation, delta_nativeCoordinateUnit,
    nativeNewtonNorm_one]

/-- Existing actual raw derivative binding gives the GEOMETRIC factor1/3. -/
theorem nativeAmbientMetric_eq_trace_third (x y : Coordinates) :
    logHessianForm QN en x y = Glennie.trace (jordan (delta x) (delta y)) / 3 := by
  have hg := rawTraceForm_eq_three_logMetric QN en nativeAmbientNormalization x y
  rw [native_rawTraceForm] at hg
  change Glennie.trace (jordan (delta x) (delta y)) = 3 * logHessianForm QN en x y at hg
  linarith

/-- Every ambient coordinate vector, including the radial unit, is retained.
This is actual affine Levi-Civita Gamma, not the level-chart Gamma=-K. -/
theorem nativeAmbientGamma_eq_neg_jordan (x y : Coordinates) :
    delta (ambientGamma QN en x y) = -jordan (delta x) (delta y) := by
  rw [ambientGamma_at_one_eq_neg_product QN en nativeAmbientNormalization
    native_logMetric_positive, map_neg]
  change -delta (nativeIntrinsicProduct x y) = -jordan (delta x) (delta y)
  rw [delta_nativeIntrinsicProduct]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (P : SymmetricTrilinearForm E) (e : E)
  (he : diagonalCubic P.form e = 1)
  (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u)

include hp in
/-- generic product naturality plus the actual native product binding.
This consumes a supplied/constructed BasedNormIso; it does not assume existence. -/
theorem nativeRecognition_product (I : BasedNormIso P e QN en) (x y : E) :
    delta (I.equiv (intrinsicProduct P e
      (rawBilinearForm_nondegenerate P e he hp) x y)) =
      jordan (delta (I.equiv x)) (delta (I.equiv y)) := by
  have h := intrinsicProduct_pull I (rawBilinearForm_nondegenerate P e he hp)
    nativeRawBilinear_nondegenerate x y
  change I.equiv (intrinsicProduct P e
    (rawBilinearForm_nondegenerate P e he hp) x y) =
      nativeIntrinsicProduct (I.equiv x) (I.equiv y) at h
  exact (congrArg delta h).trans (delta_nativeIntrinsicProduct (I.equiv x) (I.equiv y))

include he hp in
/-- Whole norm/unit transports the ACTUAL ambient Levi-Civita coefficient to
literal native multiplication; the unknown need not satisfy any Jordan law. -/
theorem nativeRecognition_ambientGamma (I : BasedNormIso P e QN en) (x y : E) :
    delta (I.equiv (ambientGamma P e x y)) =
      -jordan (delta (I.equiv x)) (delta (I.equiv y)) := by
  rw [ambientGamma_at_one_eq_neg_product P e he hp, map_neg, map_neg,
    nativeRecognition_product P e he hp I]

include he hp in
/-- Actual connection covariance is a derived output, with native positivity
supplied by its producer rather than an added unknown-carrier premise. -/
theorem nativeRecognition_connection_pull (I : BasedNormIso P e QN en) (x y : E) :
    I.equiv (ambientGamma P e x y) = ambientGamma QN en (I.equiv x) (I.equiv y) :=
  ambientGamma_at_one_pull I he nativeAmbientNormalization hp native_logMetric_positive x y

/-- The actual entire affine connection field transports wherever the original
unknown metric is positive. Whole norm/unit is the only map data supplied. -/
theorem nativeRecognition_connection_field_pull (I : BasedNormIso P e QN en) (x : E)
    (hx : 0 < diagonalCubic P.form x)
    (hpx : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) (u v : E) :
    I.equiv (ambientGamma P x u v) =
      ambientGamma QN (I.equiv x) (I.equiv u) (I.equiv v) :=
  ambientGamma_pull I x hx hpx u v

end
end AlbertGeometry.NativeAmbientConnectionBridge
