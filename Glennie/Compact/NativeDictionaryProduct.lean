/- Product transport for the explicit dictionary of `NativeDictionary`.
The external cubic is C = det H - tr(H M^dagger M) + 2 Re det M. The external product is the tensor:
polarize C, raise the index with g, unit acts as identity, scalar output
coordinate is g on traceless inputs. Statements proved here:
  * C(c) = newtonCubicNorm (extDecode0 c)              (one coordinate identity)
  * T((x o y) o z) = 3 C_polar(x, y, z) on traceless arguments
  * extEncode (x o y) = extProduct (extEncode x) (extEncode y), all 27 coordinates
  * the external commutator equals the native [L_t, L_b] with NO factor 4.
No norm or unit isometry is assumed multiplicative; the product identity is
derived from the cubic identity, the metric identity B = 3 g, commutativity and
trace associativity of the native product. -/
module

public import Glennie.Compact.NativeDictionary
public import Glennie.Theorems.CubicNorm

@[expose] public section

namespace Glennie.Compact.NativeDictionary

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-! ## The external cubic and its native identification -/

/-- The cubic C = det H - tr(H M^dagger M) + 2 Re det M, real form. -/
def extCubic (a : Fin 26 → ℝ) : ℝ :=
  (extH a).det.re - (extH a * (extM a).conjTranspose * extM a).trace.re +
    2 * (extM a).det.re

/-- The single heavy coordinate identity of the dictionary (a cubic polynomial
identity in 26 real variables). -/
theorem extCubic_eq_newtonCubicNorm (c : Fin 26 → ℝ) :
    extCubic c = newtonCubicNorm (extDecode0 c) := by
  rw [newtonCubicNorm_coordinates]
  -- Stage 1: with `extH c` and `extM c` still folded, expand both determinants and
  -- the trace of H * M^dagger * M entrywise. Folding keeps the literal-matrix simp
  -- lemmas (`Matrix.cons_mul`, `Matrix.vecMul_vecMul`) from producing `vecMul` terms.
  simp only [extCubic, Matrix.det_fin_three, Matrix.trace_fin_three, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_three]
  -- Stage 2: no matrix product remains; evaluate the literal entries and the
  -- octonion side, then close the polynomial identity.
  simp [extH, extM, Complex.mul_re, Complex.mul_im, octMul, octConj, octRe, octNormSq,
    Quaternion.normSq_def', Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

/-- For traceless x, B(x o x, x) = 3 N(x) with the raw Newton norm. -/
theorem inner_cube_of_trace_zero (x : Albert) (hx : trace x = 0) :
    inner (jordan x x) x = 3 * newtonCubicNorm x := by
  have h : inner (jordan x x) x = trace (jordan x (jordan x x)) := by
    rw [inner, jordan_comm (jordan x x) x]
  rw [h, newtonCubicNorm, hx]
  ring

/-- Polarization of the native cubic form B(x o x, x); uses only bilinearity,
commutativity and trace associativity. -/
theorem polar_native (x y z : Albert) :
    inner (jordan (x + y + z) (x + y + z)) (x + y + z) -
        inner (jordan (x + y) (x + y)) (x + y) -
        inner (jordan (x + z) (x + z)) (x + z) -
        inner (jordan (y + z) (y + z)) (y + z) +
        inner (jordan x x) x + inner (jordan y y) y + inner (jordan z z) z =
      6 * inner (jordan x y) z := by
  have s12 : ∀ u v w : Albert, inner (jordan u v) w = inner (jordan v u) w := by
    intro u v w
    rw [jordan_comm u v]
  have s23 : ∀ u v w : Albert, inner (jordan u v) w = inner (jordan v w) u := by
    intro u v w
    rw [inner_jordan_associative u v w, inner_comm]
  simp only [jordan_add_left, jordan_add_right, inner_add_left, inner_add_right]
  linarith [s12 y x z, s23 x y z, s23 y z x, s12 x z y, s12 z y x]

theorem extCubic_eq_inner (v : Fin 26 → ℝ) :
    extCubic v = inner (jordan (extDecode0 v) (extDecode0 v)) (extDecode0 v) / 3 := by
  rw [inner_cube_of_trace_zero _ (trace_extDecode0 v), extCubic_eq_newtonCubicNorm]
  ring

/-- The polarization of C (full symmetric trilinear form). -/
def extPolar (a b c : Fin 26 → ℝ) : ℝ :=
  (extCubic (a + b + c) - extCubic (a + b) - extCubic (a + c) - extCubic (b + c) +
    extCubic a + extCubic b + extCubic c) / 6

theorem extPolar_eq (a b c : Fin 26 → ℝ) :
    extPolar a b c =
      inner (jordan (extDecode0 a) (extDecode0 b)) (extDecode0 c) / 3 := by
  have hp := polar_native (extDecode0 a) (extDecode0 b) (extDecode0 c)
  simp only [extPolar, extCubic_eq_inner, extDecode0_add]
  linarith [hp]

/-- Trilinear identity: T((x o y) o z) = 3 C_polar(x, y, z) for traceless arguments. -/
theorem trace_jordan_jordan_extDecode0 (a b c : Fin 26 → ℝ) :
    trace (jordan (jordan (extDecode0 a) (extDecode0 b)) (extDecode0 c)) =
      3 * extPolar a b c := by
  rw [extPolar_eq]
  change inner (jordan (extDecode0 a) (extDecode0 b)) (extDecode0 c) =
    3 * (inner (jordan (extDecode0 a) (extDecode0 b)) (extDecode0 c) / 3)
  ring

/-! ## The external product and its transport -/

/-- The product on full coordinates: unit coordinate a0 b0 + g(a', b');
traceless coordinate k is a0 b'_k + b0 a'_k + C_polar(a', b', e_k) / g_k. -/
def extProduct (a b : Fin 27 → ℝ) : Fin 27 → ℝ :=
  Matrix.vecCons (a 0 * b 0 + extMetric (extTail a) (extTail b))
    (fun k => a 0 * b k.succ + b 0 * a k.succ +
      extPolar (extTail a) (extTail b) (extBasis k) / extG k)

/-- Product transport, all 27 output coordinates, no factor 4. -/
theorem extEncode_jordan (a b : Fin 27 → ℝ) :
    extEncode (jordan (extDecode a) (extDecode b)) = extProduct a b := by
  funext m
  induction m using Fin.cases with
  | zero =>
    have h : trace (jordan (extDecode a) (extDecode b)) =
        3 * (a 0 * b 0 + extMetric (extTail a) (extTail b)) := inner_extDecode a b
    simp only [extEncode, extProduct, Matrix.cons_val_zero]
    rw [h]
    ring
  | succ k =>
    have hg := extG_ne_zero k
    have hf := inner_extBasis k (jordan (extDecode a) (extDecode b))
    have h1 : inner (extDecode0 (extBasis k)) (1 : Albert) = 0 :=
      inner_extDecode0_one (extBasis k)
    have h2 : ∀ c : Fin 26 → ℝ,
        inner (extDecode0 (extBasis k)) (extDecode0 c) = 3 * extG k * c k := by
      intro c
      rw [inner_extBasis, extEncode0_extDecode0]
    have h3 : inner (extDecode0 (extBasis k))
        (jordan (extDecode0 (extTail a)) (extDecode0 (extTail b))) =
          3 * extPolar (extTail a) (extTail b) (extBasis k) := by
      rw [inner_comm, extPolar_eq]
      ring
    have hexp : inner (extDecode0 (extBasis k)) (jordan (extDecode a) (extDecode b)) =
        3 * extG k * (a 0 * b k.succ + b 0 * a k.succ) +
          3 * extPolar (extTail a) (extTail b) (extBasis k) := by
      simp only [extDecode, jordan_add_left, jordan_add_right, jordan_smul_left,
        jordan_smul_right, jordan_unit_left, jordan_unit_right, inner_add_right,
        inner_smul_right, h1, h2, h3, extTail_apply]
      ring
    have hP : extPolar (extTail a) (extTail b) (extBasis k) / extG k =
        extEncode0 (jordan (extDecode a) (extDecode b)) k -
          (a 0 * b k.succ + b 0 * a k.succ) := by
      rw [div_eq_iff hg]
      linear_combination (hf - hexp) / 3
    simp only [extEncode, extProduct, Matrix.cons_val_succ]
    rw [hP]
    ring

theorem extDecode_extProduct (a b : Fin 27 → ℝ) :
    extDecode (extProduct a b) = jordan (extDecode a) (extDecode b) := by
  rw [← extEncode_jordan, extDecode_extEncode]

theorem extEquiv_product (a b : Fin 27 → ℝ) :
    extEquiv (extProduct a b) = jordan (extEquiv a) (extEquiv b) := by
  simp only [extEquiv_apply]
  exact extDecode_extProduct a b

theorem extEncode_jordan_eq (x y : Albert) :
    extEncode (jordan x y) = extProduct (extEncode x) (extEncode y) := by
  rw [← extEncode_jordan, extDecode_extEncode, extDecode_extEncode]

/-- The `trprod`: three times the unit coordinate of (a b) c. -/
def extTrProd (a b c : Fin 27 → ℝ) : ℝ := 3 * extProduct (extProduct a b) c 0

theorem trace_extDecode_triple (a b c : Fin 27 → ℝ) :
    trace (jordan (jordan (extDecode a) (extDecode b)) (extDecode c)) = extTrProd a b c := by
  rw [extTrProd, ← extDecode_extProduct, ← extDecode_extProduct, trace_extDecode]

/-- Every raw native ledger entry of decoded triples is the `trprod`. -/
theorem ledger_extDecode (p q r : Fin 3 → Fin 27 → ℝ) (i j k : Fin 3) :
    ledger (fun t => extDecode (p t)) (fun t => extDecode (q t))
        (fun t => extDecode (r t)) i j k =
      extTrProd (p i) (q j) (r k) :=
  trace_extDecode_triple (p i) (q j) (r k)

theorem extDecode_sub (a b : Fin 27 → ℝ) :
    extDecode (a - b) = extDecode a - extDecode b := by
  have h := map_sub extEquiv a b
  simp only [extEquiv_apply] at h
  exact h

/-- The commutator [L_t, L_b] c is the native one: no factor 4. -/
theorem extDecode_commutator (t b c : Fin 27 → ℝ) :
    extDecode (extProduct t (extProduct b c) - extProduct b (extProduct t c)) =
      jordan (extDecode t) (jordan (extDecode b) (extDecode c)) -
        jordan (extDecode b) (jordan (extDecode t) (extDecode c)) := by
  rw [extDecode_sub, extDecode_extProduct, extDecode_extProduct, extDecode_extProduct,
    extDecode_extProduct]

end
end Glennie.Compact.NativeDictionary
