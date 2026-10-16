/- Explicit real coordinate dictionary between the 27-coordinate model and the native
compact Albert carrier of `Glennie.Native`, in the Sector gauge (hidden columns
-o12, +o02, -o01; last imaginary octonion coordinate with sign i(j l) = -k l).

Full index 0 is the unit. Full index n+1 is traceless index n, in the order
  t s a01 b01 a02 b02 a12 b12 u00 v00 u01 v01 u02 v02 u10 v10 u11 v11 u12 v12
  u20 v20 u21 v21 u22 v22,
with H = [[t+s, a01+i b01, a02+i b02], [conj, -t+s, a12+i b12], [conj, conj, -2s]]
and the ROW-major hidden matrix M[r][c] = u_rc + i v_rc.

Raw native conventions: T(1)=3, halved Jordan product,
B(x,y) = T(x o y) = 3 g, hidden metric factor 2, no factor 4 anywhere. -/
module

public import Glennie.SectorModel

@[expose] public section

namespace Glennie.Compact.NativeDictionary

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-! ## Traceless decode -/

/-- The explicit traceless decode. It equals `sectorDecode (extH a) (extM a)`
(theorem `extDecode0_eq_sectorDecode`). -/
def extDecode0 (a : Fin 26 → ℝ) : Albert :=
  ⟨a 0 + a 1, -a 0 + a 1, -2 * a 1,
    (⟨a 2, a 3, -a 12, -a 13⟩, ⟨-a 18, -a 19, -a 24, a 25⟩),
    (⟨a 4, a 5, a 10, a 11⟩, ⟨a 16, a 17, a 22, -a 23⟩),
    (⟨a 6, a 7, -a 8, -a 9⟩, ⟨-a 14, -a 15, -a 20, a 21⟩)⟩

@[simp] theorem extDecode0_d0 (a : Fin 26 → ℝ) : (extDecode0 a).d0 = a 0 + a 1 := rfl
@[simp] theorem extDecode0_d1 (a : Fin 26 → ℝ) : (extDecode0 a).d1 = -a 0 + a 1 := rfl
@[simp] theorem extDecode0_d2 (a : Fin 26 → ℝ) : (extDecode0 a).d2 = -2 * a 1 := rfl
@[simp] theorem extDecode0_o01 (a : Fin 26 → ℝ) :
    (extDecode0 a).o01 =
      ((⟨a 2, a 3, -a 12, -a 13⟩, ⟨-a 18, -a 19, -a 24, a 25⟩) : Octonion) := rfl
@[simp] theorem extDecode0_o02 (a : Fin 26 → ℝ) :
    (extDecode0 a).o02 =
      ((⟨a 4, a 5, a 10, a 11⟩, ⟨a 16, a 17, a 22, -a 23⟩) : Octonion) := rfl
@[simp] theorem extDecode0_o12 (a : Fin 26 → ℝ) :
    (extDecode0 a).o12 =
      ((⟨a 6, a 7, -a 8, -a 9⟩, ⟨-a 14, -a 15, -a 20, a 21⟩) : Octonion) := rfl

/-! ## Full 27-coordinate decode and encode -/

/-- Drop the unit coordinate: full index `i.succ` is traceless index `i`. -/
def extTail (a : Fin 27 → ℝ) : Fin 26 → ℝ := fun i => a i.succ

@[simp] theorem extTail_apply (a : Fin 27 → ℝ) (i : Fin 26) : extTail a i = a i.succ := rfl

/-- Full decode: coordinate 0 multiplies the native unit (raw trace 3). -/
def extDecode (a : Fin 27 → ℝ) : Albert := a 0 • (1 : Albert) + extDecode0 (extTail a)

/-- Traceless encode, the inverse of `extDecode0` on the traceless part. -/
def extEncode0 (x : Albert) : Fin 26 → ℝ :=
  ![(x.d0 - x.d1) / 2, (x.d0 + x.d1 - 2 * x.d2) / 6,
    x.o01.1.re, x.o01.1.imI, x.o02.1.re, x.o02.1.imI, x.o12.1.re, x.o12.1.imI,
    -x.o12.1.imJ, -x.o12.1.imK, x.o02.1.imJ, x.o02.1.imK,
    -x.o01.1.imJ, -x.o01.1.imK, -x.o12.2.re, -x.o12.2.imI,
    x.o02.2.re, x.o02.2.imI, -x.o01.2.re, -x.o01.2.imI,
    -x.o12.2.imJ, x.o12.2.imK, x.o02.2.imJ, -x.o02.2.imK,
    -x.o01.2.imJ, x.o01.2.imK]

/-- Full encode: unit coordinate T(x)/3, then the traceless coordinates. -/
def extEncode (x : Albert) : Fin 27 → ℝ := Matrix.vecCons (trace x / 3) (extEncode0 x)

theorem trace_extDecode0 (a : Fin 26 → ℝ) : trace (extDecode0 a) = 0 := by
  simp only [trace, extDecode0_d0, extDecode0_d1, extDecode0_d2]
  ring

theorem trace_extDecode (a : Fin 27 → ℝ) : trace (extDecode a) = 3 * a 0 := by
  simp only [extDecode, trace_add, trace_smul, trace_unit, trace_extDecode0]
  ring

theorem extDecode0_add (a b : Fin 26 → ℝ) :
    extDecode0 (a + b) = extDecode0 a + extDecode0 b := by
  ext <;> simp <;> ring

theorem extDecode0_smul (r : ℝ) (a : Fin 26 → ℝ) :
    extDecode0 (r • a) = r • extDecode0 a := by
  ext <;> simp <;> ring

/-- The traceless decode as a real-linear map. -/
def extDecode0L : (Fin 26 → ℝ) →ₗ[ℝ] Albert where
  toFun := extDecode0
  map_add' := extDecode0_add
  map_smul' r a := by
    try rw [RingHom.id_apply]
    exact extDecode0_smul r a

@[simp] theorem extDecode0L_apply (a : Fin 26 → ℝ) : extDecode0L a = extDecode0 a := rfl

theorem extDecode_add (a b : Fin 27 → ℝ) :
    extDecode (a + b) = extDecode a + extDecode b := by
  ext <;> simp [extDecode] <;> ring

theorem extDecode_smul (r : ℝ) (a : Fin 27 → ℝ) :
    extDecode (r • a) = r • extDecode a := by
  ext <;> simp [extDecode] <;> ring

theorem extEncode0_extDecode0 (c : Fin 26 → ℝ) : extEncode0 (extDecode0 c) = c := by
  funext i
  fin_cases i <;> simp [extEncode0] <;> ring

theorem extEncode0_extDecode (a : Fin 27 → ℝ) : extEncode0 (extDecode a) = extTail a := by
  funext i
  fin_cases i <;> simp [extEncode0, extDecode] <;> ring

theorem extEncode_extDecode (a : Fin 27 → ℝ) : extEncode (extDecode a) = a := by
  funext m
  induction m using Fin.cases with
  | zero =>
    simp only [extEncode, Matrix.cons_val_zero, trace_extDecode]
    ring
  | succ k =>
    simp only [extEncode, Matrix.cons_val_succ, extEncode0_extDecode, extTail_apply]

theorem extDecode_extEncode (x : Albert) : extDecode (extEncode x) = x := by
  ext <;> simp [extDecode, extEncode, extEncode0, trace] <;> ring

/-- The coordinate equivalence, decode direction. -/
def extEquiv : (Fin 27 → ℝ) ≃ₗ[ℝ] Albert where
  toFun := extDecode
  invFun := extEncode
  map_add' := extDecode_add
  map_smul' r a := by
    try rw [RingHom.id_apply]
    exact extDecode_smul r a
  left_inv := extEncode_extDecode
  right_inv := extDecode_extEncode

theorem extEquiv_apply (a : Fin 27 → ℝ) : extEquiv a = extDecode a := rfl

theorem extEquiv_symm_apply (x : Albert) : extEquiv.symm x = extEncode x := by
  apply extEquiv.injective
  rw [LinearEquiv.apply_symm_apply, extEquiv_apply, extDecode_extEncode]

/-! ## Metric: native B = 3 g -/

/-- The metric g on traceless coordinates: 2/3 everywhere except 2 on s. -/
def extMetric (a b : Fin 26 → ℝ) : ℝ :=
  2 / 3 * (a 0 * b 0) + 2 * (a 1 * b 1) +
    2 / 3 * (a 2 * b 2 + a 3 * b 3 + a 4 * b 4 + a 5 * b 5 + a 6 * b 6 + a 7 * b 7 +
      a 8 * b 8 + a 9 * b 9 + a 10 * b 10 + a 11 * b 11 + a 12 * b 12 + a 13 * b 13 +
      a 14 * b 14 + a 15 * b 15 + a 16 * b 16 + a 17 * b 17 + a 18 * b 18 +
      a 19 * b 19 + a 20 * b 20 + a 21 * b 21 + a 22 * b 22 + a 23 * b 23 +
      a 24 * b 24 + a 25 * b 25)

theorem inner_extDecode0_left (c : Fin 26 → ℝ) (w : Albert) :
    inner (extDecode0 c) w = 3 * extMetric c (extEncode0 w) := by
  rw [inner_coordinates]
  simp [extMetric, extEncode0, octDot_coordinates] <;> ring

theorem inner_extDecode0 (c d : Fin 26 → ℝ) :
    inner (extDecode0 c) (extDecode0 d) = 3 * extMetric c d := by
  rw [inner_extDecode0_left, extEncode0_extDecode0]

theorem inner_one_extDecode0 (c : Fin 26 → ℝ) : inner (1 : Albert) (extDecode0 c) = 0 := by
  rw [inner, jordan_unit_left, trace_extDecode0]

theorem inner_extDecode0_one (c : Fin 26 → ℝ) : inner (extDecode0 c) (1 : Albert) = 0 := by
  rw [inner, jordan_unit_right, trace_extDecode0]

theorem inner_one_one_eq_three : inner (1 : Albert) (1 : Albert) = 3 := by
  rw [inner, jordan_unit_left, trace_unit]

/-- Full raw metric: B(D a, D b) = 3 (a0 b0 + g(tail a, tail b)). -/
theorem inner_extDecode (a b : Fin 27 → ℝ) :
    inner (extDecode a) (extDecode b) =
      3 * (a 0 * b 0 + extMetric (extTail a) (extTail b)) := by
  simp only [extDecode, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    inner_one_one_eq_three, inner_one_extDecode0, inner_extDecode0_one, inner_extDecode0]
  ring

/-- The diagonal metric weights g_k. -/
def extG (k : Fin 26) : ℝ := if k = 1 then 2 else 2 / 3

/-- The traceless coordinate unit vector e_k. -/
def extBasis (k : Fin 26) : Fin 26 → ℝ := fun i => if i = k then 1 else 0

theorem extMetric_basis_left (k : Fin 26) (v : Fin 26 → ℝ) :
    extMetric (extBasis k) v = extG k * v k := by
  fin_cases k <;> simp [extMetric, extBasis, extG] <;> ring

theorem extG_ne_zero (k : Fin 26) : extG k ≠ 0 := by
  unfold extG
  split_ifs <;> norm_num

/-- Coordinate extraction by the native metric: B(D e_k, w) = 3 g_k (encode w)_k. -/
theorem inner_extBasis (k : Fin 26) (w : Albert) :
    inner (extDecode0 (extBasis k)) w = 3 * extG k * extEncode0 w k := by
  rw [inner_extDecode0_left, extMetric_basis_left]
  ring

/-! ## Gauge bridge to the SectorModel -/

/-- The Hermitian block H as a complex matrix. -/
def extH (a : Fin 26 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![Complex.mk (a 0 + a 1) 0, Complex.mk (a 2) (a 3), Complex.mk (a 4) (a 5);
     Complex.mk (a 2) (-a 3), Complex.mk (-a 0 + a 1) 0, Complex.mk (a 6) (a 7);
     Complex.mk (a 4) (-a 5), Complex.mk (a 6) (-a 7), Complex.mk (-2 * a 1) 0]

/-- The hidden matrix M, row-major. -/
def extM (a : Fin 26 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![Complex.mk (a 8) (a 9), Complex.mk (a 10) (a 11), Complex.mk (a 12) (a 13);
     Complex.mk (a 14) (a 15), Complex.mk (a 16) (a 17), Complex.mk (a 18) (a 19);
     Complex.mk (a 20) (a 21), Complex.mk (a 22) (a 23), Complex.mk (a 24) (a 25)]

theorem extDecode0_eq_sectorDecode (a : Fin 26 → ℝ) :
    extDecode0 a = sectorDecode (extH a) (extM a) := by
  ext <;> simp [sectorDecode, complexAlbertLinear, complexAlbert, complexOct,
    matrixComplexCoordinates, hiddenAlbert, hiddenOct, extH, extM] <;> ring

theorem extH_isHermitian (a : Fin 26 → ℝ) : (extH a).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [extH, Matrix.conjTranspose_apply] <;> ring

theorem sectorComplexMatrix_extDecode0 (a : Fin 26 → ℝ) :
    sectorComplexMatrix (extDecode0 a) = extH a := by
  rw [extDecode0_eq_sectorDecode]
  exact sectorComplexMatrix_decode (extH a) (extM a) (extH_isHermitian a)

theorem hiddenMatrix_extDecode0 (a : Fin 26 → ℝ) :
    hiddenMatrix (extDecode0 a) = extM a := by
  rw [extDecode0_eq_sectorDecode]
  exact hiddenMatrix_decode (extH a) (extM a)

end
end Glennie.Compact.NativeDictionary
