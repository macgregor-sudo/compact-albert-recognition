/- Formalization of the compact real Albert model. -/
module

public import Mathlib.Algebra.Quaternion
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section

open scoped BigOperators Quaternion

namespace Glennie

noncomputable section

instance atLeastTwoOneAddOne : Nat.AtLeastTwo (1 + 1) := ⟨Nat.le_refl 2⟩
instance neZeroTwoAddOne : NeZero (2 + 1 : Nat) := ⟨by decide⟩

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-- The ordinary real Cayley–Dickson octonions, as two ordinary quaternions. -/
abbrev Octonion := Quaternion ℝ × Quaternion ℝ

/-- The declared compact Cayley–Dickson convention; the doubling parameter is −1. -/
def octMul (x y : Octonion) : Octonion :=
  (x.1 * y.1 - star y.2 * x.2, y.2 * x.1 + x.2 * star y.1)

def octConj (x : Octonion) : Octonion := (star x.1, -x.2)
def octRe (x : Octonion) : ℝ := x.1.re
def octScalar (r : ℝ) : Octonion := ((r : Quaternion ℝ), 0)
def octDot (x y : Octonion) : ℝ := octRe (octMul x (octConj y))
def octNormSq (x : Octonion) : ℝ := Quaternion.normSq x.1 + Quaternion.normSq x.2

@[simp] theorem octRe_scalar (r : ℝ) : octRe (octScalar r) = r := rfl

@[simp] theorem octConj_conj (x : Octonion) : octConj (octConj x) = x := by
  simp [octConj]

@[simp] theorem octConj_scalar (r : ℝ) : octConj (octScalar r) = octScalar r := by
  simp [octConj, octScalar]

@[simp] theorem octConj_add (x y : Octonion) :
    octConj (x + y) = octConj x + octConj y := by
  simp [octConj, add_comm]

@[simp] theorem octConj_smul (r : ℝ) (x : Octonion) :
    octConj (r • x) = r • octConj x := by
  simp [octConj, smul_neg]

@[simp] theorem octMul_scalar_left (r : ℝ) (x : Octonion) :
    octMul (octScalar r) x = r • x := by
  apply Prod.ext <;>
    simp [octMul, octScalar, Quaternion.coe_mul_eq_smul, Quaternion.mul_coe_eq_smul]

@[simp] theorem octMul_scalar_right (r : ℝ) (x : Octonion) :
    octMul x (octScalar r) = r • x := by
  apply Prod.ext <;>
    simp [octMul, octScalar, Quaternion.coe_mul_eq_smul, Quaternion.mul_coe_eq_smul]

theorem octDot_coordinates (x y : Octonion) :
    octDot x y = x.1.re*y.1.re + x.1.imI*y.1.imI + x.1.imJ*y.1.imJ +
      x.1.imK*y.1.imK + x.2.re*y.2.re + x.2.imI*y.2.imI +
      x.2.imJ*y.2.imJ + x.2.imK*y.2.imK := by
  simp [octDot, octRe, octMul, octConj, Quaternion.re_mul]
  ring

theorem octDot_comm (x y : Octonion) : octDot x y = octDot y x := by
  simp only [octDot_coordinates]
  ring

theorem octConj_mul (x y : Octonion) :
    octConj (octMul x y) = octMul (octConj y) (octConj x) := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [octConj, octMul, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

theorem octMul_add_left (x y z : Octonion) :
    octMul (x+y) z = octMul x z + octMul y z := by
  simp [octMul, add_mul, mul_add, sub_add_sub_comm, add_assoc, add_left_comm, add_comm]

theorem octMul_add_right (x y z : Octonion) :
    octMul x (y+z) = octMul x y + octMul x z := by
  simp [octMul, add_mul, mul_add, sub_add_sub_comm, add_assoc, add_left_comm, add_comm]

theorem octMul_smul_left (r : ℝ) (x y : Octonion) :
    octMul (r • x) y = r • octMul x y := by
  simp [octMul, smul_sub, smul_add, smul_mul_assoc, mul_smul_comm]

theorem octMul_smul_right (r : ℝ) (x y : Octonion) :
    octMul x (r • y) = r • octMul x y := by
  simp [octMul, smul_sub, smul_add, smul_mul_assoc, mul_smul_comm]

def octConjAddHom : Octonion →+ Octonion where
  toFun := octConj
  map_zero' := by simp [octConj]
  map_add' := octConj_add

theorem octConj_sum (f : Fin 3 → Octonion) :
    octConj (∑ i, f i) = ∑ i, octConj (f i) := by
  change octConjAddHom (∑ i, f i) = ∑ i, octConjAddHom (f i)
  exact map_sum octConjAddHom f Finset.univ

theorem octAdd_conj (x : Octonion) :
    x + octConj x = (2 : ℝ) • octScalar (octRe x) := by
  apply Prod.ext <;> apply Quaternion.ext <;> simp [octConj, octScalar, octRe] <;> ring

theorem octScalar_of_conj (x : Octonion) (h : octConj x = x) :
    octScalar (octRe x) = x := by
  have h2 : (2 : ℝ) • x = (2 : ℝ) • octScalar (octRe x) := by
    simpa only [two_smul, h] using octAdd_conj x
  have h1 := congrArg (fun z : Octonion => (1/2 : ℝ) • z) h2
  norm_num [smul_smul] at h1
  exact h1.symm

@[simp] theorem octDot_self (x : Octonion) : octDot x x = octNormSq x := by
  rw [octDot_coordinates]
  simp [octNormSq, Quaternion.normSq_def']
  ring

theorem octNormSq_nonneg (x : Octonion) : 0 ≤ octNormSq x :=
  add_nonneg (Quaternion.normSq_nonneg (a := x.1)) (Quaternion.normSq_nonneg (a := x.2))

theorem octNormSq_eq_zero (x : Octonion) : octNormSq x = 0 ↔ x = 0 := by
  rw [octNormSq, add_eq_zero_iff_of_nonneg
    (Quaternion.normSq_nonneg (a := x.1)) (Quaternion.normSq_nonneg (a := x.2))]
  constructor
  · rintro ⟨h1, h2⟩
    exact Prod.ext (Quaternion.normSq_eq_zero.mp h1) (Quaternion.normSq_eq_zero.mp h2)
  · intro h
    cases h
    exact ⟨Quaternion.normSq_eq_zero.mpr rfl, Quaternion.normSq_eq_zero.mpr rfl⟩

/-- Real diagonal and upper off-diagonal coordinates (01,02,12). -/
@[ext] structure Albert where
  d0 : ℝ
  d1 : ℝ
  d2 : ℝ
  o01 : Octonion
  o02 : Octonion
  o12 : Octonion

namespace Albert

theorem extExplicit (x y : Albert)
    (h0 : x.d0 = y.d0) (h1 : x.d1 = y.d1) (h2 : x.d2 = y.d2)
    (h01 : x.o01 = y.o01) (h02 : x.o02 = y.o02) (h12 : x.o12 = y.o12) : x = y := by
  cases x
  cases y
  cases h0
  cases h1
  cases h2
  cases h01
  cases h02
  cases h12
  rfl

abbrev Coordinates := ℝ × ℝ × ℝ × Octonion × Octonion × Octonion

def coordinateEquiv : Albert ≃ Coordinates where
  toFun x := (x.d0, x.d1, x.d2, x.o01, x.o02, x.o12)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup Albert := coordinateEquiv.addCommGroup

def coordinateAddEquiv : Albert ≃+ Coordinates where
  toEquiv := coordinateEquiv
  map_add' _ _ := rfl

instance : Module ℝ Albert := coordinateAddEquiv.module ℝ

@[simp] theorem zero_d0 : (0 : Albert).d0 = 0 := rfl
@[simp] theorem zero_d1 : (0 : Albert).d1 = 0 := rfl
@[simp] theorem zero_d2 : (0 : Albert).d2 = 0 := rfl
@[simp] theorem zero_o01 : (0 : Albert).o01 = 0 := rfl
@[simp] theorem zero_o02 : (0 : Albert).o02 = 0 := rfl
@[simp] theorem zero_o12 : (0 : Albert).o12 = 0 := rfl
@[simp] theorem add_d0 (x y : Albert) : (x+y).d0 = x.d0+y.d0 := rfl
@[simp] theorem add_d1 (x y : Albert) : (x+y).d1 = x.d1+y.d1 := rfl
@[simp] theorem add_d2 (x y : Albert) : (x+y).d2 = x.d2+y.d2 := rfl
@[simp] theorem add_o01 (x y : Albert) : (x+y).o01 = x.o01+y.o01 := rfl
@[simp] theorem add_o02 (x y : Albert) : (x+y).o02 = x.o02+y.o02 := rfl
@[simp] theorem add_o12 (x y : Albert) : (x+y).o12 = x.o12+y.o12 := rfl
@[simp] theorem sub_d0 (x y : Albert) : (x-y).d0 = x.d0-y.d0 := rfl
@[simp] theorem sub_d1 (x y : Albert) : (x-y).d1 = x.d1-y.d1 := rfl
@[simp] theorem sub_d2 (x y : Albert) : (x-y).d2 = x.d2-y.d2 := rfl
@[simp] theorem sub_o01 (x y : Albert) : (x-y).o01 = x.o01-y.o01 := rfl
@[simp] theorem sub_o02 (x y : Albert) : (x-y).o02 = x.o02-y.o02 := rfl
@[simp] theorem sub_o12 (x y : Albert) : (x-y).o12 = x.o12-y.o12 := rfl
@[simp] theorem smul_d0 (r : ℝ) (x : Albert) : (r • x).d0 = r*x.d0 := rfl
@[simp] theorem smul_d1 (r : ℝ) (x : Albert) : (r • x).d1 = r*x.d1 := rfl
@[simp] theorem smul_d2 (r : ℝ) (x : Albert) : (r • x).d2 = r*x.d2 := rfl
@[simp] theorem smul_o01 (r : ℝ) (x : Albert) : (r • x).o01 = r • x.o01 := rfl
@[simp] theorem smul_o02 (r : ℝ) (x : Albert) : (r • x).o02 = r • x.o02 := rfl
@[simp] theorem smul_o12 (r : ℝ) (x : Albert) : (r • x).o12 = r • x.o12 := rfl

end Albert

def unit : Albert := ⟨1,1,1,0,0,0⟩
instance : One Albert := ⟨unit⟩

@[simp] theorem one_d0 : (1 : Albert).d0 = 1 := rfl
@[simp] theorem one_d1 : (1 : Albert).d1 = 1 := rfl
@[simp] theorem one_d2 : (1 : Albert).d2 = 1 := rfl
@[simp] theorem one_o01 : (1 : Albert).o01 = 0 := rfl
@[simp] theorem one_o02 : (1 : Albert).o02 = 0 := rfl
@[simp] theorem one_o12 : (1 : Albert).o12 = 0 := rfl

def toMatrix (x : Albert) : Matrix (Fin 3) (Fin 3) Octonion :=
  ![![octScalar x.d0, x.o01, x.o02],
    ![octConj x.o01, octScalar x.d1, x.o12],
    ![octConj x.o02, octConj x.o12, octScalar x.d2]]

/-- Binary matrix multiplication only; no associative matrix-algebra law is assumed. -/
def matrixMul (A B : Matrix (Fin 3) (Fin 3) Octonion) :
    Matrix (Fin 3) (Fin 3) Octonion := fun i j => ∑ k, octMul (A i k) (B k j)

def fromMatrix (A : Matrix (Fin 3) (Fin 3) Octonion) : Albert :=
  ⟨octRe (A 0 0), octRe (A 1 1), octRe (A 2 2), A 0 1, A 0 2, A 1 2⟩

/-- Native symmetrized binary matrix product, stored in Hermitian coordinates. -/
def jordan (x y : Albert) : Albert :=
  fromMatrix ((1/2 : ℝ) • (matrixMul (toMatrix x) (toMatrix y) +
    matrixMul (toMatrix y) (toMatrix x)))

def trace (x : Albert) : ℝ := x.d0+x.d1+x.d2
def inner (x y : Albert) : ℝ := trace (jordan x y)
def traceless (x : Albert) : Albert := x - (trace x / 3) • (1 : Albert)
def L (x z : Albert) : Albert := jordan x z
def U (x z : Albert) : Albert := (2 : ℝ) • jordan x (jordan x z) - jordan (jordan x x) z
def phi (x y z : Albert) : ℝ :=
  inner (U x (U y z) - U y (U x z)) (U z (jordan x y))

def triple (x y z : Albert) : Fin 3 → Albert := ![x,y,z]
def gram (x y z : Albert) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => inner (traceless (triple x y z i)) (traceless (triple x y z j))

/-- Ordered trace-one orthogonal idempotents summing to the unit. -/
structure Frame (p : Fin 3 → Albert) : Prop where
  trace_one : ∀ i, trace (p i) = 1
  idempotent : ∀ i, jordan (p i) (p i) = p i
  orthogonal : ∀ i j, i ≠ j → jordan (p i) (p j) = 0
  sum_unit : p 0 + p 1 + p 2 = 1

def encoder (p : Fin 3 → Albert) : Albert := p 2 - p 0
def ledger (p q r : Fin 3 → Albert) (i j k : Fin 3) : ℝ :=
  trace (jordan (jordan (p i) (q j)) (r k))
def UniformLedger (p q r : Fin 3 → Albert) : Prop :=
  ∀ i j k, ledger p q r i j k = 1/9

@[simp] theorem trace_unit : trace (1 : Albert) = 3 := by norm_num [trace, unit]
@[simp] theorem trace_add (x y : Albert) : trace (x+y) = trace x+trace y := by
  simp [trace]; ring
@[simp] theorem trace_sub (x y : Albert) : trace (x-y) = trace x-trace y := by
  simp [trace]; ring
@[simp] theorem trace_smul (r : ℝ) (x : Albert) : trace (r • x) = r * trace x := by
  simp [trace]; ring
@[simp] theorem trace_traceless (x : Albert) : trace (traceless x) = 0 := by
  simp [traceless] <;> ring

theorem toMatrix_hermitian (x : Albert) (i j : Fin 3) :
    octConj (toMatrix x i j) = toMatrix x j i := by
  fin_cases i <;> fin_cases j <;> simp [toMatrix]

theorem fromMatrix_toMatrix (x : Albert) : fromMatrix (toMatrix x) = x := rfl

theorem toMatrix_injective : Function.Injective toMatrix := by
  intro x y h
  simpa only [fromMatrix_toMatrix] using congrArg fromMatrix h

theorem matrixMul_conj (x y : Albert) (i j : Fin 3) :
    octConj (matrixMul (toMatrix x) (toMatrix y) i j) =
      matrixMul (toMatrix y) (toMatrix x) j i := by
  simp only [matrixMul, octConj_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [octConj_mul, toMatrix_hermitian, toMatrix_hermitian]

theorem toMatrix_fromMatrix_hermitian
    (A : Matrix (Fin 3) (Fin 3) Octonion)
    (h : ∀ i j, octConj (A i j) = A j i) : toMatrix (fromMatrix A) = A := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [toMatrix, fromMatrix] using octScalar_of_conj (A 0 0) (h 0 0)
  · rfl
  · rfl
  · simpa [toMatrix, fromMatrix] using h 0 1
  · simpa [toMatrix, fromMatrix] using octScalar_of_conj (A 1 1) (h 1 1)
  · rfl
  · simpa [toMatrix, fromMatrix] using h 0 2
  · simpa [toMatrix, fromMatrix] using h 1 2
  · simpa [toMatrix, fromMatrix] using octScalar_of_conj (A 2 2) (h 2 2)

theorem toMatrix_jordan (x y : Albert) :
    toMatrix (jordan x y) = (1/2 : ℝ) •
      (matrixMul (toMatrix x) (toMatrix y) + matrixMul (toMatrix y) (toMatrix x)) := by
  apply toMatrix_fromMatrix_hermitian
  intro i j
  change octConj ((1/2 : ℝ) • (matrixMul (toMatrix x) (toMatrix y) i j +
    matrixMul (toMatrix y) (toMatrix x) i j)) =
    (1/2 : ℝ) • (matrixMul (toMatrix x) (toMatrix y) j i +
      matrixMul (toMatrix y) (toMatrix x) j i)
  rw [octConj_smul, octConj_add, matrixMul_conj, matrixMul_conj, add_comm]

theorem jordan_comm (x y : Albert) : jordan x y = jordan y x := by
  unfold jordan
  rw [add_comm]

theorem jordan_d0 (x y : Albert) :
    (jordan x y).d0 = x.d0*y.d0 + octDot x.o01 y.o01 + octDot x.o02 y.o02 := by
  simp [jordan, fromMatrix, matrixMul, toMatrix, Fin.sum_univ_three,
    octRe, octScalar, octMul, octConj, octDot, Quaternion.re_mul]
  ring

theorem jordan_d1 (x y : Albert) :
    (jordan x y).d1 = x.d1*y.d1 + octDot x.o01 y.o01 + octDot x.o12 y.o12 := by
  simp [jordan, fromMatrix, matrixMul, toMatrix, Fin.sum_univ_three,
    octRe, octScalar, octMul, octConj, octDot, Quaternion.re_mul]
  ring

theorem jordan_d2 (x y : Albert) :
    (jordan x y).d2 = x.d2*y.d2 + octDot x.o02 y.o02 + octDot x.o12 y.o12 := by
  simp [jordan, fromMatrix, matrixMul, toMatrix, Fin.sum_univ_three,
    octRe, octScalar, octMul, octConj, octDot, Quaternion.re_mul]
  ring

theorem jordan_o01 (x y : Albert) :
    (jordan x y).o01 = (1/2 : ℝ) •
      ((x.d0+x.d1) • y.o01 + (y.d0+y.d1) • x.o01 +
        octMul x.o02 (octConj y.o12) + octMul y.o02 (octConj x.o12)) := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [jordan, fromMatrix, matrixMul, toMatrix, Fin.sum_univ_three,
      octRe, octScalar, octMul, octConj, Quaternion.re_mul,
      Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

theorem jordan_o02 (x y : Albert) :
    (jordan x y).o02 = (1/2 : ℝ) •
      ((x.d0+x.d2) • y.o02 + (y.d0+y.d2) • x.o02 +
        octMul x.o01 y.o12 + octMul y.o01 x.o12) := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [jordan, fromMatrix, matrixMul, toMatrix, Fin.sum_univ_three,
      octRe, octScalar, octMul, octConj, Quaternion.re_mul,
      Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

theorem jordan_o12 (x y : Albert) :
    (jordan x y).o12 = (1/2 : ℝ) •
      ((x.d1+x.d2) • y.o12 + (y.d1+y.d2) • x.o12 +
        octMul (octConj x.o01) y.o02 + octMul (octConj y.o01) x.o02) := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [jordan, fromMatrix, matrixMul, toMatrix, Fin.sum_univ_three,
      octRe, octScalar, octMul, octConj, Quaternion.re_mul,
      Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

theorem inner_coordinates (x y : Albert) :
    inner x y = x.d0*y.d0+x.d1*y.d1+x.d2*y.d2 +
      2*(octDot x.o01 y.o01+octDot x.o02 y.o02+octDot x.o12 y.o12) := by
  simp only [inner, trace, jordan_d0, jordan_d1, jordan_d2]
  ring

theorem inner_comm (x y : Albert) : inner x y = inner y x := by
  simp only [inner, jordan_comm]

theorem inner_self_coordinates (x : Albert) :
    inner x x = x.d0^2+x.d1^2+x.d2^2 +
      2*(octNormSq x.o01+octNormSq x.o02+octNormSq x.o12) := by
  simp only [inner_coordinates, octDot_self]
  ring

theorem inner_self_nonneg (x : Albert) : 0 ≤ inner x x := by
  rw [inner_self_coordinates]
  exact add_nonneg (add_nonneg (add_nonneg (sq_nonneg x.d0) (sq_nonneg x.d1))
    (sq_nonneg x.d2)) (mul_nonneg (by norm_num)
      (add_nonneg (add_nonneg (octNormSq_nonneg x.o01) (octNormSq_nonneg x.o02))
        (octNormSq_nonneg x.o12)))

theorem inner_self_eq_zero (x : Albert) : inner x x = 0 ↔ x = 0 := by
  constructor
  · intro h
    rw [inner_self_coordinates] at h
    have h01 := octNormSq_nonneg x.o01
    have h02 := octNormSq_nonneg x.o02
    have h12 := octNormSq_nonneg x.o12
    have hd0 : x.d0 = 0 := by nlinarith [sq_nonneg x.d1, sq_nonneg x.d2]
    have hd1 : x.d1 = 0 := by nlinarith [sq_nonneg x.d0, sq_nonneg x.d2]
    have hd2 : x.d2 = 0 := by nlinarith [sq_nonneg x.d0, sq_nonneg x.d1]
    have ho01 : x.o01 = 0 := (octNormSq_eq_zero _).mp (by nlinarith [sq_nonneg x.d0, sq_nonneg x.d1, sq_nonneg x.d2])
    have ho02 : x.o02 = 0 := (octNormSq_eq_zero _).mp (by nlinarith [sq_nonneg x.d0, sq_nonneg x.d1, sq_nonneg x.d2])
    have ho12 : x.o12 = 0 := (octNormSq_eq_zero _).mp (by nlinarith [sq_nonneg x.d0, sq_nonneg x.d1, sq_nonneg x.d2])
    apply Albert.extExplicit <;> simp [hd0, hd1, hd2, ho01, ho02, ho12]
  · rintro rfl
    simp [inner_self_coordinates, octNormSq, Quaternion.normSq_def']

end
end Glennie
