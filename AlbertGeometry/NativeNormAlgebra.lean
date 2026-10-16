/- Native algebraic norm/unit round trip.
The adjoint below is the literal quadratic algebraic expression, not a claimed
Frechet derivative. Binding NewtonNorm to the native determinant and genuine
norm differentiation are separate proof obligations.
-/
module

public import Glennie.Native.AlgebraLaws
public import Glennie.BasicLaws

@[expose] public section
namespace AlbertGeometry.NativeNormAlgebra
noncomputable section
open Glennie

/-- Literal Newton cubic expression using the actual native binary product and
raw trace pairing. No octonion or matrix associativity is invoked. -/
def nativeNewtonNorm (x : Albert) : ℝ :=
  (Glennie.trace x ^ 3 - 3 * Glennie.trace x * Glennie.inner x x +
    2 * Glennie.inner x (jordan x x)) / 6

/-- Literal quadratic algebraic expression; its derivative interpretation is
not part of this module. -/
def nativeAdjoint (x : Albert) : Albert :=
  jordan x x - Glennie.trace x • x +
    ((Glennie.trace x ^ 2 - Glennie.inner x x) / 2) • (1 : Albert)

/-- Unhalved polarization of the literal quadratic expression. -/
def nativeCross (x y : Albert) : Albert :=
  nativeAdjoint (x + y) - nativeAdjoint x - nativeAdjoint y

/-- The norm/unit reconstruction formula, using raw B(x,y)=inner(x,y).
For the normalized metric g=B/3, the final coefficient uses 3*g(x,y). -/
def nativeRecoveredProduct (x y : Albert) : Albert :=
  (1 / 2 : ℝ) • (nativeCross x y + Glennie.trace y • x +
    Glennie.trace x • y -
    (Glennie.trace x * Glennie.trace y - Glennie.inner x y) • (1 : Albert))

@[simp] theorem nativeNewtonNorm_zero : nativeNewtonNorm (0 : Albert) = 0 := by
  simp [nativeNewtonNorm]

@[simp] theorem nativeNewtonNorm_one : nativeNewtonNorm (1 : Albert) = 1 := by
  norm_num [nativeNewtonNorm]

theorem nativeNewtonNorm_smul (r : ℝ) (x : Albert) :
    nativeNewtonNorm (r • x) = r ^ 3 * nativeNewtonNorm x := by
  simp only [nativeNewtonNorm, trace_smul, jordan_smul_left, jordan_smul_right,
    inner_smul_left, inner_smul_right]
  ring

/-- Exact finite polynomial restriction at the actual unit. This is not a
HasFDerivAt claim; it identifies the three algebraic coefficients directly. -/
theorem nativeNewtonNorm_unit_line (x : Albert) (t : ℝ) :
    nativeNewtonNorm ((1 : Albert) + t • x) =
      1 + t * Glennie.trace x +
      t ^ 2 * ((Glennie.trace x ^ 2 - Glennie.inner x x) / 2) +
      t ^ 3 * nativeNewtonNorm x := by
  have hxx : Glennie.trace (jordan x x) = Glennie.inner x x := rfl
  simp only [nativeNewtonNorm, trace_add, trace_smul, trace_unit,
    jordan_add_left, jordan_add_right, jordan_smul_left, jordan_smul_right,
    jordan_unit_left, jordan_unit_right, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, inner_unit_left, inner_unit_right, hxx]
  ring

/-- The exact finite polynomial on any native affine line. The adjoint pairing
is a proved coefficient here; genuine Frechet differentiation is still separate. -/
theorem nativeNewtonNorm_line (x y : Albert) (t : ℝ) :
    nativeNewtonNorm (x + t • y) = nativeNewtonNorm x +
      t * Glennie.inner (nativeAdjoint x) y +
      t ^ 2 * Glennie.inner (nativeAdjoint y) x + t ^ 3 * nativeNewtonNorm y := by
  simp only [nativeNewtonNorm, nativeAdjoint, trace_add, trace_smul,
    jordan_add_left, jordan_add_right, jordan_smul_left, jordan_smul_right,
    inner_add_left, inner_add_right, inner_sub_left,
    inner_smul_left, inner_smul_right, inner_unit_left]
  simp only [jordan_comm y x, inner_comm y x,
    inner_comm y (jordan x x), inner_comm x (jordan y y),
    inner_jordan_associative x x y, inner_jordan_associative y y x]
  ring

@[simp] theorem nativeAdjoint_zero : nativeAdjoint (0 : Albert) = 0 := by
  simp [nativeAdjoint]

@[simp] theorem nativeAdjoint_one : nativeAdjoint (1 : Albert) = 1 := by
  simp only [nativeAdjoint, jordan_unit_left, trace_unit, inner_unit_left]
  norm_num <;> module

theorem nativeAdjoint_smul (r : ℝ) (x : Albert) :
    nativeAdjoint (r • x) = r ^ 2 • nativeAdjoint x := by
  simp only [nativeAdjoint, trace_smul, jordan_smul_left, jordan_smul_right,
    inner_smul_left, inner_smul_right]
  module

/-- Actual unhalved polarization, derived solely from native bilinearity. -/
theorem nativeCross_eq (x y : Albert) :
    nativeCross x y = (2 : ℝ) • jordan x y - Glennie.trace y • x -
      Glennie.trace x • y +
      (Glennie.trace x * Glennie.trace y - Glennie.inner x y) • (1 : Albert) := by
  simp only [nativeCross, nativeAdjoint, trace_add, jordan_add_left,
    jordan_add_right, inner_add_left, inner_add_right,
    jordan_comm y x, inner_comm y x]
  module

theorem nativeAdjoint_add (x y : Albert) :
    nativeAdjoint (x + y) = nativeAdjoint x + nativeAdjoint y + nativeCross x y := by
  simp only [nativeCross]
  abel

theorem nativeCross_comm (x y : Albert) : nativeCross x y = nativeCross y x := by
  simp only [nativeCross, add_comm x y]
  abel

theorem nativeCross_add_left (x y z : Albert) :
    nativeCross (x + y) z = nativeCross x z + nativeCross y z := by
  simp only [nativeCross_eq, jordan_add_left, trace_add, inner_add_left]
  module

theorem nativeCross_add_right (x y z : Albert) :
    nativeCross x (y + z) = nativeCross x y + nativeCross x z := by
  rw [nativeCross_comm x (y + z), nativeCross_add_left,
    nativeCross_comm y x, nativeCross_comm z x]

theorem nativeCross_smul_left (r : ℝ) (x y : Albert) :
    nativeCross (r • x) y = r • nativeCross x y := by
  simp only [nativeCross_eq, jordan_smul_left, trace_smul, inner_smul_left]
  module

theorem nativeCross_smul_right (r : ℝ) (x y : Albert) :
    nativeCross x (r • y) = r • nativeCross x y := by
  rw [nativeCross_comm x (r • y), nativeCross_smul_left, nativeCross_comm y x]

theorem nativeCross_one_left (x : Albert) :
    nativeCross (1 : Albert) x = Glennie.trace x • (1 : Albert) - x := by
  simp only [nativeCross_eq, jordan_unit_left, trace_unit, inner_unit_left]
  module

theorem nativeCross_one_right (x : Albert) :
    nativeCross x (1 : Albert) = Glennie.trace x • (1 : Albert) - x := by
  rw [nativeCross_comm, nativeCross_one_left]

theorem nativeAdjoint_unit_line (x : Albert) (t : ℝ) :
    nativeAdjoint ((1 : Albert) + t • x) =
      (1 : Albert) + t • (Glennie.trace x • (1 : Albert) - x) +
        t ^ 2 • nativeAdjoint x := by
  rw [nativeAdjoint_add, nativeAdjoint_one, nativeAdjoint_smul,
    nativeCross_smul_right, nativeCross_one_left]
  abel

/-- The reconstructed binary product is literally the compact native Jordan
product, without a new premise on an unknown cubic or any octonion associativity. -/
theorem nativeRecoveredProduct_eq (x y : Albert) :
    nativeRecoveredProduct x y = jordan x y := by
  simp only [nativeRecoveredProduct, nativeCross_eq]
  module

@[simp] theorem nativeRecoveredProduct_one_left (x : Albert) :
    nativeRecoveredProduct (1 : Albert) x = x := by
  rw [nativeRecoveredProduct_eq, jordan_unit_left]

@[simp] theorem nativeRecoveredProduct_one_right (x : Albert) :
    nativeRecoveredProduct x (1 : Albert) = x := by
  rw [nativeRecoveredProduct_eq, jordan_unit_right]

theorem nativeRecoveredProduct_comm (x y : Albert) :
    nativeRecoveredProduct x y = nativeRecoveredProduct y x := by
  rw [nativeRecoveredProduct_eq, nativeRecoveredProduct_eq, jordan_comm]

/-- The raw pairing is recovered with its actual factor of three relative to
trace/3; no inner-product instance is installed or overwritten. -/
theorem trace_nativeRecoveredProduct (x y : Albert) :
    Glennie.trace (nativeRecoveredProduct x y) =
      3 * (Glennie.inner x y / 3) := by
  rw [nativeRecoveredProduct_eq]
  change Glennie.inner x y = 3 * (Glennie.inner x y / 3)
  ring

end
end AlbertGeometry.NativeNormAlgebra
