/- The exact 20x20 matrix and its
determinant certificate, with the statement ring fixed as
  R6 = Z[1/6, theta]/(theta^2 - 3) = AdjoinRoot (X^2 - 3) over Localization.Away 6.
  * `JZ` is 72 J with entries in Z3 = Z[sqrt3] (literal). The real matrix is
    `JQ r n = (re + im sqrt3) / 72`; the R6 matrix is `JR = 72^-1 . iota(JZ)`.
  * Modulo p = 65521 with sqrt3 -> 627 (a ring hom Z3 -> ZMod p; no field
    hom Q(sqrt3) -> F_p is used): a row-pivoted LU factorization
    (seven explicit swaps, unit lower L, upper U) is checked by kernel `decide`
    on finite ZMod data, giving phiP (det JZ) = 32400.
  * Hence det JZ /= 0 in Z3; through the injective liftR (sqrt3 -> Real.sqrt 3),
    det JQ /= 0 over R; over R6, det JR /= 0 and toZMod (det JR) = 14151.
The bridge identifying JQ with the FlowFamily `jacobianEntry` at the flat base
is NOT in this file (see Rank20Reduction).
No `simp only` on vector
literals; every literal fact is a kernel `decide +kernel` on a closed finite
statement over ZMod 65521, Fin 20 or the integer units. -/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Glennie.Compact.Rank20Certificate

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Z[sqrt3] as a local ring (Mathlib's Zsqrtd pattern with d = 3) -/

/-- An element re + im sqrt3 of Z[sqrt3]. -/
@[ext]
structure Z3 where
  /-- The rational-integer part. -/
  re : ℤ
  /-- The coefficient of sqrt3. -/
  im : ℤ

namespace Z3

instance : Zero Z3 := ⟨⟨0, 0⟩⟩

instance : One Z3 := ⟨⟨1, 0⟩⟩

instance : Add Z3 := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩

instance : Neg Z3 := ⟨fun z => ⟨-z.re, -z.im⟩⟩

instance : Mul Z3 := ⟨fun z w => ⟨z.re * w.re + 3 * z.im * w.im, z.re * w.im + z.im * w.re⟩⟩

@[simp] theorem re_zero : (0 : Z3).re = 0 := rfl

@[simp] theorem im_zero : (0 : Z3).im = 0 := rfl

@[simp] theorem re_one : (1 : Z3).re = 1 := rfl

@[simp] theorem im_one : (1 : Z3).im = 0 := rfl

@[simp] theorem re_add (z w : Z3) : (z + w).re = z.re + w.re := rfl

@[simp] theorem im_add (z w : Z3) : (z + w).im = z.im + w.im := rfl

@[simp] theorem re_neg (z : Z3) : (-z).re = -z.re := rfl

@[simp] theorem im_neg (z : Z3) : (-z).im = -z.im := rfl

@[simp] theorem re_mul (z w : Z3) : (z * w).re = z.re * w.re + 3 * z.im * w.im := rfl

@[simp] theorem im_mul (z w : Z3) : (z * w).im = z.re * w.im + z.im * w.re := rfl

instance addCommGroup : AddCommGroup Z3 := by
  refine
  { sub := fun a b => a + -b
    nsmul := @nsmulRec Z3 ⟨0⟩ ⟨(· + ·)⟩
    zsmul := @zsmulRec Z3 ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩ (@nsmulRec Z3 ⟨0⟩ ⟨(· + ·)⟩)
    add_assoc := ?_
    zero_add := ?_
    add_zero := ?_
    neg_add_cancel := ?_
    add_comm := ?_ } <;>
  intros <;>
  ext <;>
  simp [add_comm, add_left_comm]

@[simp] theorem re_sub (z w : Z3) : (z - w).re = z.re - w.re := rfl

@[simp] theorem im_sub (z w : Z3) : (z - w).im = z.im - w.im := rfl

instance addGroupWithOne : AddGroupWithOne Z3 :=
  { Z3.addCommGroup with
    natCast := fun n => ⟨n, 0⟩
    intCast := fun n => ⟨n, 0⟩ }

instance commRing : CommRing Z3 := by
  refine
  { Z3.addGroupWithOne with
    npow := @npowRec Z3 ⟨1⟩ ⟨(· * ·)⟩,
    add_comm := ?_
    left_distrib := ?_
    right_distrib := ?_
    zero_mul := ?_
    mul_zero := ?_
    mul_assoc := ?_
    one_mul := ?_
    mul_one := ?_
    mul_comm := ?_ } <;>
  intros <;>
  ext <;>
  simp <;>
  ring

end Z3

/-- The ring hom Z3 -> R sending sqrt3 to a chosen c with c * c = 3. -/
def liftZ3 {R : Type*} [CommRing R] (c : R) (hc : c * c = 3) : Z3 →+* R where
  toFun x := (x.re : R) + (x.im : R) * c
  map_one' := by simp
  map_mul' a b := by
    simp only [Z3.re_mul, Z3.im_mul, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
    linear_combination (-((a.im : R) * (b.im : R))) * hc
  map_zero' := by simp
  map_add' a b := by
    simp only [Z3.re_add, Z3.im_add, Int.cast_add]
    ring

theorem liftZ3_apply {R : Type*} [CommRing R] (c : R) (hc : c * c = 3) (x : Z3) :
    liftZ3 c hc x = (x.re : R) + (x.im : R) * c := rfl

/-! ## 72 J over Z3 (rows: rowIndex order; columns: direction order) -/

/-- 72 times the flat-base derivative matrix, entry ⟨a, b⟩ = a + b sqrt3. -/
def JZ : Matrix (Fin 20) (Fin 20) Z3 :=
  !![⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 2⟩, ⟨-2, 0⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 2⟩, ⟨4, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-2, 0⟩, ⟨0, -2⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 2⟩, ⟨-2, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨0, 2⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 2⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 2⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-2, 0⟩, ⟨0, 2⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, -2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨0, -2⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-2, 0⟩, ⟨0, -2⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, -2⟩, ⟨-2, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨0, -2⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, -2⟩, ⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-2, 0⟩, ⟨0, 2⟩;
     ⟨0, -4⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩;
     ⟨0, -4⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 2⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, -2⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-2, 0⟩, ⟨0, -2⟩;
     ⟨0, -4⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, -2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨0, 2⟩;
     ⟨0, 0⟩, ⟨8, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, -2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, -2⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-2, 0⟩, ⟨0, 2⟩;
     ⟨0, 0⟩, ⟨8, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨8, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 2⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-2, 0⟩, ⟨0, -2⟩;
     ⟨0, 4⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 2⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨0, -2⟩;
     ⟨0, 4⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, -2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-2, 0⟩, ⟨0, 2⟩;
     ⟨0, 4⟩, ⟨4, 0⟩, ⟨-2, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 4⟩, ⟨4, 0⟩, ⟨-2, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-2, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨4, 0⟩, ⟨-2, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨-8, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-2, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨-8, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨4, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]

/-! ## Reduction modulo p = 65521, sqrt3 -> 627 -/

theorem sq627 : (627 : ZMod 65521) * 627 = 3 := by
  decide +kernel

/-- The ring hom Z3 -> ZMod 65521 sending sqrt3 to 627. -/
def phiP : Z3 →+* ZMod 65521 := liftZ3 627 sq627

theorem phiP_apply (x : Z3) : phiP x = (x.re : ZMod 65521) + (x.im : ZMod 65521) * 627 := rfl

/-- The row permutation of the pivoted elimination (seven swaps). -/
def rowPerm : Equiv.Perm (Fin 20) :=
  Equiv.swap 0 8 *
    Equiv.swap 1 11 *
    Equiv.swap 6 8 *
    Equiv.swap 7 8 *
    Equiv.swap 8 9 *
    Equiv.swap 9 10 *
    Equiv.swap 18 19

/-- Unit lower-triangular factor (mod p). -/
def Lp : Matrix (Fin 20) (Fin 20) (ZMod 65521) :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 65519, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 65519, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 65519, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 65520, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 65520, 65520, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     1, 0, 0, 0, 65520, 0, 43681, 21841, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 65520, 21841, 43681, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 65520, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 1, 65520, 0, 65520, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 65520, 0, 43681, 21841, 65520, 65520, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 65520, 21841, 43681, 0, 65520, 2, 1, 1, 1, 0, 0, 0, 0, 0, 0;
     65520, 65520, 0, 0, 1, 1, 65520, 65520, 0, 0, 0, 0, 65520, 0, 1, 0, 0, 0, 0, 0;
     65520, 65520, 0, 0, 0, 1, 43680, 21840, 0, 1, 65519, 65520, 65520, 65520, 32760, 1, 0, 0, 0, 0;
     65520, 0, 65520, 0, 0, 1, 65520, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
     65520, 0, 65520, 0, 0, 1, 21840, 43681, 65520, 0, 65520, 65520, 0, 0, 0, 0, 65520, 1, 0, 0;
     0, 65520, 2, 65520, 0, 0, 21840, 43680, 1, 1, 0, 0, 65520, 0, 0, 0, 0, 65520, 1, 0;
     0, 65520, 2, 65520, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65520, 1, 0, 1]

/-- Upper-triangular factor (mod p). -/
def Up : Matrix (Fin 20) (Fin 20) (ZMod 65521) :=
  !![63013, 65517, 0, 0, 2, 64267, 0, 0, 65517, 0, 2, 0, 0, 0, 2, 1254, 64894, 1, 4, 0;
     0, 8, 0, 0, 2, 64267, 0, 0, 2, 64267, 65520, 627, 0, 0, 2, 64267, 627, 1, 65519, 1254;
     0, 0, 2, 1254, 65519, 64267, 0, 2, 0, 0, 1, 64894, 64267, 2, 0, 0, 0, 65519, 65519, 1254;
     0, 0, 0, 2508, 65515, 64267, 64894, 3, 0, 0, 3, 63640, 64267, 6, 0, 0, 627, 65518, 65515, 3762;
     0, 0, 0, 0, 6, 64267, 627, 3, 0, 0, 65518, 627, 64267, 65515, 0, 0, 64894, 65518, 6, 64267;
     0, 0, 0, 0, 0, 63013, 1254, 0, 0, 0, 0, 1254, 63013, 0, 0, 0, 64267, 0, 0, 63013;
     0, 0, 0, 0, 0, 0, 1881, 65518, 0, 0, 65518, 1881, 0, 0, 0, 0, 63640, 3, 6, 61759;
     0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65515, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 6, 1254, 65516, 64894, 64267, 65515, 0, 63013, 1254, 0, 65519, 64267;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 63013, 4, 1254, 64267, 6, 65515, 1254, 64894, 65518, 65513, 2508;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 63640, 0, 0, 0, 0, 0, 0, 65515, 3762;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3762, 0, 0, 0, 0, 0, 0, 0, 57997;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 61759, 65515, 65509, 0, 0, 65515, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 6, 3762, 63640, 3, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65509, 0, 0, 65515, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3762, 63640, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64267, 2, 8, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 63013;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 63013;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5016]

/-- The LU certificate, checked by kernel evaluation on finite ZMod data. -/
theorem lu_certificate : (JZ.map phiP).submatrix rowPerm id = Lp * Up := by
  decide +kernel

theorem Up_upper : Up.IsUpperTriangular := by
  have hb : (List.finRange 20).all (fun i => (List.finRange 20).all
      (fun j => decide (j < i → Up i j = 0))) = true := by
    decide +kernel
  intro i j hij
  have h1 := List.all_eq_true.mp hb i (List.mem_finRange i)
  exact of_decide_eq_true (List.all_eq_true.mp h1 j (List.mem_finRange j)) hij

theorem Lp_lower : Lp.IsLowerTriangular := by
  have hb : (List.finRange 20).all (fun i => (List.finRange 20).all
      (fun j => decide (i < j → Lp i j = 0))) = true := by
    decide +kernel
  intro i j hij
  have h1 := List.all_eq_true.mp hb i (List.mem_finRange i)
  exact of_decide_eq_true (List.all_eq_true.mp h1 j (List.mem_finRange j))
    (OrderDual.toDual_lt_toDual.mp hij)

theorem det_Lp : Lp.det = 1 := by
  rw [Matrix.det_of_isLowerTriangular Lp Lp_lower]
  decide +kernel

theorem det_Up : Up.det = 33121 := by
  rw [Matrix.det_of_isUpperTriangular Up_upper]
  decide +kernel

theorem sign_rowPerm : Equiv.Perm.sign rowPerm = -1 := by
  rw [rowPerm, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul]
  rw [Equiv.Perm.sign_swap (show (0 : Fin 20) ≠ 8 by decide),
    Equiv.Perm.sign_swap (show (1 : Fin 20) ≠ 11 by decide),
    Equiv.Perm.sign_swap (show (6 : Fin 20) ≠ 8 by decide),
    Equiv.Perm.sign_swap (show (7 : Fin 20) ≠ 8 by decide),
    Equiv.Perm.sign_swap (show (8 : Fin 20) ≠ 9 by decide),
    Equiv.Perm.sign_swap (show (9 : Fin 20) ≠ 10 by decide),
    Equiv.Perm.sign_swap (show (18 : Fin 20) ≠ 19 by decide)]
  decide +kernel

/-- phiP (det JZ) = det (72 J) mod p. -/
theorem phiP_det_JZ : phiP JZ.det = 32400 := by
  have h1 := Matrix.det_permute rowPerm (JZ.map phiP)
  rw [lu_certificate, Matrix.det_mul, det_Lp, det_Up, sign_rowPerm] at h1
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one] at h1
  have hD : (JZ.map phiP).det = -33121 := by linear_combination h1
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hD]
  decide +kernel

theorem det_JZ_ne_zero : JZ.det ≠ 0 := by
  intro h
  have h2 := phiP_det_JZ
  rw [h, map_zero] at h2
  exact absurd h2 (by decide +kernel)

/-! ## The real matrix -/

theorem sqrt3_mul_self : Real.sqrt 3 * Real.sqrt 3 = 3 :=
  Real.mul_self_sqrt (by norm_num)

/-- The ring hom Z3 -> R sending sqrt3 to Real.sqrt 3. -/
def liftR : Z3 →+* ℝ := liftZ3 (Real.sqrt 3) sqrt3_mul_self

theorem liftR_apply (x : Z3) : liftR x = (x.re : ℝ) + (x.im : ℝ) * Real.sqrt 3 := rfl

/-- a * a = 3 * k forces a % 3 = 0. -/
theorem emod_three_of_mul_self {a k : ℤ} (h : a * a = 3 * k) : a % 3 = 0 := by
  have h1 : a * a % 3 = 0 := by rw [h, Int.mul_emod_right]
  rw [Int.mul_emod] at h1
  rcases (by omega : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2) with hr | hr | hr
  · exact hr
  · rw [hr] at h1
    omega
  · rw [hr] at h1
    omega

/-- Descent: a * a = 3 * (b * b) over the integers forces b = 0. -/
theorem three_descent : ∀ (n : ℕ) (a b : ℤ), b.natAbs ≤ n → a * a = 3 * (b * b) → b = 0 := by
  intro n
  induction n with
  | zero =>
    intro a b hb _
    exact Int.natAbs_eq_zero.mp (Nat.le_zero.mp hb)
  | succ n ih =>
    intro a b hb h
    obtain ⟨c, rfl⟩ : ∃ c, a = 3 * c :=
      ⟨a / 3, by have h3 := emod_three_of_mul_self h; omega⟩
    have h2 : b * b = 3 * (c * c) := by
      have h' : (3 : ℤ) * (b * b) = 3 * (3 * (c * c)) := by rw [← h]; ring
      exact mul_left_cancel₀ (by norm_num) h'
    obtain ⟨d, rfl⟩ : ∃ d, b = 3 * d :=
      ⟨b / 3, by have h3 := emod_three_of_mul_self h2; omega⟩
    have h4 : c * c = 3 * (d * d) := by
      have h' : (3 : ℤ) * (c * c) = 3 * (3 * (d * d)) := by rw [← h2]; ring
      exact mul_left_cancel₀ (by norm_num) h'
    have hd : d.natAbs ≤ n := by
      rw [Int.natAbs_mul] at hb
      have h3 : (3 : ℤ).natAbs = 3 := rfl
      rw [h3] at hb
      omega
    rw [ih c d hd h4, mul_zero]

/-- 3 is not the square of an integer: the explicit non-square fact of the step-6 shape. -/
theorem three_ne_sq (n : ℤ) : (3 : ℤ) ≠ n * n := by
  intro h
  have h1 : n * n = 3 * (1 * 1) := by linarith
  exact one_ne_zero (three_descent (1 : ℤ).natAbs n 1 le_rfl h1)

theorem liftR_eq_zero {x : Z3} (h : liftR x = 0) : x = 0 := by
  rw [liftR_apply] at h
  have hre : (x.re : ℝ) = -((x.im : ℝ) * Real.sqrt 3) := by linarith
  have hsq : (x.re : ℝ) * x.re = 3 * ((x.im : ℝ) * x.im) := by
    rw [hre]
    linear_combination ((x.im : ℝ) * x.im) * sqrt3_mul_self
  have hz : x.re * x.re = 3 * (x.im * x.im) := by exact_mod_cast hsq
  have him : x.im = 0 := three_descent x.im.natAbs x.re x.im le_rfl hz
  have hre0 : x.re = 0 := by
    rw [him] at hz
    simpa using hz
  exact Z3.ext hre0 him

theorem liftR_injective : Function.Injective liftR := by
  intro x y hxy
  have h : liftR (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp (liftR_eq_zero h)

/-- The real flat-base matrix J. -/
def JQ : Matrix (Fin 20) (Fin 20) ℝ :=
  Matrix.of fun r n => (((JZ r n).re : ℝ) + ((JZ r n).im : ℝ) * Real.sqrt 3) / 72

theorem JQ_eq : JQ = (72 : ℝ)⁻¹ • JZ.map liftR := by
  ext r n
  simp only [JQ, Matrix.of_apply, Matrix.smul_apply, Matrix.map_apply, liftR_apply, smul_eq_mul]
  ring

/-- The real 20x20 minor is nonsingular. -/
theorem det_JQ_ne_zero : JQ.det ≠ 0 := by
  rw [JQ_eq, Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
  intro h
  exact det_JZ_ne_zero (liftR_injective (h.trans (map_zero liftR).symm))

/-! ## The statement ring R6 = Z[1/6, theta]/(theta^2 - 3) -/

/-- Z[1/6]. -/
abbrev L6 : Type := Localization.Away (6 : ℤ)

/-- The polynomial X^2 - 3 over Z[1/6]. -/
abbrev f6 : Polynomial L6 := Polynomial.X ^ 2 - Polynomial.C (3 : L6)

/-- R6 = Z[1/6, theta]/(theta^2 - 3). -/
abbrev R6 : Type := AdjoinRoot f6

theorem root_mul_self : AdjoinRoot.root f6 * AdjoinRoot.root f6 = 3 := by
  have h : AdjoinRoot.mk f6 (Polynomial.X ^ 2 - Polynomial.C (3 : L6)) = 0 := AdjoinRoot.mk_self
  rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, map_ofNat] at h
  linear_combination h

/-- The internal route: Z3 -> R6, sqrt3 -> theta. -/
def iota : Z3 →+* R6 := liftZ3 (AdjoinRoot.root f6) root_mul_self

theorem iota_apply (x : Z3) : iota x = (x.re : R6) + (x.im : R6) * AdjoinRoot.root f6 := rfl

theorem isUnit_six_real : IsUnit ((Int.castRingHom ℝ) 6) := by
  rw [isUnit_iff_ne_zero]
  norm_num

def toRealL : L6 →+* ℝ := IsLocalization.Away.lift (6 : ℤ) isUnit_six_real

theorem toReal_root_eval : f6.eval₂ toRealL (Real.sqrt 3) = 0 := by
  simp only [f6, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
  simp only [map_ofNat]
  rw [Real.sq_sqrt (by norm_num)]
  norm_num

/-- R6 -> R, theta -> sqrt3. -/
def toReal : R6 →+* ℝ := AdjoinRoot.lift toRealL (Real.sqrt 3) toReal_root_eval

theorem isUnit_six_mod : IsUnit ((Int.castRingHom (ZMod 65521)) 6) :=
  IsUnit.of_mul_eq_one (54601 : ZMod 65521) (by decide +kernel)

def toZModL : L6 →+* ZMod 65521 := IsLocalization.Away.lift (6 : ℤ) isUnit_six_mod

theorem toZMod_root_eval : f6.eval₂ toZModL 627 = 0 := by
  simp only [f6, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
  simp only [map_ofNat]
  decide +kernel

/-- R6 -> ZMod 65521, theta -> 627, 1/6 -> 54601. -/
def toZMod : R6 →+* ZMod 65521 := AdjoinRoot.lift toZModL 627 toZMod_root_eval

theorem toZMod_root : toZMod (AdjoinRoot.root f6) = 627 := by
  rw [toZMod, AdjoinRoot.lift_root]

theorem toReal_root : toReal (AdjoinRoot.root f6) = Real.sqrt 3 := by
  rw [toReal, AdjoinRoot.lift_root]

theorem toZMod_iota_apply (x : Z3) : toZMod (iota x) = phiP x := by
  rw [iota_apply, phiP_apply, map_add, map_mul, map_intCast, map_intCast, toZMod_root]

theorem toReal_iota_apply (x : Z3) : toReal (iota x) = liftR x := by
  rw [iota_apply, liftR_apply, map_add, map_mul, map_intCast, map_intCast, toReal_root]

/-- The image of 1/6 in R6. -/
def inv6 : R6 := algebraMap L6 R6 (IsLocalization.Away.invSelf (6 : ℤ))

theorem toZModL_invSelf : toZModL (IsLocalization.Away.invSelf (6 : ℤ)) = 54601 := by
  have h := congrArg toZModL (IsLocalization.Away.mul_invSelf (S := L6) (6 : ℤ))
  rw [map_mul, map_one] at h
  have h1 : toZModL (algebraMap ℤ L6 6) = (Int.castRingHom (ZMod 65521)) 6 :=
    IsLocalization.Away.lift_eq (S := L6) (6 : ℤ) isUnit_six_mod 6
  rw [h1] at h
  have h6 : (Int.castRingHom (ZMod 65521)) 6 * 54601 = 1 := by decide +kernel
  linear_combination 54601 * h - toZModL (IsLocalization.Away.invSelf (6 : ℤ)) * h6

theorem toRealL_invSelf : toRealL (IsLocalization.Away.invSelf (6 : ℤ)) = 1 / 6 := by
  have h := congrArg toRealL (IsLocalization.Away.mul_invSelf (S := L6) (6 : ℤ))
  rw [map_mul, map_one] at h
  have h1 : toRealL (algebraMap ℤ L6 6) = (6 : ℝ) := by
    rw [toRealL, IsLocalization.Away.lift_eq (S := L6) (6 : ℤ) isUnit_six_real 6]
    norm_num
  rw [h1] at h
  linarith

/-- 72^-1 = 3 * 6^-3 in R6. -/
def inv72 : R6 := 3 * inv6 ^ 3

theorem toZMod_inv72 : toZMod inv72 = 64611 := by
  rw [inv72, map_mul, map_pow, map_ofNat, inv6, AdjoinRoot.algebraMap_eq, toZMod,
    AdjoinRoot.lift_of, toZModL_invSelf]
  decide +kernel

theorem toReal_inv72 : toReal inv72 = (72 : ℝ)⁻¹ := by
  rw [inv72, map_mul, map_pow, map_ofNat, inv6, AdjoinRoot.algebraMap_eq, toReal,
    AdjoinRoot.lift_of, toRealL_invSelf]
  norm_num

/-- J over the statement ring: 72^-1 . iota (72 J). -/
def JR : Matrix (Fin 20) (Fin 20) R6 := inv72 • JZ.map iota

theorem toZMod_det_JR : toZMod JR.det = 14151 := by
  have hc : toZMod (iota JZ.det) = phiP JZ.det := toZMod_iota_apply JZ.det
  rw [JR, Matrix.det_smul, Fintype.card_fin, map_mul, map_pow, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, hc, phiP_det_JZ, toZMod_inv72]
  decide +kernel

theorem det_JR_ne_zero : JR.det ≠ 0 := by
  intro h
  have h2 := toZMod_det_JR
  rw [h, map_zero] at h2
  exact absurd h2 (by decide +kernel)

theorem toReal_mapMatrix_JR : toReal.mapMatrix JR = JQ := by
  ext r n
  have hr : toReal (iota (JZ r n)) = liftR (JZ r n) := toReal_iota_apply (JZ r n)
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, JR, Matrix.smul_apply, smul_eq_mul,
    map_mul, toReal_inv72, hr, JQ, Matrix.of_apply, liftR_apply]
  ring

/-- Step 6 algebraic headline over the statement ring R6 = Z[1/6, theta]/(theta^2 - 3):
det JR is nonzero, reduces to 14151 modulo 65521 (theta -> 627), the real
specialization (theta -> sqrt3) of JR is JQ, and det JQ is nonzero. -/
theorem rank20_certificate :
    JR.det ≠ 0 ∧ toZMod JR.det = 14151 ∧ toReal.mapMatrix JR = JQ ∧ JQ.det ≠ 0 :=
  ⟨det_JR_ne_zero, toZMod_det_JR, toReal_mapMatrix_JR, det_JQ_ne_zero⟩

end
end Glennie.Compact.Rank20Certificate
