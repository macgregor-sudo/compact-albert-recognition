/- Native coordinate proofs. No Jordan or octonion laws are assumed. -/
module

public import Glennie.Native
public import Mathlib.Tactic.Module

@[expose] public section

namespace Glennie
noncomputable section

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

theorem octMul_self_conj (x : Octonion) :
    octMul x (octConj x) = octScalar (octNormSq x) := by
  apply Prod.ext
  · simp [octMul, octConj, octScalar, octNormSq,
      Quaternion.self_mul_star, Quaternion.star_mul_self]
  · simp [octMul, octConj, octScalar]

theorem octMul_conj_self (x : Octonion) :
    octMul (octConj x) x = octScalar (octNormSq x) := by
  apply Prod.ext
  · simp [octMul, octConj, octScalar, octNormSq,
      Quaternion.self_mul_star, Quaternion.star_mul_self]
  · simp [octMul, octConj, octScalar]

theorem octScalar_smul (r s : ℝ) : r • octScalar s = octScalar (r*s) := by
  apply Prod.ext <;> apply Quaternion.ext <;> simp [octScalar, smul_eq_mul]

/-- Conjugate-over-positive-norm inverse in the native division octonions. -/
def octInv (x : Octonion) : Octonion := (octNormSq x)⁻¹ • octConj x

theorem octMul_inv (x : Octonion) (hx : x ≠ 0) :
    octMul x (octInv x) = octScalar 1 := by
  have hn : octNormSq x ≠ 0 := fun h => hx ((octNormSq_eq_zero x).mp h)
  rw [octInv, octMul_smul_right, octMul_self_conj, octScalar_smul, inv_mul_cancel₀ hn]

theorem octInv_mul (x : Octonion) (hx : x ≠ 0) :
    octMul (octInv x) x = octScalar 1 := by
  have hn : octNormSq x ≠ 0 := fun h => hx ((octNormSq_eq_zero x).mp h)
  rw [octInv, octMul_smul_left, octMul_conj_self, octScalar_smul, inv_mul_cancel₀ hn]

set_option maxHeartbeats 2000000 in
theorem octNormSq_mul (x y : Octonion) :
    octNormSq (octMul x y) = octNormSq x * octNormSq y := by
  simp [octNormSq, octMul, Quaternion.normSq_def', Quaternion.re_mul,
    Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
  ring

set_option maxHeartbeats 2000000 in
theorem octMul_left_alternative (x y : Octonion) :
    octMul x (octMul x y) = octMul (octMul x x) y := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [octMul, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

set_option maxHeartbeats 2000000 in
theorem octMul_right_alternative (x y : Octonion) :
    octMul (octMul x y) y = octMul x (octMul y y) := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [octMul, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

set_option maxHeartbeats 8000000 in
theorem octMul_moufang (x y z : Octonion) :
    octMul (octMul x y) (octMul z x) = octMul (octMul x (octMul y z)) x := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [octMul, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

theorem octRe_associative (x y z : Octonion) :
    octRe (octMul (octMul x y) z) = octRe (octMul x (octMul y z)) := by
  simp [octRe, octMul, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul]
  ring

theorem octDot_add_left (x y z : Octonion) :
    octDot (x+y) z = octDot x z+octDot y z := by
  simp [octDot_coordinates]
  ring

theorem octDot_smul_left (r : ℝ) (x y : Octonion) :
    octDot (r • x) y = r*octDot x y := by
  simp [octDot_coordinates, smul_eq_mul]
  ring

theorem jordan_add_left (x y z : Albert) : jordan (x+y) z = jordan x z + jordan y z := by
  apply Albert.ext
  all_goals simp only [Albert.add_d0, Albert.add_d1, Albert.add_d2,
    Albert.add_o01, Albert.add_o02, Albert.add_o12,
    jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
    octDot_add_left, octConj_add, octMul_add_left, octMul_add_right]
  case d0 => ring
  case d1 => ring
  case d2 => ring
  all_goals module

theorem jordan_add_right (x y z : Albert) : jordan x (y+z) = jordan x y + jordan x z := by
  rw [jordan_comm, jordan_add_left, jordan_comm y x, jordan_comm z x]

theorem jordan_smul_left (r : ℝ) (x y : Albert) :
    jordan (r • x) y = r • jordan x y := by
  apply Albert.ext
  all_goals simp only [Albert.smul_d0, Albert.smul_d1, Albert.smul_d2,
    Albert.smul_o01, Albert.smul_o02, Albert.smul_o12,
    jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
    octDot_smul_left, octConj_smul, octMul_smul_left, octMul_smul_right]
  case d0 => ring
  case d1 => ring
  case d2 => ring
  all_goals module

theorem jordan_smul_right (r : ℝ) (x y : Albert) :
    jordan x (r • y) = r • jordan x y := by
  rw [jordan_comm, jordan_smul_left, jordan_comm]

@[simp] theorem jordan_neg_left (x y : Albert) : jordan (-x) y = -jordan x y := by
  simpa using jordan_smul_left (-1 : ℝ) x y

@[simp] theorem jordan_neg_right (x y : Albert) : jordan x (-y) = -jordan x y := by
  simpa using jordan_smul_right (-1 : ℝ) x y

theorem jordan_sub_left (x y z : Albert) : jordan (x-y) z = jordan x z-jordan y z := by
  simp [sub_eq_add_neg, jordan_add_left]

theorem jordan_sub_right (x y z : Albert) : jordan x (y-z) = jordan x y-jordan x z := by
  simp [sub_eq_add_neg, jordan_add_right]

@[simp] theorem jordan_unit_left (x : Albert) : jordan 1 x = x := by
  apply Albert.ext
  all_goals norm_num [jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02,
    jordan_o12, unit, octDot_coordinates, octMul, octConj, Quaternion.re_mul,
    Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, smul_eq_mul,
    Prod.mk_zero_zero, smul_smul]

@[simp] theorem jordan_unit_right (x : Albert) : jordan x 1 = x := by
  rw [jordan_comm, jordan_unit_left]

@[simp] theorem jordan_zero_left (x : Albert) : jordan 0 x = 0 := by
  simpa using jordan_smul_left (0 : ℝ) x x

@[simp] theorem jordan_zero_right (x : Albert) : jordan x 0 = 0 := by
  rw [jordan_comm, jordan_zero_left]

theorem inner_add_left (x y z : Albert) : inner (x+y) z = inner x z+inner y z := by
  simp [inner_coordinates, octDot_coordinates]
  ring

theorem inner_add_right (x y z : Albert) : inner x (y+z) = inner x y+inner x z := by
  rw [inner_comm, inner_add_left, inner_comm x y, inner_comm x z]

theorem inner_smul_left (r : ℝ) (x y : Albert) : inner (r • x) y = r * inner x y := by
  simp [inner_coordinates, octDot_coordinates, smul_eq_mul]
  ring

theorem inner_smul_right (r : ℝ) (x y : Albert) : inner x (r • y) = r * inner x y := by
  rw [inner_comm, inner_smul_left, inner_comm x y]

@[simp] theorem inner_neg_left (x y : Albert) : inner (-x) y = -inner x y := by
  simpa using inner_smul_left (-1 : ℝ) x y

@[simp] theorem inner_neg_right (x y : Albert) : inner x (-y) = -inner x y := by
  simpa using inner_smul_right (-1 : ℝ) x y

theorem inner_sub_left (x y z : Albert) : inner (x-y) z = inner x z-inner y z := by
  simp [sub_eq_add_neg, inner_add_left]

theorem inner_sub_right (x y z : Albert) : inner x (y-z) = inner x y-inner x z := by
  simp [sub_eq_add_neg, inner_add_right]

set_option maxHeartbeats 2000000 in
theorem inner_jordan_associative (x y z : Albert) :
    inner (jordan x y) z = inner x (jordan y z) := by
  simp [inner_coordinates, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12, octDot_coordinates,
    octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul, smul_eq_mul]
  ring

end
end Glennie
