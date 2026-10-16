/- Actual related-triple transport to native compact Albert automorphisms.
This file does not assume or prove universal existence of a related triple.
-/
module

public import Glennie.Native.AlgebraLaws
public import Glennie.Obligations
public import Mathlib.Data.Real.Sqrt

@[expose] public section

namespace Glennie
noncomputable section

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

theorem octNormSq_add (x y : Octonion) :
    octNormSq (x+y) = octNormSq x+octNormSq y+2*octDot x y := by
  simp [octNormSq, Quaternion.normSq_def', octDot_coordinates]
  ring

theorem octDot_sub_left (x y z : Octonion) :
    octDot (x-y) z = octDot x z-octDot y z := by
  simp [octDot_coordinates]
  ring

theorem octDot_mul_right (x y z : Octonion) :
    octDot (octMul x y) z = octDot x (octMul z (octConj y)) := by
  simp [octDot_coordinates, octMul, octConj, Quaternion.re_mul,
    Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
  ring

theorem octDot_mul_left (x y z : Octonion) :
    octDot (octMul x y) z = octDot y (octMul (octConj x) z) := by
  simp [octDot_coordinates, octMul, octConj, Quaternion.re_mul,
    Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
  ring

theorem octDot_ext (x y : Octonion) (h : ∀ z, octDot x z = octDot y z) : x = y := by
  have hz : octNormSq (x-y) = 0 := by
    rw [← octDot_self, octDot_sub_left, h (x-y), sub_self]
  exact sub_eq_zero.mp ((octNormSq_eq_zero (x-y)).mp hz)

@[simp] theorem octNormSq_conj (x : Octonion) : octNormSq (octConj x) = octNormSq x := by
  simp [octNormSq, octConj, Quaternion.normSq_def']

theorem octNormSq_smul (r : ℝ) (x : Octonion) :
    octNormSq (r • x) = r^2 * octNormSq x := by
  simp [octNormSq, Quaternion.normSq_def', smul_eq_mul]
  ring

theorem octMul_self_eq (x : Octonion) :
    octMul x x = (2*octRe x) • x - octScalar (octNormSq x) := by
  have h := congrArg (octMul x) (octAdd_conj x)
  rw [octMul_add_right, octMul_self_conj, octMul_smul_right,
    octMul_scalar_right, smul_smul] at h
  exact eq_sub_iff_add_eq.mpr h

theorem octMul_pure_unit_self (x : Octonion) (hre : octRe x = 0)
    (hn : octNormSq x = 1) : octMul x x = octScalar (-1) := by
  rw [octMul_self_eq, hre, hn]
  simp [octScalar]

/-- Every nonzero native octonion is a positive real multiple of a unit. -/
theorem octUnit_decomposition (x : Octonion) (hx : x ≠ 0) :
    ∃ a : Octonion, ∃ r : ℝ, 0 < r ∧ octNormSq a = 1 ∧ x = r • a := by
  have hn : 0 < octNormSq x := lt_of_le_of_ne (octNormSq_nonneg x)
    (Ne.symm (fun h => hx ((octNormSq_eq_zero x).mp h)))
  let r := Real.sqrt (octNormSq x)
  have hr : 0 < r := Real.sqrt_pos.2 hn
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hrsq : r^2 = octNormSq x := Real.sq_sqrt hn.le
  refine ⟨r⁻¹ • x, r, hr, ?_, ?_⟩
  · rw [octNormSq_smul, ← hrsq]
    field_simp
  · simp [smul_smul, hr0]

/-- The inverse property is proved for the declared native multiplication. -/
theorem octMul_conj_left_cancel (a x : Octonion) :
    octMul (octConj a) (octMul a x) = octNormSq a • x := by
  ext <;> simp [octMul, octConj, octNormSq, Quaternion.normSq_def',
    Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul, smul_eq_mul] <;> ring

theorem octMul_left_conj_cancel (a x : Octonion) :
    octMul a (octMul (octConj a) x) = octNormSq a • x := by
  simpa only [octConj_conj, octNormSq_conj] using
    octMul_conj_left_cancel (octConj a) x

theorem octMul_conj_right_cancel (a x : Octonion) :
    octMul (octMul x a) (octConj a) = octNormSq a • x := by
  ext <;> simp [octMul, octConj, octNormSq, Quaternion.normSq_def',
    Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul, smul_eq_mul] <;> ring

theorem octMul_right_conj_cancel (a x : Octonion) :
    octMul (octMul x (octConj a)) a = octNormSq a • x := by
  simpa only [octConj_conj, octNormSq_conj] using
    octMul_conj_right_cancel (octConj a) x

def octLeftUnitEquiv (a : Octonion) (ha : octNormSq a = 1) :
    Octonion ≃ₗ[ℝ] Octonion where
  toFun := octMul a
  invFun := octMul (octConj a)
  left_inv x := by simp [octMul_conj_left_cancel, ha]
  right_inv x := by simp [octMul_left_conj_cancel, ha]
  map_add' := octMul_add_right a
  map_smul' := fun r x => octMul_smul_right r a x

def octRightUnitEquiv (a : Octonion) (ha : octNormSq a = 1) :
    Octonion ≃ₗ[ℝ] Octonion where
  toFun x := octMul x a
  invFun x := octMul x (octConj a)
  left_inv x := by simp [octMul_conj_right_cancel, ha]
  right_inv x := by simp [octMul_right_conj_cancel, ha]
  map_add' := fun x y => octMul_add_left x y a
  map_smul' := fun r x => octMul_smul_left r x a

def octConjEquiv : Octonion ≃ₗ[ℝ] Octonion where
  toFun := octConj
  invFun := octConj
  left_inv := octConj_conj
  right_inv := octConj_conj
  map_add' := octConj_add
  map_smul' := octConj_smul

theorem octMul_flexible (a x : Octonion) :
    octMul (octMul a x) a = octMul a (octMul x a) := by
  simpa using (octMul_moufang a (octScalar 1) x).symm

/-- A genuine norm-preserving related triple; its existence is a separate obligation. -/
structure OctRelatedTriple where
  A : Octonion ≃ₗ[ℝ] Octonion
  B : Octonion ≃ₗ[ℝ] Octonion
  C : Octonion ≃ₗ[ℝ] Octonion
  norm_A : ∀ x, octNormSq (A x) = octNormSq x
  norm_B : ∀ x, octNormSq (B x) = octNormSq x
  norm_C : ∀ x, octNormSq (C x) = octNormSq x
  product : ∀ x y, octMul (A x) (B y) = C (octMul x y)

/-- An explicit genuine related triple, obtained from the native middle Moufang law. -/
def octMiddleTriple (a : Octonion) (ha : octNormSq a = 1) : OctRelatedTriple where
  A := octLeftUnitEquiv a ha
  B := octRightUnitEquiv a ha
  C := (octLeftUnitEquiv a ha).trans (octRightUnitEquiv a ha)
  norm_A x := by change octNormSq (octMul a x) = _; rw [octNormSq_mul, ha, one_mul]
  norm_B x := by change octNormSq (octMul x a) = _; rw [octNormSq_mul, ha, mul_one]
  norm_C x := by
    change octNormSq (octMul (octMul a x) a) = _
    rw [octNormSq_mul, octNormSq_mul, ha, one_mul, mul_one]
  product := octMul_moufang a

theorem octDot_of_norm_preserving (A : Octonion ≃ₗ[ℝ] Octonion)
    (hA : ∀ x, octNormSq (A x) = octNormSq x) (x y : Octonion) :
    octDot (A x) (A y) = octDot x y := by
  have h := hA (x+y)
  rw [map_add, octNormSq_add, octNormSq_add, hA, hA] at h
  linarith

namespace OctRelatedTriple

@[simp] theorem middle_A (a : Octonion) (ha : octNormSq a = 1) (x : Octonion) :
    (octMiddleTriple a ha).A x = octMul a x := rfl

@[simp] theorem middle_B (a : Octonion) (ha : octNormSq a = 1) (x : Octonion) :
    (octMiddleTriple a ha).B x = octMul x a := rfl

@[simp] theorem middle_C (a : Octonion) (ha : octNormSq a = 1) (x : Octonion) :
    (octMiddleTriple a ha).C x = octMul (octMul a x) a := rfl

theorem dot_A (g : OctRelatedTriple) (x y : Octonion) :
    octDot (g.A x) (g.A y) = octDot x y := octDot_of_norm_preserving g.A g.norm_A x y

theorem dot_B (g : OctRelatedTriple) (x y : Octonion) :
    octDot (g.B x) (g.B y) = octDot x y := octDot_of_norm_preserving g.B g.norm_B x y

theorem dot_C (g : OctRelatedTriple) (x y : Octonion) :
    octDot (g.C x) (g.C y) = octDot x y := octDot_of_norm_preserving g.C g.norm_C x y

theorem cross01 (g : OctRelatedTriple) (v w : Octonion) :
    octMul (g.C v) (octConj (g.B w)) = g.A (octMul v (octConj w)) := by
  apply octDot_ext
  intro t
  obtain ⟨u, rfl⟩ := g.A.surjective t
  rw [octDot_mul_right, octConj_conj, g.product, g.dot_C, g.dot_A,
    octDot_mul_right, octConj_conj]

theorem cross12 (g : OctRelatedTriple) (u v : Octonion) :
    octMul (octConj (g.A u)) (g.C v) = g.B (octMul (octConj u) v) := by
  apply octDot_ext
  intro t
  obtain ⟨w, rfl⟩ := g.B.surjective t
  rw [octDot_mul_left, octConj_conj, octDot_comm (g.C v), g.product,
    g.dot_C, g.dot_B, octDot_mul_left]
  exact octDot_comm _ _

/-- Composition means first h, then g in each slot. -/
def comp (g h : OctRelatedTriple) : OctRelatedTriple where
  A := h.A.trans g.A
  B := h.B.trans g.B
  C := h.C.trans g.C
  norm_A x := (g.norm_A (h.A x)).trans (h.norm_A x)
  norm_B x := (g.norm_B (h.B x)).trans (h.norm_B x)
  norm_C x := (g.norm_C (h.C x)).trans (h.norm_C x)
  product x y := by
    change octMul (g.A (h.A x)) (g.B (h.B y)) = g.C (h.C (octMul x y))
    rw [g.product, h.product]

/-- A proved triality reflection, using native Frobenius nondegeneracy. -/
def swap12 (g : OctRelatedTriple) : OctRelatedTriple where
  A := octConjEquiv.trans (g.A.trans octConjEquiv)
  B := g.C
  C := g.B
  norm_A x := by
    change octNormSq (octConj (g.A (octConj x))) = octNormSq x
    rw [octNormSq_conj, g.norm_A, octNormSq_conj]
  norm_B := g.norm_C
  norm_C := g.norm_B
  product x y := by
    change octMul (octConj (g.A (octConj x))) (g.C y) = g.B (octMul x y)
    simpa only [octConj_conj] using g.cross12 (octConj x) y

/-- A fully constructed related triple fixing the first unit.
Its second and third maps are x ↦ a ((x a) a), without an associativity assumption. -/
def unitStabilizerTriple (a : Octonion) (ha : octNormSq a = 1) : OctRelatedTriple :=
  (octMiddleTriple a ha).comp (octMiddleTriple a ha).swap12

theorem unitStabilizer_A (a : Octonion) (ha : octNormSq a = 1) (x : Octonion) :
    (unitStabilizerTriple a ha).A x = octMul a (octMul x (octConj a)) := by
  change octMul a (octConj (octMul a (octConj x))) = _
  rw [octConj_mul, octConj_conj]

theorem unitStabilizer_B (a : Octonion) (ha : octNormSq a = 1) (x : Octonion) :
    (unitStabilizerTriple a ha).B x = octMul a (octMul (octMul x a) a) := by
  change octMul (octMul (octMul a x) a) a = _
  rw [octMul_flexible, octMul_flexible]

theorem unitStabilizer_C (a : Octonion) (ha : octNormSq a = 1) (x : Octonion) :
    (unitStabilizerTriple a ha).C x = octMul a (octMul (octMul x a) a) := by
  change octMul (octMul a (octMul x a)) a = _
  rw [octMul_flexible]

theorem unitStabilizer_fix_unit (a : Octonion) (ha : octNormSq a = 1) :
    (unitStabilizerTriple a ha).A (octScalar 1) = octScalar 1 := by
  rw [unitStabilizer_A, octMul_scalar_left, one_smul, octMul_self_conj, ha]

/-- Order-three units give a genuine octonion automorphism in all three slots. -/
theorem unitStabilizer_B_eq_A (a : Octonion) (ha : octNormSq a = 1)
    (hsq : octMul a a = octConj a) (x : Octonion) :
    (unitStabilizerTriple a ha).B x = (unitStabilizerTriple a ha).A x := by
  rw [unitStabilizer_B, unitStabilizer_A, octMul_right_alternative, hsq]

theorem unitStabilizer_C_eq_A (a : Octonion) (ha : octNormSq a = 1)
    (hsq : octMul a a = octConj a) (x : Octonion) :
    (unitStabilizerTriple a ha).C x = (unitStabilizerTriple a ha).A x := by
  rw [unitStabilizer_C, unitStabilizer_A, octMul_right_alternative, hsq]

/-- Fixed diagonal and upper-slot action (01,02,12) ↦ (A,C,B). -/
def albertEquiv (g : OctRelatedTriple) : Albert ≃ₗ[ℝ] Albert where
  toFun x := ⟨x.d0,x.d1,x.d2,g.A x.o01,g.C x.o02,g.B x.o12⟩
  invFun x := ⟨x.d0,x.d1,x.d2,g.A.symm x.o01,g.C.symm x.o02,g.B.symm x.o12⟩
  left_inv x := by apply Albert.ext <;> simp
  right_inv x := by apply Albert.ext <;> simp
  map_add' x y := by apply Albert.ext <;> simp
  map_smul' r x := by apply Albert.ext <;> simp

theorem albertEquiv_jordan (g : OctRelatedTriple) (x y : Albert) :
    g.albertEquiv (jordan x y) = jordan (g.albertEquiv x) (g.albertEquiv y) := by
  apply Albert.ext
  all_goals simp [albertEquiv, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12, g.dot_A, g.dot_B, g.dot_C,
    g.cross01, g.cross12, g.product, map_add, map_smul]

/-- Actual native product- and trace-preserving automorphism from a related triple. -/
def compactAutomorphism (g : OctRelatedTriple) : CompactAutomorphism where
  equiv := g.albertEquiv
  map_jordan := g.albertEquiv_jordan
  map_trace _ := rfl

/-- An explicit automorphism fixes the diagonal and makes any nonzero 12 slot real. -/
theorem make_slot12_real (x : Albert) (hx : x.o12 ≠ 0) :
    ∃ g : CompactAutomorphism, ∃ r : ℝ, 0 < r ∧
      (g.equiv x).d0 = x.d0 ∧ (g.equiv x).d1 = x.d1 ∧
      (g.equiv x).d2 = x.d2 ∧ (g.equiv x).o12 = octScalar r := by
  obtain ⟨a, r, hr, ha, hw⟩ := octUnit_decomposition x.o12 hx
  refine ⟨(octMiddleTriple (octConj a) (by simpa using ha)).compactAutomorphism,
    r, hr, rfl, rfl, rfl, ?_⟩
  change octMul x.o12 (octConj a) = octScalar r
  rw [hw, octMul_smul_left, octMul_self_conj, ha]
  simpa [octScalar_smul]

end OctRelatedTriple
end
end Glennie
