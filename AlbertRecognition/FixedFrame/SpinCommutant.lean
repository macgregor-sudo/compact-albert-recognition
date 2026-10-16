/- The native 16-dimensional spin scalar-commutant theorem.
The unknown operator is an arbitrary real-linear map. -/
module

public import AlbertRecognition.FixedFrame.OctonionCommutants

@[expose] public section

namespace AlbertRecognition.FixedFrame
noncomputable section

open Glennie

abbrev Spin := Octonion × Octonion

/-- Native orientation for the fixed-frame spin block. -/
def spinJ (a : Octonion) : Module.End ℝ Spin where
  toFun x := (-octMul x.2 (octConj a), octMul x.1 a)
  map_add' x y := by
    apply Prod.ext
    · change (-octRight (octConj a)) (x.2+y.2) =
        (-octRight (octConj a)) x.2 + (-octRight (octConj a)) y.2
      exact map_add (-octRight (octConj a)) x.2 y.2
    · exact octMul_add_left x.1 y.1 a
  map_smul' r x := by
    apply Prod.ext <;> simp [octMul_smul_left, smul_neg]

@[simp] theorem spinJ_apply (a : Octonion) (u v : Octonion) :
    spinJ a (u, v) = (-octMul v (octConj a), octMul u a) := rfl

@[simp] theorem spinJ_unit_apply (u v : Octonion) :
    spinJ (octScalar 1) (u, v) = (-v, u) := by simp

theorem spinJ_imag_apply (a : Octonion) (ha : octConj a = -a) (u v : Octonion) :
    spinJ a (u, v) = (octMul v a, octMul u a) := by
  apply Prod.ext
  · change -octMul v (octConj a) = octMul v a
    rw [ha]
    change -(octLeft v) (-a) = (octLeft v) a
    rw [map_neg, neg_neg]
  · rfl

def spinP (F : Module.End ℝ Spin) : Module.End ℝ Octonion :=
  (LinearMap.fst ℝ Octonion Octonion).comp
    (F.comp (LinearMap.inl ℝ Octonion Octonion))
def spinQ (F : Module.End ℝ Spin) : Module.End ℝ Octonion :=
  (LinearMap.fst ℝ Octonion Octonion).comp
    (F.comp (LinearMap.inr ℝ Octonion Octonion))
def spinR (F : Module.End ℝ Spin) : Module.End ℝ Octonion :=
  (LinearMap.snd ℝ Octonion Octonion).comp
    (F.comp (LinearMap.inl ℝ Octonion Octonion))
def spinS (F : Module.End ℝ Spin) : Module.End ℝ Octonion :=
  (LinearMap.snd ℝ Octonion Octonion).comp
    (F.comp (LinearMap.inr ℝ Octonion Octonion))

/-- Literal four-block reconstruction of any real-linear map. -/
theorem spin_four_blocks (F : Module.End ℝ Spin) (u v : Octonion) :
    F (u, v) = (spinP F u + spinQ F v, spinR F u + spinS F v) := by
  have hsplit : (u, v) = (u, 0) + (0, v) := by simp
  rw [hsplit, map_add]
  rfl

/-- Commuting with J_1 gives precisely [[P,Q],[-Q,P]]. -/
theorem spin_blocks_of_unit (F : Module.End ℝ Spin)
    (hF : F.comp (spinJ (octScalar 1)) = (spinJ (octScalar 1)).comp F)
    (u v : Octonion) :
    F (u, v) = (spinP F u + spinQ F v, -spinQ F u + spinP F v) := by
  have hR (x : Octonion) : spinR F x = -spinQ F x := by
    have h := congrArg Prod.fst (LinearMap.congr_fun hF (x, 0))
    change (F (spinJ (octScalar 1) (x, 0))).1 =
      (spinJ (octScalar 1) (F (x, 0))).1 at h
    have hh : spinQ F x = -spinR F x := by
      simpa [spinJ, spinP, spinQ, spinR, spinS] using h
    simpa using congrArg Neg.neg hh.symm
  have hS (x : Octonion) : spinS F x = spinP F x := by
    have h := congrArg Prod.snd (LinearMap.congr_fun hF (x, 0))
    change (F (spinJ (octScalar 1) (x, 0))).2 =
      (spinJ (octScalar 1) (F (x, 0))).2 at h
    simpa [spinJ, spinP, spinQ, spinR, spinS] using h
  rw [spin_four_blocks F u v, hR u, hS v]

/-- Eight actual native Clifford generators have scalar common commutant.
No self-adjointness, reference invariance or algebra structure is required of F. -/
theorem spin_commutant_scalar (F : Module.End ℝ Spin)
    (hF : ∀ t : Fin 8,
      F.comp (spinJ (octBasis t)) = (spinJ (octBasis t)).comp F) :
    ∃ b : ℝ, F = b • LinearMap.id := by
  have hunit : F.comp (spinJ (octScalar 1)) = (spinJ (octScalar 1)).comp F :=
    hF 0
  have hf := spin_blocks_of_unit F hunit
  have himag (t : Fin 8) (ht : t ≠ 0) (x : Octonion) :
      spinQ F (octMul x (octBasis t)) = -octMul (spinQ F x) (octBasis t) ∧
      spinP F (octMul x (octBasis t)) = octMul (spinP F x) (octBasis t) := by
    have h := LinearMap.congr_fun (hF t) (x, 0)
    change F (spinJ (octBasis t) (x, 0)) = spinJ (octBasis t) (F (x, 0)) at h
    rw [spinJ_imag_apply _ (octBasis_conj_imag t ht), hf, hf] at h
    simp only [octMul_zero_left, map_zero, zero_add, add_zero, neg_zero] at h
    rw [spinJ_imag_apply _ (octBasis_conj_imag t ht)] at h
    constructor
    · have hh := congrArg Prod.fst h
      change spinQ F (octMul x (octBasis t)) =
        octRight (octBasis t) (-spinQ F x) at hh
      rw [map_neg] at hh
      exact hh
    · exact congrArg Prod.snd h
  have hP : ∀ t : Fin 8, ∀ x : Octonion,
      spinP F (octMul x (octBasis t)) = octMul (spinP F x) (octBasis t) := by
    intro t x
    by_cases ht : t = 0
    · subst t
      simp
    · exact (himag t ht x).2
  have hQ : ∀ t : Fin 8, t ≠ 0 → ∀ x : Octonion,
      spinQ F (octMul x (octBasis t)) = -octMul (spinQ F x) (octBasis t) := by
    intro t ht x
    exact (himag t ht x).1
  obtain ⟨b, hb⟩ := oct_right_commutant_scalar (spinP F) hP
  have hq : spinQ F = 0 := oct_imaginary_right_anticommutant_zero (spinQ F) hQ
  refine ⟨b, ?_⟩
  apply LinearMap.ext
  rintro ⟨u, v⟩
  rw [hf u v, hb, hq]
  simp

end
end AlbertRecognition.FixedFrame
