/- Native reference action and assembly of the fixed-frame identities. -/
module

public import AlbertRecognition.FixedFrame.CyclicFrameData

@[expose] public section
namespace AlbertRecognition.FixedFrame
noncomputable section
open Glennie

/-- The actual projected reference multiplication on each diagonal frame. -/
theorem KA_h_self (i : Fin 3) : KA (h i) (h i) = (-1 : ℝ) • h i := by
  have hnorm : octNormSq (0 : Octonion) = 0 := (octNormSq_eq_zero 0).mpr rfl
  fin_cases i <;> apply Subtype.ext <;> apply Albert.ext <;>
    norm_num [KA_apply, project_coe, traceless, trace, h, e, unit,
      jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octMul, octConj, hnorm]

/-- Two distinct actual frame vectors have projected product h_i+h_j. -/
theorem KA_h_cross (i j : Fin 3) (hij : i ≠ j) :
    KA (h i) (h j) = h i + h j := by
  have hnorm : octNormSq (0 : Octonion) = 0 := (octNormSq_eq_zero 0).mpr rfl
  fin_cases i <;> fin_cases j
  all_goals first | exact False.elim (hij rfl) | skip
  all_goals apply Subtype.ext
  all_goals apply Albert.ext <;>
    norm_num [KA_apply, project_coe, traceless, trace, h, e, unit,
      jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octMul, octConj, hnorm]

/-- Raw native slot eigenvalues; the adjacent slots have coefficient -1/2. -/
theorem KA_h_X01 (i : Fin 3) (u : Octonion) :
    KA (h i) (X01 u) = (if i = 2 then (1 : ℝ) else -(1/2 : ℝ)) • X01 u := by
  have hnorm : octNormSq (0 : Octonion) = 0 := (octNormSq_eq_zero 0).mpr rfl
  have hneg (x : Albert) : -x =
      ⟨-x.d0,-x.d1,-x.d2,-x.o01,-x.o02,-x.o12⟩ := rfl
  have hconj : octConj (0 : Octonion) = 0 := by simp [octConj]
  fin_cases i <;> apply Subtype.ext <;> apply Albert.ext <;>
    simp [KA_apply, project_coe, traceless, trace, h, e, unit, X01,
      jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octMul_zero_left, octMul_zero_right, hconj,
      hnorm, hneg, smul_smul] <;>
    solve
    | norm_num
    | module
    | (apply Prod.ext <;> apply Quaternion.ext <;>
        norm_num [smul_eq_mul] <;> ring)

theorem KA_h_X02 (i : Fin 3) (u : Octonion) :
    KA (h i) (X02 u) = (if i = 1 then (1 : ℝ) else -(1/2 : ℝ)) • X02 u := by
  have hnorm : octNormSq (0 : Octonion) = 0 := (octNormSq_eq_zero 0).mpr rfl
  have hneg (x : Albert) : -x =
      ⟨-x.d0,-x.d1,-x.d2,-x.o01,-x.o02,-x.o12⟩ := rfl
  have hconj : octConj (0 : Octonion) = 0 := by simp [octConj]
  fin_cases i <;> apply Subtype.ext <;> apply Albert.ext <;>
    simp [KA_apply, project_coe, traceless, trace, h, e, unit, X02,
      jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octMul_zero_left, octMul_zero_right, hconj,
      hnorm, hneg, smul_smul] <;>
    solve
    | norm_num
    | module
    | (apply Prod.ext <;> apply Quaternion.ext <;>
        norm_num [smul_eq_mul] <;> ring)

theorem KA_h_X12 (i : Fin 3) (u : Octonion) :
    KA (h i) (X12 u) = (if i = 0 then (1 : ℝ) else -(1/2 : ℝ)) • X12 u := by
  have hnorm : octNormSq (0 : Octonion) = 0 := (octNormSq_eq_zero 0).mpr rfl
  have hneg (x : Albert) : -x =
      ⟨-x.d0,-x.d1,-x.d2,-x.o01,-x.o02,-x.o12⟩ := rfl
  have hconj : octConj (0 : Octonion) = 0 := by simp [octConj]
  fin_cases i <;> apply Subtype.ext <;> apply Albert.ext <;>
    simp [KA_apply, project_coe, traceless, trace, h, e, unit, X12,
      jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octMul_zero_left, octMul_zero_right, hconj,
      hnorm, hneg, smul_smul] <;>
    solve
    | norm_num
    | module
    | (apply Prod.ext <;> apply Quaternion.ext <;>
        norm_num [smul_eq_mul] <;> ring)

/-- Literal native diagonal spanning identity, with rational coefficients. -/
theorem frameD_eq_h01 :
    frameD = (-1/3 : ℝ) • h 0 + (-2/3 : ℝ) • h 1 := by
  have hneg (x : Albert) : -x =
      ⟨-x.d0,-x.d1,-x.d2,-x.o01,-x.o02,-x.o12⟩ := rfl
  apply Subtype.ext
  apply Albert.ext <;> norm_num [frameD, h, e, unit, hneg]

private theorem half_ratio_smul (b : ℝ) (x : V) :
    (-b/2) • x = b • (-(1/2 : ℝ) • x) := by
  rw [smul_smul]
  congr 1
  ring

/-- Conditional assembly from the explicitly intermediate three-frame data.
The final theorem below constructs these data from the sole Jacobi hypothesis. -/
theorem ThreeFrameScalarData.operator_eq_reference {B : SymmetricCubic}
    (data : ThreeFrameScalarData B) :
    ∃ b : ℝ, ∀ i : Fin 3, KB B (h i) = b • KA (h i) := by
  obtain ⟨b,ha,hb,hc⟩ := data.common_coefficients
  have hdiag (i j : Fin 3) : KB B (h i) (h j) = b • KA (h i) (h j) := by
    by_cases hij : i = j
    · subst j
      rw [data.on_h_self i, ha i, KA_h_self]
      simp only [smul_smul]
      congr 1
      ring
    · rw [data.cross_h i j hij, hb i, ha i, KA_h_cross i j hij, smul_add]
      have hr : (b - -b)/2 = b := by ring
      rw [hr]
      exact add_comm _ _
  have hd (i : Fin 3) : KB B (h i) frameD = b • KA (h i) frameD := by
    rw [frameD_eq_h01]
    simp only [map_add, map_smul, hdiag, smul_add, smul_smul]
    module
  have h01 (i : Fin 3) (u : Octonion) :
      KB B (h i) (X01 u) = b • KA (h i) (X01 u) := by
    obtain ⟨h0,h1,h2⟩ := data.on_X01 u
    fin_cases i
    · change KB B (h 0) (X01 u) = b • KA (h 0) (X01 u)
      rw [h0, hc 0, KA_h_X01,
        if_neg (by decide : (0 : Fin 3) ≠ 2)]
      exact half_ratio_smul b _
    · change KB B (h 1) (X01 u) = b • KA (h 1) (X01 u)
      rw [h1, hc 1, KA_h_X01,
        if_neg (by decide : (1 : Fin 3) ≠ 2)]
      exact half_ratio_smul b _
    · change KB B (h 2) (X01 u) = b • KA (h 2) (X01 u)
      rw [h2, hb 2, KA_h_X01, if_pos rfl, one_smul]
  have h02 (i : Fin 3) (u : Octonion) :
      KB B (h i) (X02 u) = b • KA (h i) (X02 u) := by
    obtain ⟨h0,h1,h2⟩ := data.on_X02 u
    fin_cases i
    · change KB B (h 0) (X02 u) = b • KA (h 0) (X02 u)
      rw [h0, hc 0, KA_h_X02,
        if_neg (by decide : (0 : Fin 3) ≠ 1)]
      exact half_ratio_smul b _
    · change KB B (h 1) (X02 u) = b • KA (h 1) (X02 u)
      rw [h1, hb 1, KA_h_X02, if_pos rfl, one_smul]
    · change KB B (h 2) (X02 u) = b • KA (h 2) (X02 u)
      rw [h2, hc 2, KA_h_X02,
        if_neg (by decide : (2 : Fin 3) ≠ 1)]
      exact half_ratio_smul b _
  have h12 (i : Fin 3) (u : Octonion) :
      KB B (h i) (X12 u) = b • KA (h i) (X12 u) := by
    obtain ⟨h0,h1,h2⟩ := data.on_X12 u
    fin_cases i
    · change KB B (h 0) (X12 u) = b • KA (h 0) (X12 u)
      rw [h0, hb 0, KA_h_X12, if_pos rfl, one_smul]
    · change KB B (h 1) (X12 u) = b • KA (h 1) (X12 u)
      rw [h1, hc 1, KA_h_X12,
        if_neg (by decide : (1 : Fin 3) ≠ 0)]
      exact half_ratio_smul b _
    · change KB B (h 2) (X12 u) = b • KA (h 2) (X12 u)
      rw [h2, hc 2, KA_h_X12,
        if_neg (by decide : (2 : Fin 3) ≠ 0)]
      exact half_ratio_smul b _
  refine ⟨b, ?_⟩
  intro i
  apply LinearMap.ext
  intro x
  change KB B (h i) x = b • KA (h i) x
  rcases hs : (frameCoordinates x).2.2.2 with ⟨u,v⟩
  rw [frame_decompose x, hs, frameSpin_apply]
  simp only [map_add, map_smul, hdiag, hd, h01, h02, h12, smul_add, smul_smul]
  module

/-- The unchanged initial fixed-frame gate for an arbitrary genuine symmetric
trilinear form. There is no unknown invariance, Jordan or common-scalar premise. -/
theorem fixedFrame_gate_of_A_q_zero (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) :
    ∃ b : ℝ, ∀ i : Fin 3, KB B (h i) = b • KA (h i) := by
  obtain ⟨data⟩ := threeFrameScalarData_of_A_q_zero B hB
  exact data.operator_eq_reference

end
end AlbertRecognition.FixedFrame
