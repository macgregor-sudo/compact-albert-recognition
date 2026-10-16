/- Actual three-frame coarse data from the unrestricted Jacobi kernel.
Both cyclic steps use pullbacks of the arbitrary cubic, never its invariance. -/
module

public import AlbertRecognition.FixedFrame.CyclicPullback
public import AlbertRecognition.FixedFrame.ScalarBlockConsequences
public import AlbertRecognition.FixedFrame.ThreeFrameRelations

@[expose] public section
namespace AlbertRecognition.FixedFrame
noncomputable section
open Glennie

/-- The first actual cyclic pullback derives all h1 coarse actions. -/
theorem h1_coarse_actions_of_A_q_zero (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) :
    ∃ a b c : ℝ, KB B (h 1) (h 1) = a • h 1 ∧
      (∀ j : Fin 3, j ≠ 1 →
        KB B (h 1) (h j + (1/2 : ℝ) • h 1) =
          b • (h j + (1/2 : ℝ) • h 1)) ∧
      (∀ u : Octonion, KB B (h 1) (X01 u) = c • X01 u) ∧
      (∀ u : Octonion, KB B (h 1) (X02 u) = b • X02 u) ∧
      (∀ u : Octonion, KB B (h 1) (X12 u) = c • X12 u) := by
  let BT := pullbackCubic cyclicV B
  have hBT : A (q referenceCubic) BT = 0 :=
    A_q_pullback_zero cyclicAutomorphism B hB
  obtain ⟨a,b,c,ha,hd,h01,h02,h12⟩ := h0_coarse_actions_of_A_q_zero BT hBT
  have transfer (x y : V) (r : ℝ) (hh : KB BT x y = r • y) :
      KB B (cyclicV x) (cyclicV y) = r • cyclicV y :=
    scalar_action_of_pullback cyclicAutomorphism B x y r hh
  refine ⟨a,b,c,?_,?_,?_,?_,?_⟩
  · simpa only [cyclicV_h0] using transfer (h 0) (h 0) a ha
  · intro j hj
    fin_cases j
    · change KB B (h 1) (h 0 + (1/2 : ℝ) • h 1) =
        b • (h 0 + (1/2 : ℝ) • h 1)
      simpa only [map_add, map_smul, cyclicV_h0, cyclicV_h2] using
        transfer (h 0) (h 2 + (1/2 : ℝ) • h 0) b (hd 2 (by decide))
    · exact False.elim (hj rfl)
    · change KB B (h 1) (h 2 + (1/2 : ℝ) • h 1) =
        b • (h 2 + (1/2 : ℝ) • h 1)
      simpa only [map_add, map_smul, cyclicV_h0, cyclicV_h1] using
        transfer (h 0) (h 1 + (1/2 : ℝ) • h 0) b (hd 1 (by decide))
  · intro u
    simpa only [cyclicV_h0, cyclicV_X02, octConj_conj] using
      transfer (h 0) (X02 (octConj u)) c (h02 (octConj u))
  · intro u
    simpa only [cyclicV_h0, cyclicV_X12, octConj_conj] using
      transfer (h 0) (X12 (octConj u)) b (h12 (octConj u))
  · intro u
    simpa only [cyclicV_h0, cyclicV_X01] using
      transfer (h 0) (X01 u) c (h01 u)

/-- Apply the actual cyclic pullback again to derive all h2 coarse actions.
The preceding h1 theorem applied to BT performs the literal T² pullback. -/
theorem h2_coarse_actions_of_A_q_zero (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) :
    ∃ a b c : ℝ, KB B (h 2) (h 2) = a • h 2 ∧
      (∀ j : Fin 3, j ≠ 2 →
        KB B (h 2) (h j + (1/2 : ℝ) • h 2) =
          b • (h j + (1/2 : ℝ) • h 2)) ∧
      (∀ u : Octonion, KB B (h 2) (X01 u) = b • X01 u) ∧
      (∀ u : Octonion, KB B (h 2) (X02 u) = c • X02 u) ∧
      (∀ u : Octonion, KB B (h 2) (X12 u) = c • X12 u) := by
  let BT := pullbackCubic cyclicV B
  have hBT : A (q referenceCubic) BT = 0 :=
    A_q_pullback_zero cyclicAutomorphism B hB
  obtain ⟨a,b,c,ha,hd,h01,h02,h12⟩ := h1_coarse_actions_of_A_q_zero BT hBT
  have transfer (x y : V) (r : ℝ) (hh : KB BT x y = r • y) :
      KB B (cyclicV x) (cyclicV y) = r • cyclicV y :=
    scalar_action_of_pullback cyclicAutomorphism B x y r hh
  refine ⟨a,b,c,?_,?_,?_,?_,?_⟩
  · simpa only [cyclicV_h1] using transfer (h 1) (h 1) a ha
  · intro j hj
    fin_cases j
    · change KB B (h 2) (h 0 + (1/2 : ℝ) • h 2) =
        b • (h 0 + (1/2 : ℝ) • h 2)
      simpa only [map_add, map_smul, cyclicV_h1, cyclicV_h2] using
        transfer (h 1) (h 2 + (1/2 : ℝ) • h 1) b (hd 2 (by decide))
    · change KB B (h 2) (h 1 + (1/2 : ℝ) • h 2) =
        b • (h 1 + (1/2 : ℝ) • h 2)
      simpa only [map_add, map_smul, cyclicV_h1, cyclicV_h0] using
        transfer (h 1) (h 0 + (1/2 : ℝ) • h 1) b (hd 0 (by decide))
    · exact False.elim (hj rfl)
  · intro u
    simpa only [cyclicV_h1, cyclicV_X02, octConj_conj] using
      transfer (h 1) (X02 (octConj u)) b (h02 (octConj u))
  · intro u
    simpa only [cyclicV_h1, cyclicV_X12, octConj_conj] using
      transfer (h 1) (X12 (octConj u)) c (h12 (octConj u))
  · intro u
    simpa only [cyclicV_h1, cyclicV_X01] using
      transfer (h 1) (X01 u) c (h01 u)

/-- Construct, rather than assume, the intermediate data for the original gate.
Only genuine cubic symmetry and A(q(referenceCubic))B=0 are available. -/
theorem threeFrameScalarData_of_A_q_zero (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) : Nonempty (ThreeFrameScalarData B) := by
  obtain ⟨a0,b0,c0,ha0,hd0,h010,h020,h120⟩ := h0_coarse_actions_of_A_q_zero B hB
  obtain ⟨a1,b1,c1,ha1,hd1,h011,h021,h121⟩ := h1_coarse_actions_of_A_q_zero B hB
  obtain ⟨a2,b2,c2,ha2,hd2,h012,h022,h122⟩ := h2_coarse_actions_of_A_q_zero B hB
  refine ⟨{
    a := ![a0,a1,a2]
    b := ![b0,b1,b2]
    c := ![c0,c1,c2]
    on_h_self := ?_
    on_complementary_diagonal := ?_
    on_X01 := ?_
    on_X02 := ?_
    on_X12 := ?_ }⟩
  · intro i
    fin_cases i
    · simpa using ha0
    · simpa using ha1
    · simpa using ha2
  · intro i j hij
    fin_cases i
    · simpa using hd0 j hij.symm
    · simpa using hd1 j hij.symm
    · simpa using hd2 j hij.symm
  · intro u
    simpa using And.intro (h010 u) (And.intro (h011 u) (h012 u))
  · intro u
    simpa using And.intro (h020 u) (And.intro (h021 u) (h022 u))
  · intro u
    simpa using And.intro (h120 u) (And.intro (h121 u) (h122 u))

/-- Common actual coarse actions follow from the unrestricted original kernel.
The operator endpoint still requires the native reference action and spanning step. -/
theorem threeFrame_common_actions_of_A_q_zero (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) :
    ∃ data : ThreeFrameScalarData B, ∃ b : ℝ,
      (∀ i, data.a i = -b) ∧ (∀ i, data.b i = b) ∧ (∀ i, data.c i = -b/2) := by
  obtain ⟨data⟩ := threeFrameScalarData_of_A_q_zero B hB
  obtain ⟨b,ha,hb,hc⟩ := data.common_coefficients
  exact ⟨data,b,ha,hb,hc⟩

end
end AlbertRecognition.FixedFrame
