/- Concrete h0 coarse actions derived from the native scalar blocks.
-/
module

public import AlbertRecognition.FixedFrame.ScalarBlocks

@[expose] public section
namespace AlbertRecognition.FixedFrame
noncomputable section
open Glennie

/-- Actual complementary diagonal coordinates for the zero-based h0 frame. -/
theorem h1_half_h0_eq_frameD :
    h 1 + (1/2 : ℝ) • h 0 = -(3/2 : ℝ) • frameD := by
  have hneg (x : Albert) : -x =
      ⟨-x.d0,-x.d1,-x.d2,-x.o01,-x.o02,-x.o12⟩ := rfl
  apply Subtype.ext
  apply Albert.ext <;> norm_num [h, e, unit, frameD, hneg]

theorem h2_half_h0_eq_frameD :
    h 2 + (1/2 : ℝ) • h 0 = (3/2 : ℝ) • frameD := by
  apply Subtype.ext
  apply Albert.ext <;> norm_num [h, e, unit, frameD]

/-- The scalar-block output supplies every native coarse h0 action needed by
three-frame transport. No covariance or invariance is a premise. -/
theorem frame_commutant_h0_coarse_actions (G : Module.End ℝ V)
    (hG : ∀ t : Fin 8, G.comp (frameAction (octBasis t)) =
      (frameAction (octBasis t)).comp G) :
    ∃ a b c : ℝ, G (h 0) = a • h 0 ∧
      (∀ j : Fin 3, j ≠ 0 →
        G (h j + (1/2 : ℝ) • h 0) = b • (h j + (1/2 : ℝ) • h 0)) ∧
      (∀ u : Octonion, G (X01 u) = c • X01 u) ∧
      (∀ u : Octonion, G (X02 u) = c • X02 u) ∧
      (∀ u : Octonion, G (X12 u) = b • X12 u) := by
  obtain ⟨a,b,c,ha,hb,h12,hs⟩ := frame_commutant_scalar_blocks G hG
  refine ⟨a,b,c,ha,?_,?_,?_,h12⟩
  · intro j hj
    fin_cases j
    · exact False.elim (hj rfl)
    · change G (h 1 + (1/2 : ℝ) • h 0) = b • (h 1 + (1/2 : ℝ) • h 0)
      rw [h1_half_h0_eq_frameD, map_smul, hb]
      module
    · change G (h 2 + (1/2 : ℝ) • h 0) = b • (h 2 + (1/2 : ℝ) • h 0)
      rw [h2_half_h0_eq_frameD, map_smul, hb]
      module
  · intro u
    have hh := hs (u,0)
    simpa only [frameSpin_apply, map_zero, add_zero] using hh
  · intro u
    have hh := hs (0,u)
    simpa only [frameSpin_apply, map_zero, zero_add] using hh

/-- Concrete h0 coarse data for the arbitrary-cubic Jacobi kernel. The sole
hypothesis is the literal initial-gate equation; all actions are derived. -/
theorem h0_coarse_actions_of_A_q_zero (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) :
    ∃ a b c : ℝ, KB B (h 0) (h 0) = a • h 0 ∧
      (∀ j : Fin 3, j ≠ 0 →
        KB B (h 0) (h j + (1/2 : ℝ) • h 0) =
          b • (h j + (1/2 : ℝ) • h 0)) ∧
      (∀ u : Octonion, KB B (h 0) (X01 u) = c • X01 u) ∧
      (∀ u : Octonion, KB B (h 0) (X02 u) = c • X02 u) ∧
      (∀ u : Octonion, KB B (h 0) (X12 u) = b • X12 u) := by
  apply frame_commutant_h0_coarse_actions (KB B (h 0))
  intro t
  apply LinearMap.ext
  intro x
  exact h0_frame_action_intertwines_of_A_q_zero B hB (octBasis t) x

end
end AlbertRecognition.FixedFrame
