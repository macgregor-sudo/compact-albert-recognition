/- Unrestricted native q-fiber recovery after the actual Albert kernel line.
no Euclidean coefficient identification is assumed here. -/
module

public import AlbertRecognition.FixedFrame.KernelLine

@[expose] public section
namespace AlbertRecognition
noncomputable section
open FixedFrame Glennie

/-- An explicit native witness for nonzero quadratic reference curvature. -/
theorem q_reference_h0_h1_h0 :
    q referenceCubic (h 0) (h 1) (h 0) = h 0 + (2 : ℝ) • h 1 := by
  simp only [q, KB_referenceCubic, operatorComm_apply]
  simp only [KA_h_cross 1 0 (by decide), KA_h_cross 0 1 (by decide),
    KA_h_self, map_add, map_smul]
  module

theorem q_reference_ne_zero : q referenceCubic ≠ 0 := by
  intro hz
  have hv := congrArg (fun T : V → V → Module.End ℝ V => T (h 0) (h 1) (h 0)) hz
  rw [q_reference_h0_h1_h0] at hv
  change h 0 + (2 : ℝ) • h 1 = 0 at hv
  have hd := congrArg (fun x : V => (x : Albert).d1) hv
  norm_num [h, e, unit] at hd

/-- Every competitor is constrained solely by equality of the actual native q.
Universal operator Jacobi supplies kernel membership; the true reference
kernel line and nonzero witness force the only possible scales to be ±1. -/
theorem q_fiber_reference (B : SymmetricCubic) :
    q B = q referenceCubic ↔
      B = referenceCubic ∨ B = scalarCubic (-1) referenceCubic := by
  constructor
  · intro hq
    have hB : A (q referenceCubic) B = 0 := by
      rw [← hq]
      exact A_q_self B
    obtain ⟨b,hb⟩ := (reference_nativeKernelLine B).mp hB
    have hs : b^2 • q referenceCubic = (1 : ℝ) • q referenceCubic := by
      rw [one_smul, ← q_scalarCubic, ← hb]
      exact hq
    have hb2 : b^2 = 1 := smul_left_injective ℝ q_reference_ne_zero hs
    rcases sq_eq_one_iff.mp hb2 with hb1 | hbm1
    · left
      rw [hb1, scalarCubic_one] at hb
      exact hb
    · right
      simpa only [hbm1] using hb
  · rintro (rfl | rfl)
    · rfl
    · rw [q_scalarCubic]
      norm_num

end
end AlbertRecognition
