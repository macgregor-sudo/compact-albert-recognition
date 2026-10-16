/- Consumer of the full 54-entry two-section theorem. -/
module

public import Glennie.Compact.Sections

@[expose] public section

namespace Glennie.Compact.NativeSectionFullLedger

open Glennie.Compact.Affine20 Glennie.Compact.FlowFamily Glennie.Compact.Sections

noncomputable section

set_option autoImplicit false

/-- Both original local sections have the same complete54 ledger, with every
original hypothesis, neighbourhood, frame, chart and sign output retained. -/
theorem flat_two_sections_full54 (e : (Fin 20 → ℝ) ≃L[ℝ] (Fin 20 → ℝ))
    (he : (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) = rowLedgerDeriv flatBase) :
    ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧ encode20 (ledger54 flatBase) ∈ V ∧
      ∃ secPos secNeg : (Fin 20 → ℝ) → Triple,
        ContinuousOn secPos V ∧ ContinuousOn secNeg V ∧
        (∀ b ∈ V, ∀ a : Fin 3, Frame (secPos b a)) ∧
        (∀ b ∈ V, ∀ a : Fin 3, Frame (secNeg b a)) ∧
        (∀ b ∈ V, encode20 (ledger54 (secPos b)) = b) ∧
        (∀ b ∈ V, encode20 (ledger54 (secNeg b)) = b) ∧
        (∀ b ∈ V, ledger54 (secPos b) = decode20 b) ∧
        (∀ b ∈ V, ledger54 (secNeg b) = decode20 b) ∧
        (∀ b ∈ V, 0 < phiOf (secPos b)) ∧
        (∀ b ∈ V, phiOf (secNeg b) < 0) := by
  obtain ⟨V, hVopen, hbase, secPos, secNeg, hcontPos, hcontNeg,
    hframesPos, hframesNeg, hchartPos, hchartNeg, hpos, hneg⟩ :=
    flat_two_sections e he
  refine ⟨V, hVopen, hbase, secPos, secNeg, hcontPos, hcontNeg,
    hframesPos, hframesNeg, hchartPos, hchartNeg, ?_, ?_, hpos, hneg⟩
  · intro b hb
    have h := decode_encode_frames (secPos b) (hframesPos b hb)
    rw [hchartPos b hb] at h
    exact h.symm
  · intro b hb
    have h := decode_encode_frames (secNeg b) (hframesNeg b hb)
    rw [hchartNeg b hb] at h
    exact h.symm

end
end Glennie.Compact.NativeSectionFullLedger
