/- Native flat sections of the full 54-entry ledger map. -/
module

public import Glennie.Compact.NativeFlatRank20
public import Glennie.Compact.NativeSectionFullLedger

@[expose] public section

namespace Glennie.Compact.NativeFlatSections

open Glennie.Compact.Affine20 Glennie.Compact.FlowFamily

noncomputable section

set_option autoImplicit false

/-- The actual original flat-base derivative supplies both local full54 sections.
All neighbourhood, continuity, frame, chart and strict-sign outputs are retained. -/
theorem native_flat_two_sections_full54 :
    ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧
      encode20 (ledger54 Glennie.Compact.Sections.flatBase) ∈ V ∧
      ∃ secPos secNeg : (Fin 20 → ℝ) → Triple,
        ContinuousOn secPos V ∧ ContinuousOn secNeg V ∧
        (∀ b ∈ V, ∀ a : Fin 3, Frame (secPos b a)) ∧
        (∀ b ∈ V, ∀ a : Fin 3, Frame (secNeg b a)) ∧
        (∀ b ∈ V, encode20 (ledger54 (secPos b)) = b) ∧
        (∀ b ∈ V, encode20 (ledger54 (secNeg b)) = b) ∧
        (∀ b ∈ V, ledger54 (secPos b) = decode20 b) ∧
        (∀ b ∈ V, ledger54 (secNeg b) = decode20 b) ∧
        (∀ b ∈ V, 0 < Glennie.Compact.Sections.phiOf (secPos b)) ∧
        (∀ b ∈ V, Glennie.Compact.Sections.phiOf (secNeg b) < 0) := by
  obtain ⟨e, he, _, _, _⟩ :=
    Glennie.Compact.NativeFlatRank20.native_rank20_strict_with_inverse
  have heBase :
      (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) =
        rowLedgerDeriv Glennie.Compact.Sections.flatBase := by
    simpa only [Glennie.Compact.Sections.flatBase] using he
  exact Glennie.Compact.NativeSectionFullLedger.flat_two_sections_full54 e heBase

end
end Glennie.Compact.NativeFlatSections
