module

public import Glennie.Compact.PositiveWordSignR01
public import Glennie.Compact.NearbyOrbitsClosed

/- Word-score sign stability in the existing local ledger domain.
   Observations are abstract real scalars; no positive-map semantics. -/
@[expose] public section
namespace Glennie.Compact.PositiveWordNearFlatR01
open Glennie
open Glennie.Compact.Sections Glennie.Compact.Affine20
open Glennie.Compact.PositiveWordBookkeepingR01
open Glennie.Compact.PositiveWordDefinitionR01
open Glennie.Compact.PositiveWordErrorR01
open Glennie.Compact.PositiveWordSignR01
noncomputable section
set_option autoImplicit false

theorem near_flat_word_sign_stable :
    ∃ V : Set Ledger54, IsOpen V ∧
      ledger54 Glennie.Compact.FrameTopology.flatBaseTriple ∈ V ∧
      ∀ (T : Triple) (observed : Label → ℝ) (ε : ℝ),
        (∀ a : Fin 3, Glennie.Frame (T a)) → ledger54 T ∈ V →
        (∀ a : Label, |observed a - evaluation (T 0) (T 1) (T 2) a| ≤ ε) →
        1280 * ε ≤ 1 / 27 →
        ((observedScore observed < 0 ∧ phiOf T < 0) ∨
         (0 < observedScore observed ∧ 0 < phiOf T)) := by
  obtain ⟨V, ho, hm, hb⟩ := Glennie.Compact.NearbyOrbits.phi_bounded_away_near_flat
  refine ⟨V, ho, hm, ?_⟩
  intro T observed ε hT hV herr hε
  have hmargin := hb T hT hV
  have hε0 : 0 ≤ ε :=
    le_trans (abs_nonneg (observed (default : Label) -
      evaluation (T 0) (T 1) (T 2) default)) (herr default)
  have herror := expanded_error (T 0) (T 1) (T 2) observed ε hε0 herr
  rw [← phiOf_apply] at herror
  change |observedScore observed - phiOf T| ≤ 1280 * ε at herror
  rcases abs_le.mp herror with ⟨hl, hu⟩
  rcases le_total 0 (phiOf T) with hp | hn
  · rw [abs_of_nonneg hp] at hmargin
    right
    constructor <;> linarith
  · rw [abs_of_nonpos hn] at hmargin
    left
    constructor <;> linarith

end
end Glennie.Compact.PositiveWordNearFlatR01
