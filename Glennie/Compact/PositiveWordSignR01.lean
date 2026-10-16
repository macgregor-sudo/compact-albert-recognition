module

public import Glennie.Compact.PositiveWordErrorR01

/- A posteriori sign certificates for abstract real scalar observations.
   No positive-map or probability interpretation is asserted. -/
@[expose] public section
namespace Glennie.Compact.PositiveWordSignR01
open Glennie
open Glennie.Compact.PositiveWordBookkeepingR01
open Glennie.Compact.PositiveWordDefinitionR01
open Glennie.Compact.PositiveWordErrorR01
noncomputable section
set_option autoImplicit false

def observedScore (observed : Label → ℝ) : ℝ :=
  ∑ a : Label, labelCoefficient a * observed a

theorem positive_certificate (p q r : Fin 3 → Albert)
    (observed : Label → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (herr : ∀ a : Label, |observed a - evaluation p q r a| ≤ ε)
    (hp : 1280 * ε < observedScore observed) :
    0 < phi (encoder p) (encoder q) (encoder r) := by
  have hb := expanded_error p q r observed ε hε herr
  have hu := (abs_le.mp hb).2
  dsimp [observedScore] at hp
  linarith

theorem negative_certificate (p q r : Fin 3 → Albert)
    (observed : Label → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (herr : ∀ a : Label, |observed a - evaluation p q r a| ≤ ε)
    (hn : observedScore observed < -(1280 * ε)) :
    phi (encoder p) (encoder q) (encoder r) < 0 := by
  have hb := expanded_error p q r observed ε hε herr
  have hl := (abs_le.mp hb).1
  dsimp [observedScore] at hn
  linarith

theorem sign_certificate (p q r : Fin 3 → Albert)
    (observed : Label → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (herr : ∀ a : Label, |observed a - evaluation p q r a| ≤ ε)
    (hm : 1280 * ε < |observedScore observed|) :
    (observedScore observed < 0 ∧ phi (encoder p) (encoder q) (encoder r) < 0) ∨
    (0 < observedScore observed ∧ 0 < phi (encoder p) (encoder q) (encoder r)) := by
  rcases le_total 0 (observedScore observed) with hp | hn
  · rw [abs_of_nonneg hp] at hm
    exact Or.inr ⟨by linarith, positive_certificate p q r observed ε hε herr hm⟩
  · rw [abs_of_nonpos hn] at hm
    have hm' : observedScore observed < -(1280 * ε) := by linarith
    exact Or.inl ⟨by linarith, negative_certificate p q r observed ε hε herr hm'⟩

end
end Glennie.Compact.PositiveWordSignR01
