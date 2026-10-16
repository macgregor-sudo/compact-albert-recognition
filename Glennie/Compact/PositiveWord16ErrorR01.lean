module

public import Glennie.Compact.PositiveWord16EqualityR01

/- Deterministic scalar error for the distinct 16-label native-U alphabet.
   No cone, interval, probability, or implementation premise. -/
@[expose] public section
namespace Glennie.Compact.PositiveWord16ErrorR01
open Glennie
open Glennie.Compact.PositiveWord16DefinitionR01
open Glennie.Compact.PositiveWord16EqualityR01
noncomputable section
set_option autoImplicit false

def observedScore (observed : Label16 → ℝ) : ℝ :=
  ∑ a : Label16, labelCoefficient a * observed a

theorem expanded_error (p q r : Fin 3 → Albert)
    (observed : Label16 → ℝ) (ε : ℝ) (_hε : 0 ≤ ε)
    (herr : ∀ a : Label16, |observed a - evaluation p q r a| ≤ ε) :
    |observedScore observed -
      phi (encoder p) (encoder q) (encoder r)| ≤ 16 * ε := by
  have hdiff :
      observedScore observed - expanded p q r =
        ∑ a : Label16, labelCoefficient a * (observed a - evaluation p q r a) := by
    simp only [observedScore, expanded, Finset.sum_sub_distrib, mul_sub]
  rw [← expanded_eq_phi p q r, hdiff]
  calc
    |∑ a : Label16, labelCoefficient a * (observed a - evaluation p q r a)| ≤
        ∑ a : Label16, |labelCoefficient a * (observed a - evaluation p q r a)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : Label16, |labelCoefficient a| * ε := by
      apply Finset.sum_le_sum
      intro a ha
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (herr a) (abs_nonneg (labelCoefficient a))
    _ = (∑ a : Label16, |labelCoefficient a|) * ε := by
      rw [Finset.sum_mul]
    _ = 16 * ε := by rw [coefficient_mass]

theorem sign_certificate (p q r : Fin 3 → Albert)
    (observed : Label16 → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (herr : ∀ a : Label16, |observed a - evaluation p q r a| ≤ ε)
    (hm : 16 * ε < |observedScore observed|) :
    (observedScore observed < 0 ∧ phi (encoder p) (encoder q) (encoder r) < 0) ∨
    (0 < observedScore observed ∧ 0 < phi (encoder p) (encoder q) (encoder r)) := by
  have hb := expanded_error p q r observed ε hε herr
  rcases abs_le.mp hb with ⟨hl, hu⟩
  rcases le_total 0 (observedScore observed) with hp | hn
  · rw [abs_of_nonneg hp] at hm
    right
    constructor <;> linarith
  · rw [abs_of_nonpos hn] at hm
    left
    constructor <;> linarith

end
end Glennie.Compact.PositiveWord16ErrorR01
