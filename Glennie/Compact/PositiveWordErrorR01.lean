module

public import Glennie.Compact.PositiveWordEqualityR01

/- Deterministic errors in the labeled scalar values.
   No probability, independence, positivity, or implementation premise. -/
@[expose] public section
namespace Glennie.Compact.PositiveWordErrorR01
open Glennie
open Glennie.Compact.PositiveWordBookkeepingR01
open Glennie.Compact.PositiveWordDefinitionR01
open Glennie.Compact.PositiveWordEqualityR01
noncomputable section
set_option autoImplicit false

theorem expanded_error (p q r : Fin 3 → Albert)
    (observed : Label → ℝ) (ε : ℝ) (_hε : 0 ≤ ε)
    (herr : ∀ a : Label, |observed a - evaluation p q r a| ≤ ε) :
    |(∑ a : Label, labelCoefficient a * observed a) -
      phi (encoder p) (encoder q) (encoder r)| ≤ 1280 * ε := by
  have hdiff :
      (∑ a : Label, labelCoefficient a * observed a) - expanded p q r =
        ∑ a : Label, labelCoefficient a * (observed a - evaluation p q r a) := by
    simp only [expanded, Finset.sum_sub_distrib, mul_sub]
  rw [← expanded_eq_phi p q r, hdiff]
  calc
    |∑ a : Label, labelCoefficient a * (observed a - evaluation p q r a)| ≤
        ∑ a : Label, |labelCoefficient a * (observed a - evaluation p q r a)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : Label, |labelCoefficient a| * ε := by
      apply Finset.sum_le_sum
      intro a ha
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (herr a) (abs_nonneg (labelCoefficient a))
    _ = (∑ a : Label, |labelCoefficient a|) * ε := by
      rw [Finset.sum_mul]
    _ = 1280 * ε := by rw [coefficient_mass]

end
end Glennie.Compact.PositiveWordErrorR01
