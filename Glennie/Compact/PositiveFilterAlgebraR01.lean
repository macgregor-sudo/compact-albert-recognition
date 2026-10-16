module

public import Glennie.Compact.OperationalPhi
public import Mathlib.Tactic.LinearCombination

/- Pure native filter algebra. No positivity, interval bound,
finite-word expansion, or implementation claim. -/
@[expose] public section
namespace Glennie.Compact.PositiveFilterAlgebraR01
open Glennie Glennie.Compact.OperationalPhi
noncomputable section
set_option autoImplicit false

def amplitude (w : Albert) (s : Bool) : Albert :=
  halfAmplitude (if s then -w else w)

def filter (w : Albert) (s : Bool) (v : Albert) : Albert :=
  U (amplitude w s) v

/- Rearrangement and linear normalization occur over abstract module elements.
   Native U, jordan, and filter never appear in these helper proofs. -/
private theorem rearrange_sub_sub {E : Type*} [AddCommGroup E]
    (A B C D : E) (h : A - B - C = D) : A = B + C + D := by
  have h₁ : A - B = D + C := sub_eq_iff_eq_add.mp h
  have h₂ : A = (D + C) + B := sub_eq_iff_eq_add.mp h₁
  exact h₂.trans (by ac_rfl)

private theorem recover_linear {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P M R V J : E)
    (hp : (4 : ℝ) • P = R + V + (2 : ℝ) • J)
    (hm : (4 : ℝ) • M = R + V - (2 : ℝ) • J) :
    J = P - M := by
  linear_combination (norm := module) (1 / 4 : ℝ) • hm - (1 / 4 : ℝ) • hp

private theorem recover_quadratic {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P M R V J : E)
    (hp : (4 : ℝ) • P = R + V + (2 : ℝ) • J)
    (hm : (4 : ℝ) • M = R + V - (2 : ℝ) • J) :
    R = (2 : ℝ) • P + (2 : ℝ) • M - V := by
  linear_combination (norm := module) (-1 / 2 : ℝ) • hp + (-1 / 2 : ℝ) • hm

theorem filter_plus_eq (w v : Albert) :
    filter w false v = U (halfAmplitude w) v := rfl

theorem filter_minus_eq (w v : Albert) :
    filter w true v = U (halfAmplitude (-w)) v := rfl

theorem U_neg_base (w v : Albert) : U (-w) v = U w v := by
  have h := U_smul_base (-1 : ℝ) w v
  norm_num only [neg_one_smul] at h
  simpa only [one_smul] using h

theorem plus_subtraction_stage (w v : Albert) :
    (4 : ℝ) • U (halfAmplitude w) v - U w v - v =
      (2 : ℝ) • jordan w v := by
  simpa only [U_one] using four_U_halfAmplitude w v

theorem minus_subtraction_stage (w v : Albert) :
    (4 : ℝ) • U (halfAmplitude (-w)) v - U w v - v =
      -((2 : ℝ) • jordan w v) := by
  simpa only [U_one, U_neg_base, jordan_neg_left, smul_neg] using
    four_U_halfAmplitude (-w) v

theorem four_filter_plus (w v : Albert) :
    (4 : ℝ) • filter w false v =
      U w v + v + (2 : ℝ) • jordan w v := by
  exact (congrArg (fun a : Albert => (4 : ℝ) • a) (filter_plus_eq w v)).trans
    (rearrange_sub_sub _ _ _ _ (plus_subtraction_stage w v))

theorem four_filter_minus (w v : Albert) :
    (4 : ℝ) • filter w true v =
      U w v + v - (2 : ℝ) • jordan w v := by
  have hr : (4 : ℝ) • U (halfAmplitude (-w)) v =
      U w v + v + -((2 : ℝ) • jordan w v) :=
    rearrange_sub_sub _ _ _ _ (minus_subtraction_stage w v)
  have ht :=
    (congrArg (fun a : Albert => (4 : ℝ) • a) (filter_minus_eq w v)).trans hr
  simpa only [sub_eq_add_neg] using ht

theorem jordan_filter_difference (w v : Albert) :
    jordan w v = filter w false v - filter w true v := by
  exact recover_linear (filter w false v) (filter w true v) (U w v) v
    (jordan w v) (four_filter_plus w v) (four_filter_minus w v)

theorem U_filter_decomposition (w v : Albert) :
    U w v = (2 : ℝ) • filter w false v + (2 : ℝ) • filter w true v - v := by
  exact recover_quadratic (filter w false v) (filter w true v) (U w v) v
    (jordan w v) (four_filter_plus w v) (four_filter_minus w v)

end
end Glennie.Compact.PositiveFilterAlgebraR01
