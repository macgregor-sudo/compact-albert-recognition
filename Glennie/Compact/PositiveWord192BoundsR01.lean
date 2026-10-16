module
public import Glennie.Compact.PositiveWord16BoundsR01
public import Glennie.Compact.PositiveWordDefinitionR01

/- Native square-cone bounds for each actual 192-label evaluation.
   This concerns algebraic U-word values, not sampling or implementation. -/
@[expose] public section
namespace Glennie.Compact.PositiveWord192BoundsR01
open Glennie Glennie.NativeSquareConeR01
open Glennie.Compact.PositiveFilterAlgebraR01
open Glennie.Compact.PositiveWordLayersR01
open Glennie.Compact.PositiveWordBookkeepingR01 (Label)
open Glennie.Compact.PositiveWordEndpointR01
open Glennie.Compact.PositiveWordDefinitionR01
open Glennie.Compact.NativeWordBoundsR01
noncomputable section
set_option autoImplicit false

def amplitudes (p q r : Fin 3 → Albert) (o sy sx : Bool) (i : Fin 3)
    (l : Bool) : List Albert :=
  let first := if o then amplitude (encoder p) sx else amplitude (encoder q) sy
  let second := if o then amplitude (encoder q) sy else amplitude (encoder p) sx
  if i = 0 then [first, second, amplitude (encoder r) false, amplitude (encoder p) l]
  else if i = 1 then [first, second, amplitude (encoder r) true, amplitude (encoder p) l]
  else [first, second, amplitude (encoder p) l]

private theorem filterLinear_apply (w : Albert) (s : Bool) (v : Albert) :
    filterLinear w s v = filter w s v := rfl

theorem word_eq_applyWord (p q r : Fin 3 → Albert) (v : Albert)
    (o sy sx : Bool) (i : Fin 3) (l : Bool) :
    word (encoder p) (encoder q) (encoder r) v o sy sx i l =
      applyWord (amplitudes p q r o sy sx i l) v := by
  fin_cases i <;> cases o <;>
    simp [word, wordLinear, middleLinear, amplitudes,
      LinearMap.comp_apply, filterLinear_apply, filter, applyWord]

theorem amplitudes_square_bound (p q r : Fin 3 → Albert)
    (hp : Frame p) (hq : Frame q) (hr : Frame r)
    (o sy sx : Bool) (i : Fin 3) (l : Bool) :
    ∀ b ∈ amplitudes p q r o sy sx i l,
      Positive ((1 : Albert) - jordan b b) := by
  intro b hb
  fin_cases i <;> cases o <;> simp [amplitudes] at hb
  all_goals rcases hb with rfl | rfl | rfl | rfl
  all_goals first
    | exact frame_amplitude_square_le p hp sx
    | exact frame_amplitude_square_le q hq sy
    | exact frame_amplitude_square_le r hr false
    | exact frame_amplitude_square_le r hr true
    | exact frame_amplitude_square_le p hp l

theorem evaluation_bounds (p q r : Fin 3 → Albert)
    (hp : Frame p) (hq : Frame q) (hr : Frame r) (a : Label) :
    0 ≤ evaluation p q r a ∧ evaluation p q r a ≤ 1 := by
  rcases a with ⟨o, sy, sx, i, l, k, j⟩
  simp only [evaluation]
  rw [word_eq_applyWord]
  exact idempotent_word_pairing_bounds (amplitudes p q r o sy sx i l)
    (amplitudes_square_bound p q r hp hq hr o sy sx i l)
    (endpoint r k) (endpoint q j)
    (Glennie.Compact.PositiveWord16BoundsR01.endpoint_idempotent r hr k)
    (Glennie.Compact.PositiveWord16BoundsR01.endpoint_idempotent q hq j)
    (Glennie.Compact.PositiveWord16BoundsR01.endpoint_trace_one q hq j)

end
end Glennie.Compact.PositiveWord192BoundsR01
