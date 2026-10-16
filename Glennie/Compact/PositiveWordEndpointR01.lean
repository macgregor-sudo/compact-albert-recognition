module

public import Glennie.Compact.PositiveWordLayersR01

/- The four signed endpoint choices collapse by bilinearity.
   This is independent of all native U and cone facts. -/
@[expose] public section
namespace Glennie.Compact.PositiveWordEndpointR01
open Glennie Glennie.Compact.PositiveWordBookkeepingR01
noncomputable section
set_option autoImplicit false

def endpoint (p : Fin 3 → Albert) (s : Bool) : Albert :=
  if s then p 0 else p 2

theorem signed_endpoint_pairing
    (F : Albert →ₗ[ℝ] Albert) (q r : Fin 3 → Albert) :
    (∑ k : Bool, ∑ j : Bool,
      sign k * sign j * inner (endpoint r k) (F (endpoint q j))) =
    inner (encoder r) (F (encoder q)) := by
  simp [Fintype.sum_bool, sign, endpoint, encoder, map_sub,
    inner_sub_left, inner_sub_right]
  ring

end
end Glennie.Compact.PositiveWordEndpointR01
