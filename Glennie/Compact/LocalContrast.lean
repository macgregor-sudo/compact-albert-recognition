/- The algebraic readout of the signed invariant on ordered frame triples. -/
module

public import Glennie.Compact.NearbyOrbitsClosed
public import Glennie.Compact.OperationalPhi
public import Glennie.Compact.NativeQFamilyLedger

@[expose] public section
namespace Glennie.Compact.LocalContrast

open Glennie
open Glennie.Compact.Affine20
open Glennie.Compact.Sections
open Glennie.Compact.OperationalPhi

noncomputable section

/-- Division-free six-readout score on the fixed-orientation frame encoders. -/
def score (T : Triple) : ℝ :=
  let x := encoder (T 0)
  let y := encoder (T 1)
  let z := encoder (T 2)
  4 * delta x y z (halfAmplitude x) y -
    delta x y z x y - delta x y z 1 y

theorem score_eq_two_phi (T : Triple) : score T = 2 * phiOf T := by
  exact phi_division_free (encoder (T 0)) (encoder (T 1)) (encoder (T 2))

end
end Glennie.Compact.LocalContrast
