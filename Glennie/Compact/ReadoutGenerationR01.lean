/- A posteriori full-generation certificate from six scalar readouts of actual
ordered frames. The unit is supplied by the frame sum. -/
module
public import Glennie.NativeOrderedFrameGenerationR01
public import Glennie.Compact.ReadoutRobustnessR01

@[expose] public section
namespace Glennie.Compact.ReadoutGenerationR01
noncomputable section
open Glennie Glennie.Compact.Affine20 Glennie.Compact.Sections
open Glennie.Compact.ReadoutRobustnessR01

/-- A strict measured margin certifies full generation by the nine ordered atoms. -/
theorem ordered_frame_atoms_generate_of_noisy_readouts
    (T : Triple) (hT : ∀ a, Frame (T a))
    (noisy : Readouts) (ε : ℝ) (hε : 0 ≤ ε)
    (hErr : ErrorsAtMost noisy (exactReadouts T) ε)
    (hMargin : 12 * ε < |weightedScore noisy|)
    (K : Submodule ℝ Albert)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (hAtoms : ∀ a i, T a i ∈ K) : K = ⊤ := by
  have hs := sign_certificate T noisy ε hε hErr hMargin
  have hphi : phiOf T ≠ 0 := by
    rcases hs with ⟨_, hn⟩ | ⟨_, hp⟩
    · exact ne_of_lt hn
    · exact ne_of_gt hp
  exact Glennie.NativeOrderedFrameGenerationR01.ordered_frame_atoms_generate
    T hT hphi K hJ hAtoms

end
end Glennie.Compact.ReadoutGenerationR01
