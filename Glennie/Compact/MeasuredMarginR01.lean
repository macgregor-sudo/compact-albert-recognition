module
public import Glennie.Compact.InputDisplacementR01
public import Glennie.NativeGenerationStabilizersR01
public import Glennie.Compact.ReadoutRobustnessR01

/- Measured margins using native producers.
ε denotes entrywise raw readout error, ξ a certified scalar error allowance,
and δ endpoint displacement. No target-null or multiplication-defect claim. -/
@[expose] public section
namespace Glennie.Compact.MeasuredMarginR01
open Glennie
open Glennie.NativeGenerationEndpointR01
open Glennie.NativeGenerationStabilizersR01
open Glennie.Compact.NativeNormKernel
noncomputable section
set_option autoImplicit false

 theorem scalar_margin_lower (observed actual ξ : ℝ)
    (herr : |observed-actual| ≤ ξ) : |observed|-ξ ≤ |actual| := by
  have ht : |observed| ≤ |observed-actual|+|actual| := by
    calc
      |observed| = |(observed-actual)+actual| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  linarith

 theorem scalar_sign_certificate (observed actual ξ : ℝ) (hξ : 0 ≤ ξ)
    (herr : |observed-actual| ≤ ξ) (hmargin : ξ < |observed|) :
    (observed < 0 ∧ actual < 0) ∨ (0 < observed ∧ 0 < actual) := by
  rcases abs_le.mp herr with ⟨hl,hu⟩
  rcases le_total 0 observed with hp | hn
  · rw [abs_of_nonneg hp] at hmargin
    exact Or.inr ⟨by linarith, by linarith⟩
  · rw [abs_of_nonpos hn] at hmargin
    exact Or.inl ⟨by linarith, by linarith⟩

 theorem native_ne_zero_of_measured_margin (x y z : Albert) (observed ξ : ℝ)
    (herr : |observed-phi x y z| ≤ ξ) (hmargin : ξ < |observed|) :
    phi x y z ≠ 0 := by
  have hl := scalar_margin_lower observed (phi x y z) ξ herr
  intro he
  rw [he, abs_zero] at hl
  linarith

 /-- Definition-free unital generation and the actual native point stabilizer. -/
 theorem native_generation_of_measured_margin (x y z : Albert) (observed ξ : ℝ)
    (herr : |observed-phi x y z| ≤ ξ) (hmargin : ξ < |observed|) :
    (∀ (K : Submodule ℝ Albert), (1 : Albert) ∈ K →
      (∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K) →
      x ∈ K → y ∈ K → z ∈ K → K = ⊤) ∧
    (∀ g : CompactAutomorphism,
      g.equiv x = x → g.equiv y = y → g.equiv z = z →
      g = CompactAutomorphism.refl) := by
  have hp := native_ne_zero_of_measured_margin x y z observed ξ herr hmargin
  exact ⟨fun K h1 hJ hx hy hz => eq_top_of_phi_ne_zero K h1 hJ x y z hx hy hz hp,
    fun g hx hy hz => automorphism_eq_refl_of_phi_ne_zero g x y z hp hx hy hz⟩

 /-- Certified scalar error and native displacement compose additively. -/
 theorem measured_displacement_error (x y z x' y' z' : Albert)
    (observed ξ R δ : ℝ) (hR : 0 ≤ R)
    (herr : |observed-phi x y z| ≤ ξ)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R)
    (hx' : ‖x'‖ ≤ R) (hy' : ‖y'‖ ≤ R) (hz' : ‖z'‖ ≤ R)
    (hdx : ‖x-x'‖ ≤ δ) (hdy : ‖y-y'‖ ≤ δ) (hdz : ‖z-z'‖ ≤ δ) :
    |observed-phi x' y' z'| ≤ ξ+18*R^8*δ := by
  have hp := phi_displacement_18 x y z x' y' z' R δ hR
    hx hy hz hx' hy' hz' hdx hdy hdz
  calc
    _ = |(observed-phi x y z)+(phi x y z-phi x' y' z')| := by congr 1; ring
    _ ≤ |observed-phi x y z|+|phi x y z-phi x' y' z'| := abs_add_le _ _
    _ ≤ ξ+18*R^8*δ := add_le_add herr hp

 /-- Equality at the error margin is deliberately excluded by the strict premise. -/
 theorem same_radius_sign_and_generation (x y z x' y' z' : Albert)
    (observed ξ R δ : ℝ) (hξ : 0 ≤ ξ) (hR : 0 ≤ R)
    (herr : |observed-phi x y z| ≤ ξ)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R)
    (hx' : ‖x'‖ ≤ R) (hy' : ‖y'‖ ≤ R) (hz' : ‖z'‖ ≤ R)
    (hdx : ‖x-x'‖ ≤ δ) (hdy : ‖y-y'‖ ≤ δ) (hdz : ‖z-z'‖ ≤ δ)
    (hmargin : 18*R^8*δ < |observed|-ξ) :
    ((observed < 0 ∧ phi x' y' z' < 0) ∨
      (0 < observed ∧ 0 < phi x' y' z')) ∧
    (∀ (K : Submodule ℝ Albert), (1 : Albert) ∈ K →
      (∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K) →
      x' ∈ K → y' ∈ K → z' ∈ K → K = ⊤) ∧
    (∀ g : CompactAutomorphism,
      g.equiv x' = x' → g.equiv y' = y' → g.equiv z' = z' →
      g = CompactAutomorphism.refl) := by
  have hδ : 0 ≤ δ := (norm_nonneg (x-x')).trans hdx
  have he := measured_displacement_error x y z x' y' z' observed ξ R δ hR herr
    hx hy hz hx' hy' hz' hdx hdy hdz
  have hE : 0 ≤ ξ+18*R^8*δ := by positivity
  have hm : ξ+18*R^8*δ < |observed| := by linarith
  exact ⟨scalar_sign_certificate observed (phi x' y' z') _ hE he hm,
    native_generation_of_measured_margin x' y' z' observed _ he hm⟩

 /-- Raw six-readout errors ε induce a scalar allowance ξ when 6ε≤ξ.
No frame premise is needed for this algebraic error statement. -/
 theorem six_readout_scalar_error
    (T : Glennie.Compact.Affine20.Triple)
    (noisy : Glennie.Compact.ReadoutRobustnessR01.Readouts) (ε ξ : ℝ)
    (herr : Glennie.Compact.ReadoutRobustnessR01.ErrorsAtMost noisy
      (Glennie.Compact.ReadoutRobustnessR01.exactReadouts T) ε)
    (hallowance : 6*ε ≤ ξ) :
    |Glennie.Compact.ReadoutRobustnessR01.noisyPhi noisy -
      phi (encoder (T 0)) (encoder (T 1)) (encoder (T 2))| ≤ ξ := by
  exact (Glennie.Compact.ReadoutRobustnessR01.phi_error T noisy ε herr).trans hallowance

 /-- Concrete readout-to-displacement consumer. ε, ξ, and δ have distinct premises. -/
 theorem six_readout_same_radius_sign_and_generation
    (T : Glennie.Compact.Affine20.Triple)
    (noisy : Glennie.Compact.ReadoutRobustnessR01.Readouts)
    (x' y' z' : Albert) (ε ξ R δ : ℝ) (hξ : 0 ≤ ξ) (hR : 0 ≤ R)
    (hreadout : Glennie.Compact.ReadoutRobustnessR01.ErrorsAtMost noisy
      (Glennie.Compact.ReadoutRobustnessR01.exactReadouts T) ε)
    (hallowance : 6*ε ≤ ξ)
    (hx : ‖encoder (T 0)‖ ≤ R) (hy : ‖encoder (T 1)‖ ≤ R)
    (hz : ‖encoder (T 2)‖ ≤ R)
    (hx' : ‖x'‖ ≤ R) (hy' : ‖y'‖ ≤ R) (hz' : ‖z'‖ ≤ R)
    (hdx : ‖encoder (T 0)-x'‖ ≤ δ) (hdy : ‖encoder (T 1)-y'‖ ≤ δ)
    (hdz : ‖encoder (T 2)-z'‖ ≤ δ)
    (hmargin : 18*R^8*δ <
      |Glennie.Compact.ReadoutRobustnessR01.noisyPhi noisy|-ξ) :
    ((Glennie.Compact.ReadoutRobustnessR01.noisyPhi noisy < 0 ∧ phi x' y' z' < 0) ∨
      (0 < Glennie.Compact.ReadoutRobustnessR01.noisyPhi noisy ∧ 0 < phi x' y' z')) ∧
    (∀ (K : Submodule ℝ Albert), (1 : Albert) ∈ K →
      (∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K) →
      x' ∈ K → y' ∈ K → z' ∈ K → K = ⊤) ∧
    (∀ g : CompactAutomorphism,
      g.equiv x' = x' → g.equiv y' = y' → g.equiv z' = z' →
      g = CompactAutomorphism.refl) := by
  exact same_radius_sign_and_generation (encoder (T 0)) (encoder (T 1))
    (encoder (T 2)) x' y' z'
    (Glennie.Compact.ReadoutRobustnessR01.noisyPhi noisy) ξ R δ hξ hR
    (six_readout_scalar_error T noisy ε ξ hreadout hallowance)
    hx hy hz hx' hy' hz' hdx hdy hdz hmargin

end
end Glennie.Compact.MeasuredMarginR01
