module
public import Glennie.Compact.NativeQ20AdapterR01
public import Glennie.Compact.ReadoutRobustnessR01

@[expose] public section
namespace Glennie.Compact.CompactNoisyRecoveryR01
noncomputable section
open Glennie.Compact.LocalOrbitQuotientR01
open Glennie.Compact.NativeQ20AdapterR01
open Glennie.Compact.ReadoutRobustnessR01
open Glennie.Compact.Affine20
open Glennie.Compact.Sections
set_option autoImplicit false

/-- A strict six-readout score margin identifies the existing local orbit sheet. -/
theorem sheet_eq_noisy_sign (d : LocalData) (T : Admitted d)
    (noisy : Readouts) (ε : ℝ) (hε : 0 ≤ ε)
    (hErr : ErrorsAtMost noisy (exactReadouts T.1) ε)
    (hMargin : 12 * ε < |weightedScore noisy|) :
    sheet d T = decide (0 < weightedScore noisy) := by
  rcases sign_certificate T.1 noisy ε hε hErr hMargin with ⟨hn, hphi⟩ | ⟨hp, hphi⟩
  · have hs : sheet d T = false := (sheet_false_iff d T).2 hphi
    have hscore : decide (0 < weightedScore noisy) = false := by
      simp [not_lt.mpr hn.le]
    exact hs.trans hscore.symm
  · have hs : sheet d T = true := (sheet_true_iff d T).2 hphi
    have hscore : decide (0 < weightedScore noisy) = true := by simp [hp]
    exact hs.trans hscore.symm

/-- A certified feasible nearby chart and a strict noisy sign select a close
representative after one actual simultaneous automorphism. -/
theorem compact_noisy_feasible_recovery (d : LocalData)
    (K : Set d.V) (hK : IsCompact K) (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ η > 0, ∀ T : Admitted d, chart d T ∈ K →
      ∀ b : d.V, b ∈ K → dist (chart d T) b < η →
      ∀ noisy : Readouts, ∀ ε : ℝ, 0 ≤ ε →
        ErrorsAtMost noisy (exactReadouts T.1) ε →
        12 * ε < |weightedScore noisy| →
        ∃ g : Glennie.CompactAutomorphism,
          ‖T.1 - mapAtoms g (branchSection d b (decide (0 < weightedScore noisy)))‖ < ζ := by
  obtain ⟨η, hη, hrec⟩ := compact_feasible_recovery d K hK ζ hζ
  refine ⟨η, hη, ?_⟩
  intro T hT b hb hdist noisy ε hε hErr hMargin
  obtain ⟨g, hg⟩ := hrec T hT b hb hdist
  refine ⟨g, ?_⟩
  rw [sheet_eq_noisy_sign d T noisy ε hε hErr hMargin] at hg
  exact hg

/-- A uniform native Phi margin gives the correct noisy sign before the
stronger a posteriori score test is guaranteed to fire. -/
theorem sheet_eq_of_uniform_phi_margin (d : LocalData) (T : Admitted d)
    (m : ℝ) (hm : m ≤ |phiOf T.1|)
    (noisy : Readouts) (ε : ℝ)
    (hErr : ErrorsAtMost noisy (exactReadouts T.1) ε)
    (hsmall : 6 * ε < m) :
    sheet d T = decide (0 < weightedScore noisy) := by
  have herr := phi_error T.1 noisy ε hErr
  rcases lt_trichotomy (phiOf T.1) 0 with hn | heq | hp
  · have hphi : phiOf T.1 ≤ -m := by rw [abs_of_neg hn] at hm; linarith
    have hu := (abs_le.mp herr).2
    have hscore : weightedScore noisy < 0 := by
      dsimp [noisyPhi] at hu
      linarith
    have hs : sheet d T = false := (sheet_false_iff d T).2 hn
    have hnoisy : decide (0 < weightedScore noisy) = false := by
      simp [not_lt.mpr hscore.le]
    exact hs.trans hnoisy.symm
  · exact False.elim ((phi_ne_zero d T) heq)
  · have hphi : m ≤ phiOf T.1 := by simpa [abs_of_pos hp] using hm
    have hl := (abs_le.mp herr).1
    have hscore : 0 < weightedScore noisy := by
      dsimp [noisyPhi] at hl
      linarith
    have hs : sheet d T = true := (sheet_true_iff d T).2 hp
    have hnoisy : decide (0 < weightedScore noisy) = true := by simp [hscore]
    exact hs.trans hnoisy.symm

/-- The stronger uniform inequality guarantees that the strict a posteriori
six-readout test fires for every permitted noise realization. -/
theorem posterior_fires_of_uniform_phi_margin (T : Triple)
    (m : ℝ) (hm : m ≤ |phiOf T|)
    (noisy : Readouts) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hErr : ErrorsAtMost noisy (exactReadouts T) ε)
    (hsmall : 12 * ε < m) :
    12 * ε < |weightedScore noisy| := by
  have herr := phi_error T noisy ε hErr
  rcases le_total 0 (phiOf T) with hp | hn
  · have hphi : m ≤ phiOf T := by simpa [abs_of_nonneg hp] using hm
    have hl := (abs_le.mp herr).1
    have hscore : 12 * ε < weightedScore noisy := by
      dsimp [noisyPhi] at hl
      linarith
    rw [abs_of_pos (by linarith : 0 < weightedScore noisy)]
    exact hscore
  · have hphi : phiOf T ≤ -m := by rw [abs_of_nonpos hn] at hm; linarith
    have hu := (abs_le.mp herr).2
    have hscore : weightedScore noisy < -(12 * ε) := by
      dsimp [noisyPhi] at hu
      linarith
    rw [abs_of_neg (by linarith : weightedScore noisy < 0)]
    linarith

/-- One compact feasible region supplies both distinct noise thresholds.
Here `6 ε < m` corresponds to `12 ε < 2m`; `12 ε < m` to `24 ε < 2m`. -/
theorem compact_noise_thresholds (d : LocalData) (K : Set d.V)
    (hK : IsCompact K) :
    ∃ m > 0, ∀ T : Admitted d, chart d T ∈ K →
      ∀ noisy : Readouts, ∀ ε : ℝ,
        0 ≤ ε →
        ErrorsAtMost noisy (exactReadouts T.1) ε →
        (6 * ε < m → sheet d T = decide (0 < weightedScore noisy)) ∧
        (12 * ε < m → 12 * ε < |weightedScore noisy|) := by
  obtain ⟨m, hm, hbound⟩ := compact_response_margin d K hK
  refine ⟨m, hm, ?_⟩
  intro T hT noisy ε hε hErr
  have hb := hbound T hT
  exact ⟨sheet_eq_of_uniform_phi_margin d T m hb noisy ε hErr,
    posterior_fires_of_uniform_phi_margin T.1 m hb noisy ε hε hErr⟩

end
end Glennie.Compact.CompactNoisyRecoveryR01
