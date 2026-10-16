module

public import Glennie.Compact.LocalContrast

@[expose] public section
namespace Glennie.Compact.LocalReconstruction
noncomputable section

open Glennie
open Glennie.Compact.Affine20 Glennie.Compact.FlatOrbit
open Glennie.Compact.NearbyOrbits Glennie.Compact.NearbyOrbitsClosed
open Glennie.Compact.NativeQFamilyLedger Glennie.Compact.LocalContrast
open Glennie.Compact.Sections

def SameScoreSign (T S : Triple) : Prop :=
  (score T < 0 ∧ score S < 0) ∨ (0 < score T ∧ 0 < score S)

/-- The existing local fibre theorem gives a finite-observation orbit test on actual frames. -/
theorem nearby_q26_score_complete :
    ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧
      encode20 (ledger54 flatBase) ∈ V ∧
      ∀ T S : Triple, (∀ a, Frame (T a)) → (∀ a, Frame (S a)) →
        encode20 (ledger54 T) ∈ V →
        score T ≠ 0 ∧
        ((∃ k : CompactAutomorphism, mapAtoms k S = T) ↔
          q26 T = q26 S ∧ SameScoreSign T S) := by
  obtain ⟨V, hVopen, hbase, secPos, secNeg, _hcP, _hcN, _hfP, _hfN,
      _heP, _heN, _hlP, _hlN, hpP, hpN, hcover, _hdisj, h20⟩ :=
    nearby_fibres_two_orbits_unconditional
  refine ⟨V, hVopen, hbase, ?_⟩
  intro T S hT hS hb
  let b := encode20 (ledger54 T)
  have hTf : T ∈ fibre54 b := by
    rw [← h20 b hb]
    exact ⟨hT, rfl⟩
  have hTorbit : T ∈ autOrbit (secNeg b) ∨ T ∈ autOrbit (secPos b) := by
    change T ∈ autOrbit (secNeg b) ∪ autOrbit (secPos b)
    rw [← hcover b hb]
    exact hTf
  have hscoreNeg (X : Triple) (hX : X ∈ autOrbit (secNeg b)) : score X < 0 := by
    rw [score_eq_two_phi, phiOf_eq_of_mem_autOrbit hX]
    linarith [hpN b hb]
  have hscorePos (X : Triple) (hX : X ∈ autOrbit (secPos b)) : 0 < score X := by
    rw [score_eq_two_phi, phiOf_eq_of_mem_autOrbit hX]
    linarith [hpP b hb]
  have hscoreT : score T ≠ 0 := by
    rcases hTorbit with hN | hP
    · exact ne_of_lt (hscoreNeg T hN)
    · exact ne_of_gt (hscorePos T hP)
  refine ⟨hscoreT, ?_⟩
  constructor
  · rintro ⟨k, hk⟩
    have hL : ledger54 T = ledger54 S := by
      rw [← hk, ledger54_map]
    have hq : q26 T = q26 S :=
      (q26_eq_iff_ledger54_eq T S hT hS).mpr hL
    have hphi : phiOf T = phiOf S :=
      phiOf_eq_of_mem_autOrbit (show T ∈ autOrbit S from ⟨k, hk⟩)
    have hscore : score T = score S := by
      rw [score_eq_two_phi, score_eq_two_phi, hphi]
    refine ⟨hq, ?_⟩
    rcases lt_trichotomy (score T) 0 with hNeg | hZero | hPos
    · exact Or.inl ⟨hNeg, by rwa [← hscore]⟩
    · exact False.elim (hscoreT hZero)
    · exact Or.inr ⟨hPos, by rwa [← hscore]⟩
  · rintro ⟨hq, hsign⟩
    have hL : ledger54 T = ledger54 S :=
      (q26_eq_iff_ledger54_eq T S hT hS).mp hq
    have hSf : S ∈ fibre54 b := by
      rw [← h20 b hb]
      refine ⟨hS, ?_⟩
      exact hL.symm ▸ rfl
    have hSorbit : S ∈ autOrbit (secNeg b) ∨ S ∈ autOrbit (secPos b) := by
      change S ∈ autOrbit (secNeg b) ∪ autOrbit (secPos b)
      rw [← hcover b hb]
      exact hSf
    rcases hTorbit with hTN | hTP
    · have hTneg := hscoreNeg T hTN
      have hSneg : score S < 0 := by
        rcases hsign with h | h
        · exact h.2
        · linarith [h.1]
      rcases hSorbit with hSN | hSP
      · change T ∈ autOrbit S
        rw [autOrbit_eq_of_mem hSN]
        exact hTN
      · linarith [hscorePos S hSP]
    · have hTpos := hscorePos T hTP
      have hSpos : 0 < score S := by
        rcases hsign with h | h
        · linarith [h.1]
        · exact h.2
      rcases hSorbit with hSN | hSP
      · linarith [hscoreNeg S hSN]
      · change T ∈ autOrbit S
        rw [autOrbit_eq_of_mem hSP]
        exact hTP

end
end Glennie.Compact.LocalReconstruction
