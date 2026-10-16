/- Actual reference-automorphism transport of the unrestricted Jacobi kernel.
-/
module

public import AlbertRecognition.FixedFrame.FixedFrameGate
public import Mathlib.Algebra.Module.Torsion.Free

@[expose] public section
namespace AlbertRecognition.FixedFrame
noncomputable section
open Glennie

/-- Native projected multiplication on the complementary diagonal direction. -/
theorem KA_h0_frameD : KA (h 0) frameD = frameD := by
  rw [frameD_eq_h01, map_add, map_smul, map_smul, KA_h_self,
    KA_h_cross 0 1 (by decide)]
  module

/-- A literal inverse polynomial, checked on the actual 1+1+8+16 decomposition.
The three eigenvalues -1,1,-1/2 are nonzero; no invertibility is assumed. -/
theorem KA_h0_inverse_polynomial (x : V) :
    (2 : ℝ) • KA (h 0) (KA (h 0) (KA (h 0) x)) +
      KA (h 0) (KA (h 0) x) - (2 : ℝ) • KA (h 0) x = x := by
  have h01 (u : Octonion) : KA (h 0) (X01 u) = -(1/2 : ℝ) • X01 u := by
    simpa using KA_h_X01 0 u
  have h02 (u : Octonion) : KA (h 0) (X02 u) = -(1/2 : ℝ) • X02 u := by
    simpa using KA_h_X02 0 u
  have h12 (u : Octonion) : KA (h 0) (X12 u) = X12 u := by
    simpa using KA_h_X12 0 u
  rcases hs : (frameCoordinates x).2.2.2 with ⟨u,v⟩
  rw [frame_decompose x, hs, frameSpin_apply]
  simp only [map_add, map_smul, KA_h_self, KA_h0_frameD, h01, h02, h12]
  module

theorem KA_h0_injective : Function.Injective (KA (h 0)) := by
  intro x y hxy
  have hz : KA (h 0) (x-y) = 0 := by rw [map_sub, hxy, sub_self]
  have hinv := KA_h0_inverse_polynomial (x-y)
  simp only [hz, map_zero, smul_zero, add_zero, sub_zero] at hinv
  exact sub_eq_zero.mp hinv.symm

/-- The same literal polynomial supplies a preimage for every vector. -/
theorem KA_h0_surjective : Function.Surjective (KA (h 0)) := by
  intro y
  refine ⟨(2 : ℝ) • KA (h 0) (KA (h 0) y) + KA (h 0) y - (2 : ℝ) • y, ?_⟩
  simpa only [map_sub, map_add, map_smul] using KA_h0_inverse_polynomial y

theorem KA_h0_bijective : Function.Bijective (KA (h 0)) :=
  ⟨KA_h0_injective, KA_h0_surjective⟩

theorem h0_ne_zero : h 0 ≠ 0 := by
  intro hz
  have hd := congrArg (fun x : V => (x : Albert).d0) hz
  norm_num [h, e, unit] at hd

/-- Actual conjugation transports the injectivity of reference multiplication. -/
theorem KA_transported_h0_injective (g : CompactAutomorphism) :
    Function.Injective (KA (automorphismV g (h 0))) := by
  intro x y hxy
  have hpre : KA (h 0) ((automorphismV g).symm x) =
      KA (h 0) ((automorphismV g).symm y) := by
    apply (automorphismV g).injective
    simpa only [automorphismV_KA, LinearEquiv.apply_symm_apply] using hxy
  have h := congrArg (automorphismV g) (KA_h0_injective hpre)
  simpa only [LinearEquiv.apply_symm_apply] using h

/-- Pull back the arbitrary unknown, apply the proved fixed-frame gate, then
transport the equality back. There is no invariance assumption on B. -/
theorem transported_frame_constraint (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) (g : CompactAutomorphism) :
    ∃ c : ℝ, ∀ i : Fin 3,
      KB B (automorphismV g (h i)) = c • KA (automorphismV g (h i)) := by
  obtain ⟨c,hc⟩ := fixedFrame_gate_of_A_q_zero
    (pullbackCubic (automorphismV g) B) (A_q_pullback_zero g B hB)
  refine ⟨c, ?_⟩
  intro i
  apply LinearMap.ext
  intro z
  obtain ⟨w,rfl⟩ := (automorphismV g).surjective z
  calc
    KB B (automorphismV g (h i)) (automorphismV g w) =
        automorphismV g (KB (pullbackCubic (automorphismV g) B) (h i) w) :=
      (automorphismV_KB_pullback g B (h i) w).symm
    _ = automorphismV g (c • KA (h i) w) := by
      exact congrArg (automorphismV g) (LinearMap.congr_fun (hc i) w)
    _ = c • KA (automorphismV g (h i)) (automorphismV g w) := by
      rw [map_smul, automorphismV_KA]

/-- Nonzero transported directions force their scalar to agree with the base
scalar, by product symmetry and the proved native injectivity at h0. -/
theorem transported_scalar_eq (B : SymmetricCubic) (g : CompactAutomorphism)
    (b c : ℝ) (hb : KB B (h 0) = b • KA (h 0))
    (hc : KB B (automorphismV g (h 0)) = c • KA (automorphismV g (h 0))) :
    b = c := by
  have hu : automorphismV g (h 0) ≠ 0 := by
    intro hz
    apply h0_ne_zero
    apply (automorphismV g).injective
    simpa only [map_zero] using hz
  have hv : KA (h 0) (automorphismV g (h 0)) ≠ 0 := by
    intro hz
    apply hu
    apply KA_h0_injective
    simpa only [map_zero] using hz
  have heq : b • KA (h 0) (automorphismV g (h 0)) =
      c • KA (h 0) (automorphismV g (h 0)) := by
    calc
      _ = KB B (h 0) (automorphismV g (h 0)) :=
        (LinearMap.congr_fun hb _).symm
      _ = KB B (automorphismV g (h 0)) (h 0) := KB_comm B _ _
      _ = c • KA (automorphismV g (h 0)) (h 0) := LinearMap.congr_fun hc _
      _ = _ := congrArg (fun x : V => c • x) (KA_comm _ _)
  exact smul_left_injective ℝ hv heq

/-- One scalar works on every actual transported reference frame. The sole
hypothesis is the original unrestricted Jacobi equation. -/
theorem common_scalar_on_reference_frames (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) :
    ∃ b : ℝ, ∀ g : CompactAutomorphism, ∀ i : Fin 3,
      KB B (automorphismV g (h i)) = b • KA (automorphismV g (h i)) := by
  obtain ⟨b,hb⟩ := fixedFrame_gate_of_A_q_zero B hB
  refine ⟨b, ?_⟩
  intro g
  obtain ⟨c,hc⟩ := transported_frame_constraint B hB g
  have hbc : b = c := transported_scalar_eq B g b c (hb 0) (hc 0)
  rw [← hbc] at hc
  exact hc

end
end AlbertRecognition.FixedFrame
