/- Consequences of native unital generation.
No generation/span premise. -/
module
public import Glennie.NativeGenerationEndpointR01
public import Glennie.Compact.InnerDerivation
public import Glennie.Compact.LocalReconstruction

@[expose] public section
namespace Glennie.NativeGenerationStabilizersR01
noncomputable section
open Glennie.NativeGenerationEndpointR01
open Glennie.Compact
open Glennie.Compact.Affine20
open Glennie.Compact.Sections

/-- Actual native automorphisms are determined by their linear equivalence. -/
theorem automorphism_ext {g h : CompactAutomorphism} (he : g.equiv = h.equiv) : g = h := by
  cases g
  cases h
  cases he
  rfl

def fixedSubmodule (g : CompactAutomorphism) : Submodule ℝ Albert where
  carrier := {t | g.equiv t = t}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    simp only [Set.mem_setOf_eq] at hp hq ⊢
    rw [map_add, hp, hq]
  smul_mem' := by
    intro r p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    rw [map_smul, hp]

theorem automorphism_fixes_all_of_phi_ne_zero
    (g : CompactAutomorphism) (x y z : Albert)
    (hphi : phi x y z ≠ 0)
    (hx : g.equiv x = x) (hy : g.equiv y = y) (hz : g.equiv z = z) :
    ∀ t : Albert, g.equiv t = t := by
  have hK : fixedSubmodule g = ⊤ := eq_top_of_phi_ne_zero (fixedSubmodule g)
    g.map_unit
    (by
      intro p hp q hq
      change g.equiv p = p at hp
      change g.equiv q = q at hq
      change g.equiv (jordan p q) = jordan p q
      rw [g.map_jordan, hp, hq])
    x y z hx hy hz hphi
  intro t
  have ht : t ∈ fixedSubmodule g := by rw [hK]; trivial
  exact ht

theorem automorphism_eq_refl_of_phi_ne_zero
    (g : CompactAutomorphism) (x y z : Albert)
    (hphi : phi x y z ≠ 0)
    (hx : g.equiv x = x) (hy : g.equiv y = y) (hz : g.equiv z = z) :
    g = CompactAutomorphism.refl := by
  apply automorphism_ext
  apply LinearEquiv.ext
  exact automorphism_fixes_all_of_phi_ne_zero g x y z hphi hx hy hz

/-- No trace-free condition is needed for this derivation consequence. -/
theorem derivation_eq_zero_of_phi_ne_zero
    (D : Albert →ₗ[ℝ] Albert) (hD : IsJordanDerivation D)
    (x y z : Albert) (hphi : phi x y z ≠ 0)
    (hx : D x = 0) (hy : D y = 0) (hz : D z = 0) : D = 0 := by
  have hK : LinearMap.ker D = ⊤ := eq_top_of_phi_ne_zero (LinearMap.ker D)
    hD.map_one
    (by
      intro p hp q hq
      change D p = 0 at hp
      change D q = 0 at hq
      change D (jordan p q) = 0
      rw [hD p q, hp, hq]
      simp)
    x y z hx hy hz hphi
  apply LinearMap.ext
  intro t
  have ht : t ∈ LinearMap.ker D := by rw [hK]; trivial
  exact ht

/-- The complete actual automorphism stabilizer of the labelled atoms is trivial. -/
theorem ordered_atoms_stabilizer_eq_refl
    (T : Triple) (hphi : phiOf T ≠ 0) (g : CompactAutomorphism)
    (hfix : mapAtoms g T = T) : g = CompactAutomorphism.refl := by
  have hf : ∀ a i, g.equiv (T a i) = T a i := by
    intro a i
    exact congrFun (congrFun hfix a) i
  apply automorphism_eq_refl_of_phi_ne_zero g
    (encoder (T 0)) (encoder (T 1)) (encoder (T 2)) hphi
  all_goals simp only [encoder, map_sub, hf]

theorem ordered_atoms_derivation_eq_zero
    (T : Triple) (hphi : phiOf T ≠ 0)
    (D : Albert →ₗ[ℝ] Albert) (hD : IsJordanDerivation D)
    (hkill : ∀ a i, D (T a i) = 0) : D = 0 := by
  apply derivation_eq_zero_of_phi_ne_zero D hD
    (encoder (T 0)) (encoder (T 1)) (encoder (T 2)) hphi
  all_goals simp only [encoder, map_sub, hkill, sub_zero]

/-- This applies directly to the nonzero score produced by the existing
local ordered-frame finite-observation theorem. -/
theorem ordered_stabilizers_of_score_ne_zero
    (T : Triple) (hscore : Glennie.Compact.LocalContrast.score T ≠ 0) :
    (∀ g : CompactAutomorphism, mapAtoms g T = T → g = CompactAutomorphism.refl) ∧
    (∀ D : Albert →ₗ[ℝ] Albert, IsJordanDerivation D →
      (∀ a i, D (T a i) = 0) → D = 0) := by
  have hp : phiOf T ≠ 0 := by
    intro hz
    apply hscore
    rw [Glennie.Compact.LocalContrast.score_eq_two_phi, hz, mul_zero]
  exact ⟨fun g hg => ordered_atoms_stabilizer_eq_refl T hp g hg,
    fun D hD hk => ordered_atoms_derivation_eq_zero T hp D hD hk⟩

end
end Glennie.NativeGenerationStabilizersR01
