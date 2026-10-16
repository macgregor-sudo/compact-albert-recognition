/- Third-slot noncriticality implies native unital Jordan generation.
All exposition and Lean code are AI-generated under Robert MacGregor's direction.
No novelty is asserted.
-/
module

public import Glennie.Compact.GlennieDerivativeR01
public import Glennie.NativeGenerationEndpointR01

@[expose] public section
namespace Glennie.Compact.GlennieDerivativeGenerationR01

open Glennie
open Glennie.Compact.GlennieScalarPotentialR01
open Glennie.Compact.GlennieDerivativeR01
open Glennie.NativeGenerationEndpointR01

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
-- Keep the native/Hilbert inherited-instance convention of the provider.
set_option backward.isDefEq.respectTransparency false

/-! Polynomial closure uses only the submodule laws and native Jordan closure.
The unit enters later, through the existing scalar-generation theorem. -/

theorem U_mem (K : Submodule ℝ Albert)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (a b : Albert) (ha : a ∈ K) (hb : b ∈ K) : U a b ∈ K := by
  rw [U]
  exact K.sub_mem
    (K.smul_mem (2 : ℝ) (hJ a ha (jordan a b) (hJ a ha b hb)))
    (hJ (jordan a a) (hJ a ha a ha) b hb)

theorem commU_mem (K : Submodule ℝ Albert)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (x y z : Albert) (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K) :
    commU x y z ∈ K := by
  rw [commU]
  exact K.sub_mem
    (U_mem K hJ x (U y z) hx (U_mem K hJ y z hy hz))
    (U_mem K hJ y (U x z) hy (U_mem K hJ x z hx hz))

theorem doubledTriple_mem (K : Submodule ℝ Albert)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (a b c : Albert) (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) :
    doubledTriple a b c ∈ K := by
  rw [doubledTriple]
  exact K.smul_mem (2 : ℝ) (K.sub_mem
    (K.add_mem
      (hJ a ha (jordan b c) (hJ b hb c hc))
      (hJ (jordan a b) (hJ a ha b hb) c hc))
    (hJ (jordan a c) (hJ a ha c hc) b hb))

/-- The actual native gradient vector stays in any Jordan-product-closed
real submodule containing its three arguments. -/
theorem glennieVector_mem (K : Submodule ℝ Albert)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (x y z : Albert) (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K) :
    glennieVector x y z ∈ K := by
  have hp : jordan x y ∈ K := hJ x hx y hy
  rw [glennieVector]
  exact K.sub_mem
    (doubledTriple_mem K hJ (commU x y z) z (jordan x y)
      (commU_mem K hJ x y z hx hy hz) hz hp)
    (commU_mem K hJ x y (U z (jordan x y)) hx hy
      (U_mem K hJ z (jordan x y) hz hp))

/-! Proper unital submodules force scalar and third-slot gradient vanishing. -/

/-- Vanishing is deduced from the retained scalar-generation theorem.
It is not supplied as a property of the submodule. -/
theorem phi_eq_zero_of_ne_top
    (K : Submodule ℝ Albert) (h1 : (1 : Albert) ∈ K)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K) (hK : K ≠ ⊤)
    (x y z : Albert) (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K) :
    phi x y z = 0 := by
  by_contra hphi
  exact hK (eq_top_of_phi_ne_zero K h1 hJ x y z hx hy hz hphi)

/-- Differentiate the identically zero affine curve in the native G8 direction.
Its derivative is the raw positive pairing of G8 with itself. -/
theorem glennieVector_eq_zero_of_ne_top
    (K : Submodule ℝ Albert) (h1 : (1 : Albert) ∈ K)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K) (hK : K ≠ ⊤)
    (x y z : Albert) (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K) :
    glennieVector x y z = 0 := by
  have hg : glennieVector x y z ∈ K := glennieVector_mem K hJ x y z hx hy hz
  have hcurve :
      (fun t : ℝ => phi x y (z + t • glennieVector x y z)) =
      (fun _ : ℝ => (0 : ℝ)) := by
    funext t
    exact phi_eq_zero_of_ne_top K h1 hJ hK x y
      (z + t • glennieVector x y z) hx hy (K.add_mem hz (K.smul_mem t hg))
  have hd := hasDerivAt_phi_third_affine x y z (glennieVector x y z)
  rw [hcurve] at hd
  have hzero : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 (0 : ℝ) :=
    hasDerivAt_const (0 : ℝ) (0 : ℝ)
  exact (inner_self_eq_zero (glennieVector x y z)).mp (hd.unique hzero)

/-! Definition-free generation endpoints for arbitrary native triples. -/

/-- A nonzero native G8 value forces every containing unital,
Jordan-product-closed real submodule to be the entire Albert space. -/
theorem eq_top_of_glennieVector_ne_zero
    (K : Submodule ℝ Albert) (h1 : (1 : Albert) ∈ K)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (x y z : Albert) (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K)
    (hg : glennieVector x y z ≠ 0) : K = ⊤ := by
  by_contra hK
  exact hg (glennieVector_eq_zero_of_ne_top K h1 hJ hK x y z hx hy hz)

/-- Actual third-slot noncriticality suffices for full unital Jordan generation.
No nonzero-Phi assumption or full-triple derivative premise is required. -/
theorem eq_top_of_fderiv_phi_third_ne_zero
    (K : Submodule ℝ Albert) (h1 : (1 : Albert) ∈ K)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (x y z : Albert) (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K)
    (hd : fderiv ℝ (fun w : Albert => phi x y w) z ≠ 0) :
    K = ⊤ := by
  apply eq_top_of_glennieVector_ne_zero K h1 hJ x y z hx hy hz
  intro hg
  exact hd ((fderiv_phi_third_eq_zero_iff x y z).mpr hg)

end
end Glennie.Compact.GlennieDerivativeGenerationR01
