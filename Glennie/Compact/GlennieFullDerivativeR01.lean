/- Actual full native differential of Phi and its forward generation consequence.
All exposition and Lean code are AI-generated under Robert MacGregor's direction.
No novelty is asserted.
-/
module

public import Glennie.Compact.GlennieDerivativeGenerationR01
public import Glennie.Covariance
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

@[expose] public section
namespace Glennie.Compact.GlennieFullDerivativeR01

open Glennie
open Glennie.Compact.GlennieScalarPotentialR01
open Glennie.Compact.GlennieDerivativeR01
open Glennie.Compact.GlennieDerivativeGenerationR01

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-- The ordinary native product space, with its existing product topology. -/
abbrev NativeTriple := Albert × (Albert × Albert)

/-- The literal native scalar on three independently variable Albert inputs. -/
def phiTriple (p : NativeTriple) : ℝ := phi p.1 p.2.1 p.2.2

theorem phi_cyclic (x y z : Albert) : phi y z x = phi x y z := by
  rw [phi_swap_first_two z y x, phi_swap_first_third x y z, neg_neg]

theorem hasFDerivAt_phi_first (x y z : Albert) :
    HasFDerivAt (fun w : Albert => phi w y z)
      (nativeInnerContinuous (glennieVector y z x)) x := by
  have hfun : (fun w : Albert => phi w y z) = (fun w => phi y z w) := by
    funext w
    exact (phi_cyclic w y z).symm
  rw [hfun]
  exact hasFDerivAt_phi_third y z x

theorem hasFDerivAt_phi_second (x y z : Albert) :
    HasFDerivAt (fun w : Albert => phi x w z)
      (nativeInnerContinuous (glennieVector z x y)) y := by
  have hfun : (fun w : Albert => phi x w z) = (fun w => phi z x w) := by
    funext w
    exact phi_cyclic z x w
  rw [hfun]
  exact hasFDerivAt_phi_third z x y

/-! Joint differentiability is proved independently of the partial formulas. -/

theorem differentiable_jordan_triple {f g : NativeTriple → Albert}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    Differentiable ℝ (fun p => jordan (f p) (g p)) := by
  have hd := jordanContinuous.isBoundedBilinearMap.differentiable.comp (hf.prodMk hg)
  have hfun : ((fun q : Albert × Albert => jordanContinuous q.1 q.2) ∘
      (fun p : NativeTriple => (f p, g p))) =
      (fun p => jordan (f p) (g p)) := by
    funext p
    simp only [Function.comp_def, jordanContinuous_apply]
  rw [hfun] at hd
  exact hd

theorem differentiable_U_triple {f g : NativeTriple → Albert}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    Differentiable ℝ (fun p => U (f p) (g p)) := by
  have hfirst := differentiable_jordan_triple hf (differentiable_jordan_triple hf hg)
  have hsecond := differentiable_jordan_triple (differentiable_jordan_triple hf hf) hg
  have hd := (hfirst.const_smul (2 : ℝ)).sub hsecond
  have hfun :
      ((2 : ℝ) • (fun p : NativeTriple => jordan (f p) (jordan (f p) (g p))) -
        (fun p => jordan (jordan (f p) (f p)) (g p))) =
      (fun p => U (f p) (g p)) := by
    funext p
    simp only [Pi.sub_apply, Pi.smul_apply, U]
  rw [hfun] at hd
  exact hd

/-- Genuine joint differentiability of the original polynomial on all triples. -/
theorem differentiable_phiTriple : Differentiable ℝ phiTriple := by
  have hx : Differentiable ℝ (fun p : NativeTriple => p.1) := differentiable_fst
  have hyz : Differentiable ℝ (fun p : NativeTriple => p.2) := differentiable_snd
  have hy : Differentiable ℝ (fun p : NativeTriple => p.2.1) := hyz.fst
  have hz : Differentiable ℝ (fun p : NativeTriple => p.2.2) := hyz.snd
  have hleft := (differentiable_U_triple hx (differentiable_U_triple hy hz)).sub
    (differentiable_U_triple hy (differentiable_U_triple hx hz))
  have hright := differentiable_U_triple hz (differentiable_jordan_triple hx hy)
  have hd := nativeInnerContinuous.isBoundedBilinearMap.differentiable.comp
    (hleft.prodMk hright)
  have hfun :
      ((fun q : Albert × Albert => nativeInnerContinuous q.1 q.2) ∘
        (fun p : NativeTriple =>
          (U p.1 (U p.2.1 p.2.2) - U p.2.1 (U p.1 p.2.2),
            U p.2.2 (jordan p.1 p.2.1)))) = phiTriple := by
    funext p
    simp only [Function.comp_def, pairingContinuous_apply, phiTriple, phi]
  simp only [Pi.sub_apply] at hd
  rw [hfun] at hd
  exact hd

section StableFullDerivative
set_option backward.isDefEq.respectTransparency false
attribute [local instance 20000] Glennie.nativeRealSMulComm Glennie.nativeRealContinuousAdd Glennie.nativeRealContinuousSMul
/-- Three continuous linear trace pairings, with the actual cyclic G8 values. -/
def fullDerivative (x y z : Albert) : NativeTriple →L[ℝ] ℝ :=
  (nativeInnerContinuous (glennieVector y z x)).coprod
    ((nativeInnerContinuous (glennieVector z x y)).coprod
      (nativeInnerContinuous (glennieVector x y z)))
end StableFullDerivative

theorem fullDerivative_apply (x y z a b c : Albert) :
    fullDerivative x y z (a, b, c) =
      inner a (glennieVector y z x) + inner b (glennieVector z x y) +
        inner c (glennieVector x y z) := by
  simp only [fullDerivative, ContinuousLinearMap.coprod_apply, pairingContinuous_apply,
    inner_comm (glennieVector y z x) a, inner_comm (glennieVector z x y) b,
    inner_comm (glennieVector x y z) c, add_assoc]

/-- Identify the actual joint derivative by its three coordinate restrictions.
Joint differentiability above supplies existence; it is not inferred from
separate partial derivatives alone. -/
theorem hasFDerivAt_phiTriple (x y z : Albert) :
    HasFDerivAt phiTriple (fullDerivative x y z) (x, y, z) := by
  let D : NativeTriple →L[ℝ] ℝ := fderiv ℝ phiTriple (x, y, z)
  have hd : HasFDerivAt phiTriple D (x, y, z) :=
    (differentiable_phiTriple (x, y, z)).hasFDerivAt
  have hix : HasFDerivAt (fun w : Albert => (w, y, z))
      (ContinuousLinearMap.inl ℝ Albert (Albert × Albert)) x :=
    hasFDerivAt_prodMk_left (𝕜 := ℝ) x (y, z)
  have hx : HasFDerivAt (fun w : Albert => phi w y z)
      (D.comp (ContinuousLinearMap.inl ℝ Albert (Albert × Albert))) x := by
    simpa only [Function.comp_def, phiTriple] using
      (HasFDerivAt.comp (𝕜 := ℝ) (f := fun w : Albert => (w, y, z))
        (g := phiTriple) x hd hix)
  have hiyz : HasFDerivAt (fun q : Albert × Albert => (x, q))
      (ContinuousLinearMap.inr ℝ Albert (Albert × Albert)) (y, z) :=
    hasFDerivAt_prodMk_right (𝕜 := ℝ) x (y, z)
  have hyz : HasFDerivAt (fun q : Albert × Albert => phi x q.1 q.2)
      (D.comp (ContinuousLinearMap.inr ℝ Albert (Albert × Albert))) (y, z) := by
    simpa only [Function.comp_def, phiTriple] using
      (HasFDerivAt.comp (𝕜 := ℝ) (f := fun q : Albert × Albert => (x, q))
        (g := phiTriple) (y, z) hd hiyz)
  have hiy : HasFDerivAt (fun w : Albert => (w, z))
      (ContinuousLinearMap.inl ℝ Albert Albert) y :=
    hasFDerivAt_prodMk_left (𝕜 := ℝ) y z
  have hy : HasFDerivAt (fun w : Albert => phi x w z)
      ((D.comp (ContinuousLinearMap.inr ℝ Albert (Albert × Albert))).comp
        (ContinuousLinearMap.inl ℝ Albert Albert)) y := by
    simpa only [Function.comp_def] using
      (HasFDerivAt.comp (𝕜 := ℝ) (f := fun w : Albert => (w, z))
        (g := fun q : Albert × Albert => phi x q.1 q.2) y hyz hiy)
  have hiz : HasFDerivAt (fun w : Albert => (y, w))
      (ContinuousLinearMap.inr ℝ Albert Albert) z :=
    hasFDerivAt_prodMk_right (𝕜 := ℝ) y z
  have hz : HasFDerivAt (fun w : Albert => phi x y w)
      ((D.comp (ContinuousLinearMap.inr ℝ Albert (Albert × Albert))).comp
        (ContinuousLinearMap.inr ℝ Albert Albert)) z := by
    simpa only [Function.comp_def] using
      (HasFDerivAt.comp (𝕜 := ℝ) (f := fun w : Albert => (y, w))
        (g := fun q : Albert × Albert => phi x q.1 q.2) z hyz hiz)
  have h1 := hx.unique (hasFDerivAt_phi_first x y z)
  have h2 := hy.unique (hasFDerivAt_phi_second x y z)
  have h3 := hz.unique (hasFDerivAt_phi_third x y z)
  have h23 : D.comp (ContinuousLinearMap.inr ℝ Albert (Albert × Albert)) =
      (nativeInnerContinuous (glennieVector z x y)).coprod
        (nativeInnerContinuous (glennieVector x y z)) := by
    calc
      _ = ((D.comp (ContinuousLinearMap.inr ℝ Albert (Albert × Albert))).comp
            (ContinuousLinearMap.inl ℝ Albert Albert)).coprod
          ((D.comp (ContinuousLinearMap.inr ℝ Albert (Albert × Albert))).comp
            (ContinuousLinearMap.inr ℝ Albert Albert)) :=
        (ContinuousLinearMap.coprod_comp_inl_inr _).symm
      _ = _ := by rw [h2, h3]
  have hfull : D = fullDerivative x y z := by
    calc
      _ = (D.comp (ContinuousLinearMap.inl ℝ Albert (Albert × Albert))).coprod
          (D.comp (ContinuousLinearMap.inr ℝ Albert (Albert × Albert))) :=
        (ContinuousLinearMap.coprod_comp_inl_inr D).symm
      _ = _ := by simp only [h1, h23, fullDerivative]
  exact hd.congr_fderiv hfull

theorem fderiv_phiTriple (x y z : Albert) :
    fderiv ℝ phiTriple (x, y, z) = fullDerivative x y z :=
  (hasFDerivAt_phiTriple x y z).fderiv

/-- The full differential on an arbitrary native direction (a,b,c). -/
theorem fderiv_phiTriple_apply (x y z a b c : Albert) :
    fderiv ℝ phiTriple (x, y, z) (a, b, c) =
      inner a (glennieVector y z x) + inner b (glennieVector z x y) +
        inner c (glennieVector x y z) := by
  rw [fderiv_phiTriple, fullDerivative_apply]

/-- Full ambient criticality is equivalent to vanishing of all three cyclic
native G8 values. The forward proof tests the three coordinate directions. -/
theorem fderiv_phiTriple_eq_zero_iff (x y z : Albert) :
    fderiv ℝ phiTriple (x, y, z) = 0 ↔
      glennieVector y z x = 0 ∧ glennieVector z x y = 0 ∧
        glennieVector x y z = 0 := by
  constructor
  · intro hd
    have h1 : inner (glennieVector y z x) (glennieVector y z x) = 0 := by
      have h := fderiv_phiTriple_apply x y z (glennieVector y z x) 0 0
      simpa only [hd, zero_apply, inner_zero_left, add_zero] using h.symm
    have h2 : inner (glennieVector z x y) (glennieVector z x y) = 0 := by
      have h := fderiv_phiTriple_apply x y z 0 (glennieVector z x y) 0
      simpa only [hd, zero_apply, inner_zero_left, zero_add, add_zero] using h.symm
    have h3 : inner (glennieVector x y z) (glennieVector x y z) = 0 := by
      have h := fderiv_phiTriple_apply x y z 0 0 (glennieVector x y z)
      simpa only [hd, zero_apply, inner_zero_left, zero_add] using h.symm
    exact ⟨(inner_self_eq_zero _).mp h1, (inner_self_eq_zero _).mp h2,
      (inner_self_eq_zero _).mp h3⟩
  · rintro ⟨h1, h2, h3⟩
    apply ContinuousLinearMap.ext
    rintro ⟨a, b, c⟩
    simp only [fderiv_phiTriple_apply, h1, h2, h3, inner_zero_right, add_zero, zero_apply]

/-- A nonzero actual full differential forces full unital Jordan generation.
The three membership permutations use the proper-submodule theorem. -/
theorem eq_top_of_fderiv_phiTriple_ne_zero
    (K : Submodule ℝ Albert) (h1 : (1 : Albert) ∈ K)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (x y z : Albert) (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K)
    (hd : fderiv ℝ phiTriple (x, y, z) ≠ 0) : K = ⊤ := by
  by_contra hK
  apply hd
  apply (fderiv_phiTriple_eq_zero_iff x y z).mpr
  exact ⟨glennieVector_eq_zero_of_ne_top K h1 hJ hK y z x hy hz hx,
    glennieVector_eq_zero_of_ne_top K h1 hJ hK z x y hz hx hy,
    glennieVector_eq_zero_of_ne_top K h1 hJ hK x y z hx hy hz⟩

end
end Glennie.Compact.GlennieFullDerivativeR01
