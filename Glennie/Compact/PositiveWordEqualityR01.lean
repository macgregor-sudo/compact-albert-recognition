/- Bounded proof of the pure native 192-label equality.
No positivity or operational realization statement. -/
module
public import Glennie.Compact.PositiveWordDefinitionR01
public import Glennie.Compact.PositiveCommutatorR01

@[expose] public section
namespace Glennie.Compact.PositiveWordEqualityR01
open Glennie Glennie.Compact.OperationalPhi
open Glennie.Compact.PositiveFilterAlgebraR01
open Glennie.Compact.PositiveWordBookkeepingR01
open Glennie.Compact.PositiveWordLayersR01
open Glennie.Compact.PositiveWordEndpointR01
open Glennie.Compact.PositiveWordDefinitionR01
noncomputable section
set_option autoImplicit false

private def readout (t : Albert) (F : Albert →ₗ[ℝ] Albert) : Albert →ₗ[ℝ] ℝ where
  toFun v := inner t (F v)
  map_add' a b := by rw [map_add, inner_add_right]
  map_smul' r a := by rw [map_smul, inner_smul_right]; rfl

private theorem readout_apply (t v : Albert) (F : Albert →ₗ[ℝ] Albert) :
    readout t F v = inner t (F v) := rfl

private theorem weighted_readout_sum {ι : Type*} [Fintype ι]
    (t : Albert) (F : Albert →ₗ[ℝ] Albert) (C : ℝ)
    (a : ι → ℝ) (v : ι → Albert) :
    (∑ i, C * a i * inner t (F (v i))) =
      C * inner t (F (∑ i, a i • v i)) := by
  have h : (∑ i, a i * inner t (F (v i))) =
      inner t (F (∑ i, a i • v i)) := by
    change (∑ i, a i * readout t F (v i)) = readout t F (∑ i, a i • v i)
    simp only [map_sum, map_smul, smul_eq_mul]
  calc
    _ = C * (∑ i, a i * inner t (F (v i))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by rw [h]

def outerLinear (x y : Albert) (o sy sx : Bool) : Albert →ₗ[ℝ] Albert :=
  if o then (filterLinear x sx).comp (filterLinear y sy)
  else (filterLinear y sy).comp (filterLinear x sx)

theorem outerLinear_apply (x y v : Albert) (o sy sx : Bool) :
    outerLinear x y o sy sx v =
      if o then filter x sx (filter y sy v) else filter y sy (filter x sx v) := by
  cases o <;> simp [outerLinear, filterLinear]

theorem word_factor (x y z v : Albert) (o sy sx : Bool) (i : Fin 3) (l : Bool) :
    word x y z v o sy sx i l =
      ((outerLinear x y o sy sx).comp (middleLinear z i)) (filter x l v) := by
  cases o <;> simp [word, wordLinear, outerLinear, filterLinear]

/-- Four scalar endpoint terms, with all five outer choices held fixed. -/
theorem collapse_endpoints (p q r : Fin 3 → Albert)
    (o sy sx : Bool) (i : Fin 3) (l : Bool) :
    (∑ k : Bool, ∑ j : Bool,
      coefficient o i l k j * inner (endpoint r k)
        (word (encoder p) (encoder q) (encoder r) (endpoint q j) o sy sx i l)) =
    (4 * sign o * middleCoeff i * sign l) *
      inner (encoder r)
        (word (encoder p) (encoder q) (encoder r) (encoder q) o sy sx i l) := by
  let C := 4 * sign o * middleCoeff i * sign l
  calc
    _ = C * (∑ k : Bool, ∑ j : Bool,
        sign k * sign j * inner (endpoint r k)
          (wordLinear (encoder p) (encoder q) (encoder r) o sy sx i l (endpoint q j))) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro j hj
      dsimp only [C, coefficient, word]
      ring
    _ = _ := by
      rw [signed_endpoint_pairing]
      rfl

/-- Two signed filters collapse to the native Jordan input. -/
theorem collapse_signed_filter (x y z t v : Albert) (o sy sx : Bool) (i : Fin 3) :
    (∑ l : Bool, (4 * sign o * middleCoeff i * sign l) *
      inner t (word x y z v o sy sx i l)) =
    (4 * sign o * middleCoeff i) *
      inner t (outerLinear x y o sy sx (middleLinear z i (jordan x v))) := by
  simp only [word_factor]
  rw [weighted_readout_sum t ((outerLinear x y o sy sx).comp (middleLinear z i))
    (4 * sign o * middleCoeff i) sign (fun l => filter x l v), signed_filter_apply]
  rfl

/-- Three middle choices collapse to U_z. -/
theorem collapse_middle (x y z t v : Albert) (o sy sx : Bool) :
    (∑ i : Fin 3, (4 * sign o * middleCoeff i) *
      inner t (outerLinear x y o sy sx (middleLinear z i v))) =
    (4 * sign o) * inner t (outerLinear x y o sy sx (U z v)) := by
  simp only [middleLinear_apply]
  rw [weighted_readout_sum t (outerLinear x y o sy sx)
    (4 * sign o) middleCoeff (fun i => middle z v i), middle_sum]

/-- Eight ordered filter terms collapse with the native adjoint commutator sign. -/
theorem collapse_commutator (x y t v : Albert) :
    (∑ o : Bool, ∑ sy : Bool, ∑ sx : Bool,
      (4 * sign o) * inner t (outerLinear x y o sy sx v)) =
    inner t (U y (U x v) - U x (U y v)) := by
  have h := congrArg (inner t)
    (Glennie.Compact.PositiveCommutatorR01.commutator_filter_expansion x y v)
  simp only [inner_smul_right, inner_add_right, inner_sub_right] at h
  rw [inner_sub_right, h]
  simp only [Fintype.sum_bool]
  simp [outerLinear_apply, sign]
  ring

/-- The product index is flattened once; native maps remain opaque. -/
theorem expanded_endpoint_collapsed (p q r : Fin 3 → Albert) :
    expanded p q r =
      ∑ o : Bool, ∑ sy : Bool, ∑ sx : Bool, ∑ i : Fin 3, ∑ l : Bool,
        (4 * sign o * middleCoeff i * sign l) *
          inner (encoder r)
            (word (encoder p) (encoder q) (encoder r) (encoder q) o sy sx i l) := by
  simp only [expanded, Fintype.sum_prod_type, labelCoefficient, evaluation]
  simp_rw [collapse_endpoints]

/-- Exact algebraic equality for arbitrary endpoint maps; no Frame or trace premise. -/
theorem expanded_eq_phi (p q r : Fin 3 → Albert) :
    expanded p q r = phi (encoder p) (encoder q) (encoder r) := by
  rw [expanded_endpoint_collapsed]
  simp_rw [collapse_signed_filter, collapse_middle]
  rw [collapse_commutator]
  exact (phi_eq_contrast (encoder p) (encoder q) (encoder r)).symm

end
end Glennie.Compact.PositiveWordEqualityR01
