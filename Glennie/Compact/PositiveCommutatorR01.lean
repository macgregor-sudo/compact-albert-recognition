module

public import Glennie.Compact.PositiveWordLayersR01

/- The commutator is normalized over abstract linear maps, then specialized to native U. -/
@[expose] public section
namespace Glennie.Compact.PositiveCommutatorR01
open Glennie
open Glennie.Compact.PositiveFilterAlgebraR01
open Glennie.Compact.PositiveWordLayersR01
noncomputable section
set_option autoImplicit false

private def quadraticFromFilters {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P M : E →ₗ[ℝ] E) : E →ₗ[ℝ] E :=
  (2 : ℝ) • P + (2 : ℝ) • M - LinearMap.id

/-- All normalization happens with abstract maps and abstract module elements.
    The two identity-map terms cancel before any native specialization. -/
private theorem abstract_commutator {E : Type*} [AddCommGroup E] [Module ℝ E]
    (xp xm yp ym : E →ₗ[ℝ] E) (v : E) :
    quadraticFromFilters yp ym (quadraticFromFilters xp xm v) -
      quadraticFromFilters xp xm (quadraticFromFilters yp ym v) =
    (4 : ℝ) •
      (yp (xp v) - xp (yp v) +
       (yp (xm v) - xm (yp v)) +
       (ym (xp v) - xp (ym v)) +
       (ym (xm v) - xm (ym v))) := by
  simp only [quadraticFromFilters, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.id_apply, map_add, map_sub, map_smul]
  module

private theorem filterLinear_apply (w v : Albert) (s : Bool) :
    filterLinear w s v = filter w s v := rfl

private theorem native_quadratic_apply (w v : Albert) :
    quadraticFromFilters (filterLinear w false) (filterLinear w true) v = U w v := by
  simpa only [quadraticFromFilters, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.id_apply, filterLinear_apply] using
      (U_filter_decomposition w v).symm

/-- Native adjoint order [U_y,U_x], with eight signed ordered filter words. -/
theorem commutator_filter_expansion (x y v : Albert) :
    U y (U x v) - U x (U y v) = (4 : ℝ) •
      (filter y false (filter x false v) - filter x false (filter y false v) +
       (filter y false (filter x true v) - filter x true (filter y false v)) +
       (filter y true (filter x false v) - filter x false (filter y true v)) +
       (filter y true (filter x true v) - filter x true (filter y true v))) := by
  have h := abstract_commutator
    (filterLinear x false) (filterLinear x true)
    (filterLinear y false) (filterLinear y true) v
  simpa only [native_quadratic_apply, filterLinear_apply] using h

end
end Glennie.Compact.PositiveCommutatorR01
