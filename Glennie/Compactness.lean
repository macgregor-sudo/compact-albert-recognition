/- Compactness of the actual native automorphism maps.
The maximum theorem does not assert diagonalization; explicit rotations are
needed to show that a maximizing point has vanishing off-diagonal entries. -/
module
public import Glennie.Hilbert
public import Glennie.Automorphism
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Order.Compact

@[expose] public section
namespace Glennie
noncomputable section

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def jordanContinuous : Albert →L[ℝ] Albert →L[ℝ] Albert :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
      (Albert →ₗ[ℝ] Albert) ≃ₗ[ℝ] (Albert →L[ℝ] Albert)).toLinearMap.comp jordanLinear)

@[simp] theorem jordanContinuous_apply (x y : Albert) :
    jordanContinuous x y = jordan x y := rfl

theorem continuous_jordan : Continuous (fun p : Albert × Albert => jordan p.1 p.2) :=
  (jordanContinuous.continuous.comp continuous_fst).clm_apply continuous_snd

section StableNativePairing
set_option backward.isDefEq.respectTransparency false
theorem nativeRealSMulComm : SMulCommClass ℝ ℝ ℝ := inferInstance
theorem nativeRealContinuousAdd : ContinuousAdd ℝ := inferInstance
theorem nativeRealContinuousSMul : ContinuousConstSMul ℝ ℝ := inferInstance
attribute [local instance 20000] nativeRealSMulComm nativeRealContinuousAdd nativeRealContinuousSMul
def nativeInnerLinear : Albert →ₗ[ℝ] Albert →ₗ[ℝ] ℝ where
  toFun x :=
    { toFun := inner x
      map_add' y z := inner_add_right x y z
      map_smul' r y := inner_smul_right r x y }
  map_add' x y := by ext z; exact inner_add_left x y z
  map_smul' r x := by ext y; exact inner_smul_left r x y

theorem nativeInnerRight_cont (x : Albert) : Continuous (fun y => inner x y) :=
  (nativeInnerLinear x).continuous_of_finiteDimensional
def nativeInnerRight (x : Albert) : Albert →L[ℝ] ℝ where
  toLinearMap := nativeInnerLinear x
  cont := nativeInnerRight_cont x
theorem nativeInnerRight_add (x y : Albert) :
    nativeInnerRight (x + y) = nativeInnerRight x + nativeInnerRight y :=
  ContinuousLinearMap.ext (fun z => inner_add_left x y z)
theorem nativeInnerRight_smul (r : ℝ) (x : Albert) :
    nativeInnerRight (r • x) = r • nativeInnerRight x :=
  ContinuousLinearMap.ext (fun y => inner_smul_left r x y)
def nativeInnerRightLinear : Albert →ₗ[ℝ] (Albert →L[ℝ] ℝ) where
  toFun := nativeInnerRight
  map_add' := nativeInnerRight_add
  map_smul' := nativeInnerRight_smul
theorem nativeInnerRightLinear_cont : Continuous nativeInnerRightLinear :=
  nativeInnerRightLinear.continuous_of_finiteDimensional
def nativeInnerContinuous : Albert →L[ℝ] Albert →L[ℝ] ℝ where
  toLinearMap := nativeInnerRightLinear
  cont := nativeInnerRightLinear_cont
end StableNativePairing

theorem continuous_native_inner : Continuous (fun p : Albert × Albert => inner p.1 p.2) :=
  (nativeInnerContinuous.continuous.comp continuous_fst).clm_apply continuous_snd

/-- An actual real-linear map is represented by its images on a fixed basis.
The parameter space has the ordinary product topology on 27 native Albert
columns, with no operator-space metric or alternate topology. -/
abbrev AutomorphismColumns := Fin 27 → Albert

def automorphismBasis : Module.Basis (Fin 27) ℝ Albert :=
  Module.finBasisOfFinrankEq ℝ Albert albert_finrank

def columnMap (v : AutomorphismColumns) : Albert →ₗ[ℝ] Albert :=
  automorphismBasis.constr ℝ v

@[simp] theorem columnMap_basis (v : AutomorphismColumns) (i : Fin 27) :
    columnMap v (automorphismBasis i) = v i :=
  automorphismBasis.constr_basis ℝ v i

theorem columnMap_apply (v : AutomorphismColumns) (x : Albert) :
    columnMap v x = ∑ i, automorphismBasis.equivFun x i • v i :=
  automorphismBasis.constr_apply_fintype ℝ v x

@[simp] theorem columnMap_linearImage (f : Albert →ₗ[ℝ] Albert) :
    columnMap (fun i => f (automorphismBasis i)) = f :=
  automorphismBasis.constr_self ℝ f

theorem continuous_columnMap_apply (x : Albert) :
    Continuous (fun v : AutomorphismColumns => columnMap v x) := by
  simp_rw [columnMap_apply]
  exact continuous_finsetSum Finset.univ fun i _ =>
    (continuous_const : Continuous (fun _ : AutomorphismColumns =>
      automorphismBasis.equivFun x i)).smul (continuous_apply i)

/-- Only actual unit, product and native metric preservation are required.
No spectral, transitivity or endpoint condition occurs in this closed set. -/
def automorphismMaps : Set AutomorphismColumns :=
  {v | columnMap v 1 = 1 ∧
    (∀ x y, columnMap v (jordan x y) = jordan (columnMap v x) (columnMap v y)) ∧
    ∀ x y, inner (columnMap v x) (columnMap v y) = inner x y}

theorem automorphismMaps_closed : IsClosed automorphismMaps := by
  have heval (x : Albert) :
      Continuous (fun v : AutomorphismColumns => columnMap v x) :=
    continuous_columnMap_apply x
  have hj (x y : Albert) :
      IsClosed {v : AutomorphismColumns |
        columnMap v (jordan x y) = jordan (columnMap v x) (columnMap v y)} := by
    have hprod : Continuous (fun v : AutomorphismColumns =>
        (columnMap v x, columnMap v y)) := (heval x).prodMk (heval y)
    have hright : Continuous (fun v : AutomorphismColumns =>
        jordan (columnMap v x) (columnMap v y)) := by
      simpa only [Function.comp_def] using continuous_jordan.comp hprod
    exact isClosed_eq (heval (jordan x y)) hright
  have hi (x y : Albert) :
      IsClosed {v : AutomorphismColumns |
        inner (columnMap v x) (columnMap v y) = inner x y} := by
    have hprod : Continuous (fun v : AutomorphismColumns =>
        (columnMap v x, columnMap v y)) := (heval x).prodMk (heval y)
    have hleft : Continuous (fun v : AutomorphismColumns =>
        inner (columnMap v x) (columnMap v y)) := by
      simpa only [Function.comp_def] using continuous_native_inner.comp hprod
    exact isClosed_eq hleft
      (continuous_const : Continuous (fun _ : AutomorphismColumns => inner x y))
  have hunit : IsClosed {v : AutomorphismColumns | columnMap v 1 = 1} :=
    isClosed_eq (heval 1)
      (continuous_const : Continuous (fun _ : AutomorphismColumns => (1 : Albert)))
  have hc := hunit.inter
    ((isClosed_iInter fun x => isClosed_iInter fun y => hj x y).inter
      (isClosed_iInter fun x => isClosed_iInter fun y => hi x y))
  convert hc using 1
  ext v
  simp [automorphismMaps]

theorem automorphismMaps_norm (v : AutomorphismColumns) (hv : v ∈ automorphismMaps)
    (x : Albert) : ‖columnMap v x‖ = ‖x‖ := by
  have h := hv.2.2 x x
  rw [← native_norm_sq, ← native_norm_sq] at h
  nlinarith [norm_nonneg (columnMap v x), norm_nonneg x]

/-- Each basis image lies in its native compact closed ball. A finite product
of these balls bounds the actual automorphism columns. -/
theorem automorphismMaps_compact : IsCompact automorphismMaps := by
  have hb : IsCompact {v : AutomorphismColumns |
      ∀ i, v i ∈ Metric.closedBall (0 : Albert) ‖automorphismBasis i‖} :=
    isCompact_pi_infinite fun i => isCompact_closedBall (0 : Albert) ‖automorphismBasis i‖
  apply hb.of_isClosed_subset automorphismMaps_closed
  intro v hv i
  have hn := automorphismMaps_norm v hv (automorphismBasis i)
  rw [columnMap_basis] at hn
  simpa only [Metric.mem_closedBall, dist_zero_right] using hn.le

theorem automorphismMaps_nonempty : automorphismMaps.Nonempty := by
  have hm : columnMap (fun i => automorphismBasis i) = (LinearMap.id : Albert →ₗ[ℝ] Albert) := by
    simpa only [LinearMap.id_apply] using columnMap_linearImage
      (LinearMap.id : Albert →ₗ[ℝ] Albert)
  refine ⟨(fun i => automorphismBasis i), ?_⟩
  change columnMap _ 1 = 1 ∧ _
  rw [hm]
  exact ⟨rfl, (fun _ _ => rfl), (fun _ _ => rfl)⟩

def CompactAutomorphism.columns (g : CompactAutomorphism) : AutomorphismColumns :=
  fun i => g.equiv (automorphismBasis i)

@[simp] theorem CompactAutomorphism.columns_apply (g : CompactAutomorphism) (x : Albert) :
    columnMap g.columns x = g.equiv x := by
  rw [show columnMap g.columns = g.equiv.toLinearMap from
    columnMap_linearImage g.equiv.toLinearMap]
  rfl

theorem CompactAutomorphism.columns_mem (g : CompactAutomorphism) :
    g.columns ∈ automorphismMaps := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [CompactAutomorphism.columns_apply] using g.map_unit
  · intro x y
    simpa only [CompactAutomorphism.columns_apply] using g.map_jordan x y
  · intro x y
    simpa only [CompactAutomorphism.columns_apply] using g.inner_map x y

/-- Metric preservation supplies injectivity and finite dimension supplies
surjectivity. Unit and metric preservation then imply trace preservation. -/
def compactAutomorphismOfMap (v : AutomorphismColumns) (hv : v ∈ automorphismMaps) :
    CompactAutomorphism := by
  have hinj : Function.Injective (columnMap v) := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply (inner_self_eq_zero (x-y)).mp
    have h := hv.2.2 (x-y) (x-y)
    simpa only [map_sub, hxy, sub_self, inner_zero_left] using h.symm
  refine ⟨LinearEquiv.ofBijective (columnMap v)
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩, hv.2.1, ?_⟩
  intro x
  rw [LinearEquiv.ofBijective_apply]
  have h := hv.2.2 x 1
  simpa only [hv.1, inner_unit_right] using h

@[simp] theorem compactAutomorphismOfMap_apply (v : AutomorphismColumns)
    (hv : v ∈ automorphismMaps) (x : Albert) :
    (compactAutomorphismOfMap v hv).equiv x = columnMap v x := by
  simp only [compactAutomorphismOfMap, LinearEquiv.ofBijective_apply]

def diagonalEnergy (x : Albert) : ℝ := x.d0^2 + x.d1^2 + x.d2^2

def diagonalCoordinateLinear (i : Fin 3) : Albert →ₗ[ℝ] ℝ where
  toFun x := ![x.d0,x.d1,x.d2] i
  map_add' x y := by fin_cases i <;> rfl
  map_smul' r x := by fin_cases i <;> rfl

theorem continuous_diagonalEnergy : Continuous diagonalEnergy := by
  have h0 : Continuous (fun x : Albert => x.d0) :=
    (diagonalCoordinateLinear 0).continuous_of_finiteDimensional
  have h1 : Continuous (fun x : Albert => x.d1) :=
    (diagonalCoordinateLinear 1).continuous_of_finiteDimensional
  have h2 : Continuous (fun x : Albert => x.d2) :=
    (diagonalCoordinateLinear 2).continuous_of_finiteDimensional
  exact ((h0.pow 2).add (h1.pow 2)).add (h2.pow 2)

/-- Every native Albert element admits an actual automorphism maximizing
its diagonal energy. The compact parameter set contains no diagonalization
conclusion; that conclusion still requires the explicit rotation argument. -/
theorem exists_diagonalEnergy_maximum (x : Albert) :
    ∃ g : CompactAutomorphism, ∀ h : CompactAutomorphism,
      diagonalEnergy (h.equiv x) ≤ diagonalEnergy (g.equiv x) := by
  have hc : Continuous (fun v : AutomorphismColumns => diagonalEnergy (columnMap v x)) := by
    simpa only [Function.comp_def] using
      continuous_diagonalEnergy.comp (continuous_columnMap_apply x)
  obtain ⟨v, hv, hmax⟩ := automorphismMaps_compact.exists_isMaxOn
    automorphismMaps_nonempty hc.continuousOn
  refine ⟨compactAutomorphismOfMap v hv, fun h => ?_⟩
  have hm : diagonalEnergy (columnMap h.columns x) ≤ diagonalEnergy (columnMap v x) :=
    hmax h.columns_mem
  simpa only [compactAutomorphismOfMap_apply, CompactAutomorphism.columns_apply] using hm

end
end Glennie
