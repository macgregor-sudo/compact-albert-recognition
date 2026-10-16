/- The relabelling action on the 20 chart
coordinates is faithful, and every non-identity relabelling has a nowhere-dense fixed set.
  * `AffineComb.continuous20`: a map of the 20 coordinates that preserves affine combinations
    is continuous (it is a linear map plus a constant; finite dimension).
  * `AffineComb.eq_of_interior_fixed`: if such a map fixes a neighbourhood of one point, it
    fixes every point (restrict to the line through that point).
  * A test ledger `Lstar` in the affine domain whose 27 pair-block entries are pairwise
    different (`zTab`, kernel-checked integers). Five chart coordinates of `Lstar` already
    pin down the relabelling: `relabel_eq_one_of_heads`.
  * `act20_moved`, `relabel_faithful`, `fixed_interior_empty`, `isOpen_moved`, `dense_moved`,
    `relabel_gates` (the `hopen`/`hdense` hypotheses of the RobustBranchCore
    `dense_avoids_relabel_fixed_points`, for `ledgerRelabel := act20`), and `dense_avoids`.
`Lstar` is a point of the affine chart domain, not claimed to be the ledger of actual frames.
No rank, inverse-function, section or Phi statement is made here.
Proof method: Fin 3 splits use the Boolean `fin3_cases`; chart coordinates and ledger
projections are rewritten with rfl lemmas on variables before any comparison. The one linear
map built here (`AffineComb.continuous20`) is an abstract `f`, spelled `→ₗ[ℝ]` throughout. -/
module

public import Glennie.Compact.Affine20.Chart
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Real
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Module

@[expose] public section

namespace Glennie.Compact.Affine20

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Maps preserving affine combinations of the 20 coordinates -/

/-- A map of the 20 coordinates that preserves affine combinations is continuous. -/
theorem AffineComb.continuous20 {f : (Fin 20 → ℝ) → (Fin 20 → ℝ)} (hf : AffineComb f) :
    Continuous f := by
  have hsmul : ∀ (t : ℝ) (y : Fin 20 → ℝ), f (t • y) - f 0 = t • (f y - f 0) := by
    intro t y
    have h := hf 0 y t
    rw [sub_zero, zero_add] at h
    rw [h]
    abel
  have hadd : ∀ x y : Fin 20 → ℝ, f (x + y) - f 0 = (f x - f 0) + (f y - f 0) := by
    intro x y
    have h := hf ((2 : ℝ) • x) ((2 : ℝ) • y) (1 / 2)
    have e : (2 : ℝ) • x + (1 / 2 : ℝ) • ((2 : ℝ) • y - (2 : ℝ) • x) = x + y := by
      module
    rw [e] at h
    have h2x : f ((2 : ℝ) • x) = f 0 + (2 : ℝ) • (f x - f 0) := by
      rw [← hsmul]
      abel
    have h2y : f ((2 : ℝ) • y) = f 0 + (2 : ℝ) • (f y - f 0) := by
      rw [← hsmul]
      abel
    rw [h, h2x, h2y]
    module
  have hG : Continuous (fun x => f x - f 0) :=
    LinearMap.continuous_of_finiteDimensional
      ({ toFun := fun x => f x - f 0
         map_add' := hadd
         map_smul' := fun t y => by
           try rw [RingHom.id_apply]
           exact hsmul t y } : (Fin 20 → ℝ) →ₗ[ℝ] (Fin 20 → ℝ))
  have hf' : f = fun x => (f x - f 0) + f 0 := by
    funext x
    abel
  rw [hf']
  exact hG.fun_add continuous_const

/-- If a map preserving affine combinations fixes a neighbourhood of one point, it fixes
every point. -/
theorem AffineComb.eq_of_interior_fixed {F : (Fin 20 → ℝ) → (Fin 20 → ℝ)} (hf : AffineComb F)
    {b1 : Fin 20 → ℝ} (hb1 : b1 ∈ interior {b | F b = b}) (y : Fin 20 → ℝ) : F y = y := by
  have hS : {b | F b = b} ∈ nhds b1 := mem_interior_iff_mem_nhds.mp hb1
  have hfix0 : b1 ∈ {b | F b = b} := interior_subset hb1
  have hfix1 : F b1 = b1 := hfix0
  have hline : Continuous (fun t : ℝ => b1 + t • (y - b1)) := by
    fun_prop
  have hpre : (fun t : ℝ => b1 + t • (y - b1)) ⁻¹' {b | F b = b} ∈ nhds (0 : ℝ) := by
    refine hline.continuousAt.preimage_mem_nhds ?_
    simpa using hS
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  have hmem : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  have hx : F (b1 + (ε / 2) • (y - b1)) = b1 + (ε / 2) • (y - b1) := hball hmem
  rw [hf b1 y (ε / 2), hfix1] at hx
  have hx2 : (ε / 2) • (F y - b1) = (ε / 2) • (y - b1) := add_left_cancel hx
  have hne : ε / 2 ≠ 0 := (half_pos hε).ne'
  have hx3 : F y - b1 = y - b1 := by
    have h := congrArg (fun z => (ε / 2)⁻¹ • z) hx2
    simp only [smul_smul, inv_mul_cancel₀ hne, one_smul] at h
    exact h
  exact sub_left_inj.mp hx3

/-! ## A test ledger with pairwise different pair entries -/

/-- Integer offsets of the three pair blocks: zero row and column sums in each block, and
27 pairwise different values. -/
def zTab : Fin 3 → Fin 3 → Fin 3 → ℤ :=
  ![![![12, 0, -12], ![9, -1, -8], ![-21, 1, 20]],
    ![![-3, -11, 14], ![-4, -2, 6], ![7, 13, -20]],
    ![![-5, -10, 15], ![2, -6, 4], ![3, 16, -19]]]

theorem zTab_inj (β u w β' u' w' : Fin 3) (h : zTab β u w = zTab β' u' w') :
    β = β' ∧ u = u' ∧ w = w' := by
  have hb : (List.finRange 3).all (fun β => (List.finRange 3).all (fun u =>
      (List.finRange 3).all (fun w => (List.finRange 3).all (fun β' =>
        (List.finRange 3).all (fun u' => (List.finRange 3).all (fun w' =>
          decide (zTab β u w = zTab β' u' w' → β = β' ∧ u = u' ∧ w = w'))))))) = true := by
    decide +kernel
  have h1 := List.all_eq_true.mp hb β (List.mem_finRange β)
  have h2 := List.all_eq_true.mp h1 u (List.mem_finRange u)
  have h3 := List.all_eq_true.mp h2 w (List.mem_finRange w)
  have h4 := List.all_eq_true.mp h3 β' (List.mem_finRange β')
  have h5 := List.all_eq_true.mp h4 u' (List.mem_finRange u')
  exact of_decide_eq_true (List.all_eq_true.mp h5 w' (List.mem_finRange w')) h

theorem zTab_row (β u : Fin 3) : zTab β u 0 + zTab β u 1 + zTab β u 2 = 0 := by
  have hb : (List.finRange 3).all (fun β => (List.finRange 3).all (fun u =>
      decide (zTab β u 0 + zTab β u 1 + zTab β u 2 = 0))) = true := by
    decide +kernel
  have h1 := List.all_eq_true.mp hb β (List.mem_finRange β)
  exact of_decide_eq_true (List.all_eq_true.mp h1 u (List.mem_finRange u))

theorem zTab_col (β w : Fin 3) : zTab β 0 w + zTab β 1 w + zTab β 2 w = 0 := by
  have hb : (List.finRange 3).all (fun β => (List.finRange 3).all (fun w =>
      decide (zTab β 0 w + zTab β 1 w + zTab β 2 w = 0))) = true := by
    decide +kernel
  have h1 := List.all_eq_true.mp hb β (List.mem_finRange β)
  exact of_decide_eq_true (List.all_eq_true.mp h1 w (List.mem_finRange w))

/-- Pair-block entries of the test ledger: 1/3 + zTab/100. -/
def Lv (β u w : Fin 3) : ℝ := 1 / 3 + (zTab β u w : ℝ) / 100

theorem Lv_row (β u : Fin 3) : Lv β u 0 + Lv β u 1 + Lv β u 2 = 1 := by
  have h : (zTab β u 0 : ℝ) + (zTab β u 1 : ℝ) + (zTab β u 2 : ℝ) = 0 := by
    exact_mod_cast zTab_row β u
  unfold Lv
  linarith

theorem Lv_col (β w : Fin 3) : Lv β 0 w + Lv β 1 w + Lv β 2 w = 1 := by
  have h : (zTab β 0 w : ℝ) + (zTab β 1 w : ℝ) + (zTab β 2 w : ℝ) = 0 := by
    exact_mod_cast zTab_col β w
  unfold Lv
  linarith

theorem Lv_inj {β u w β' u' w' : Fin 3} (h : Lv β u w = Lv β' u' w') :
    β = β' ∧ u = u' ∧ w = w' := by
  have h1 : (zTab β u w : ℝ) = (zTab β' u' w' : ℝ) := by
    unfold Lv at h
    linarith
  exact zTab_inj β u w β' u' w' (by exact_mod_cast h1)

/-- The test ledger: pair blocks Lv 0, Lv 1, Lv 2 and centred triple tensor zero. -/
def Lstar : Ledger54 :=
  (fun i j k => (Lv 0 i j + Lv 1 j k + Lv 2 k i) / 3 - 2 / 9, Lv 0, Lv 1, Lv 2)

theorem Lstar_C (i j k : Fin 3) :
    Lstar.1 i j k = (Lv 0 i j + Lv 1 j k + Lv 2 k i) / 3 - 2 / 9 := rfl

theorem Lstar_P (i j : Fin 3) : Lstar.2.1 i j = Lv 0 i j := rfl

theorem Lstar_Q (j k : Fin 3) : Lstar.2.2.1 j k = Lv 1 j k := rfl

theorem Lstar_R (k i : Fin 3) : Lstar.2.2.2 k i = Lv 2 k i := rfl

theorem Lstar_inDomain : InDomain Lstar where
  P_row i := by
    simp only [Lstar_P]
    exact Lv_row 0 i
  P_col j := by
    simp only [Lstar_P]
    exact Lv_col 0 j
  Q_row j := by
    simp only [Lstar_Q]
    exact Lv_row 1 j
  Q_col k := by
    simp only [Lstar_Q]
    exact Lv_col 1 k
  R_row k := by
    simp only [Lstar_R]
    exact Lv_row 2 k
  R_col i := by
    simp only [Lstar_R]
    exact Lv_col 2 i
  C_k i j := by
    simp only [Lstar_C, Lstar_P]
    linarith [Lv_row 1 j, Lv_col 2 i]
  C_i j k := by
    simp only [Lstar_C, Lstar_Q]
    linarith [Lv_col 0 j, Lv_row 2 k]
  C_j k i := by
    simp only [Lstar_C, Lstar_R]
    linarith [Lv_row 0 i, Lv_col 1 k]

theorem pairExt_Lstar_01 (u w : Fin 3) : pairExt Lstar 0 1 u w = Lv 0 u w := by
  rw [pairExt_01, Lstar_P]

theorem pairExt_Lstar_10 (u w : Fin 3) : pairExt Lstar 1 0 u w = Lv 0 w u := by
  rw [pairExt_10, Lstar_P]

theorem pairExt_Lstar_12 (u w : Fin 3) : pairExt Lstar 1 2 u w = Lv 1 u w := by
  rw [pairExt_12, Lstar_Q]

theorem pairExt_Lstar_21 (u w : Fin 3) : pairExt Lstar 2 1 u w = Lv 1 w u := by
  rw [pairExt_21, Lstar_Q]

theorem pairExt_Lstar_20 (u w : Fin 3) : pairExt Lstar 2 0 u w = Lv 2 u w := by
  rw [pairExt_20, Lstar_R]

theorem pairExt_Lstar_02 (u w : Fin 3) : pairExt Lstar 0 2 u w = Lv 2 w u := by
  rw [pairExt_02, Lstar_R]

/-! ## Five chart coordinates of the test ledger pin down the relabelling -/

theorem fin3_third (c : Fin 3) (h0 : c ≠ 0) (h1 : c ≠ 1) : c = 2 := by
  have hb : (List.finRange 3).all (fun c => decide (c ≠ 0 → c ≠ 1 → c = 2)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp hb c (List.mem_finRange c)) h0 h1

theorem perm_eq_one (π : Equiv.Perm (Fin 3)) (h0 : π 0 = 0) (h1 : π 1 = 1) : π = 1 := by
  have h2 : π 2 = 2 := fin3_third (π 2)
    (fun h => absurd (π.injective (h.trans h0.symm)) (by decide))
    (fun h => absurd (π.injective (h.trans h1.symm)) (by decide))
  refine Equiv.Perm.ext fun x => ?_
  rcases fin3_cases x with rfl | rfl | rfl
  · exact h0.trans (Equiv.Perm.one_apply (0 : Fin 3)).symm
  · exact h1.trans (Equiv.Perm.one_apply (1 : Fin 3)).symm
  · exact h2.trans (Equiv.Perm.one_apply (2 : Fin 3)).symm

theorem relabel_eq_one_of_heads (γ : Relabel)
    (hP00 : pairExt Lstar (γ.order 0) (γ.order 1) (γ.labels 0 0) (γ.labels 1 0) = Lv 0 0 0)
    (hP01 : pairExt Lstar (γ.order 0) (γ.order 1) (γ.labels 0 0) (γ.labels 1 1) = Lv 0 0 1)
    (hP10 : pairExt Lstar (γ.order 0) (γ.order 1) (γ.labels 0 1) (γ.labels 1 0) = Lv 0 1 0)
    (hQ00 : pairExt Lstar (γ.order 1) (γ.order 2) (γ.labels 1 0) (γ.labels 2 0) = Lv 1 0 0)
    (hQ01 : pairExt Lstar (γ.order 1) (γ.order 2) (γ.labels 1 0) (γ.labels 2 1) = Lv 1 0 1) :
    γ = 1 := by
  have h01 : γ.order 0 ≠ γ.order 1 := γ.order.injective.ne (by decide)
  rcases pair3_cases _ _ h01 with ⟨e0, e1⟩ | ⟨e0, e1⟩ | ⟨e0, e1⟩ | ⟨e0, e1⟩ | ⟨e0, e1⟩ |
    ⟨e0, e1⟩
  · -- order (0, 1, 2): all three outcome permutations are forced to be the identity
    rw [e0, e1, pairExt_Lstar_01] at hP00 hP01 hP10
    obtain ⟨-, a0, b0⟩ := Lv_inj hP00
    obtain ⟨-, -, b1⟩ := Lv_inj hP01
    obtain ⟨-, a1, -⟩ := Lv_inj hP10
    have e2 : γ.order 2 = 2 := fin3_third (γ.order 2)
      (fun h => absurd (γ.order.injective (h.trans e0.symm)) (by decide))
      (fun h => absurd (γ.order.injective (h.trans e1.symm)) (by decide))
    rw [e1, e2, pairExt_Lstar_12] at hQ00 hQ01
    obtain ⟨-, -, c0⟩ := Lv_inj hQ00
    obtain ⟨-, -, c1⟩ := Lv_inj hQ01
    apply Relabel.ext
    · exact (perm_eq_one _ e0 e1).trans Relabel.one_order.symm
    · funext a
      rcases fin3_cases a with rfl | rfl | rfl
      · exact (perm_eq_one _ a0 a1).trans (Relabel.one_labels 0).symm
      · exact (perm_eq_one _ b0 b1).trans (Relabel.one_labels 1).symm
      · exact (perm_eq_one _ c0 c1).trans (Relabel.one_labels 2).symm
  · -- slots 0 and 1 swapped: P is read transposed, so the labels of slot 1 collide
    rw [e0, e1, pairExt_Lstar_10] at hP00 hP01
    obtain ⟨-, b0, -⟩ := Lv_inj hP00
    obtain ⟨-, b1, -⟩ := Lv_inj hP01
    exact absurd ((γ.labels 1).injective (b0.trans b1.symm)) (by decide)
  · rw [e0, e1, pairExt_Lstar_12] at hP00
    exact absurd (Lv_inj hP00).1 (by decide)
  · rw [e0, e1, pairExt_Lstar_21] at hP00
    exact absurd (Lv_inj hP00).1 (by decide)
  · rw [e0, e1, pairExt_Lstar_20] at hP00
    exact absurd (Lv_inj hP00).1 (by decide)
  · rw [e0, e1, pairExt_Lstar_02] at hP00
    exact absurd (Lv_inj hP00).1 (by decide)

/-! ## Faithfulness and the fixed sets -/

/-- The chart point of the test ledger. -/
def bStar : Fin 20 → ℝ := encode20 Lstar

theorem act20_bStar (γ : Relabel) : act20 γ bStar = encode20 (ledgerAct γ Lstar) := by
  unfold act20 bStar
  rw [decode_encode Lstar Lstar_inDomain]

/-- Every non-identity relabelling moves the test point. -/
theorem act20_moved (γ : Relabel) (hγ : γ ≠ 1) : act20 γ bStar ≠ bStar := by
  intro h
  apply hγ
  rw [act20_bStar] at h
  unfold bStar at h
  have e0 := congrFun h 0
  have e1 := congrFun h 1
  have e2 := congrFun h 2
  have e4 := congrFun h 4
  have e5 := congrFun h 5
  rw [encode20_apply_0, encode20_apply_0, sub_left_inj, ledgerAct_P, Lstar_P] at e0
  rw [encode20_apply_1, encode20_apply_1, sub_left_inj, ledgerAct_P, Lstar_P] at e1
  rw [encode20_apply_2, encode20_apply_2, sub_left_inj, ledgerAct_P, Lstar_P] at e2
  rw [encode20_apply_4, encode20_apply_4, sub_left_inj, ledgerAct_Q, Lstar_Q] at e4
  rw [encode20_apply_5, encode20_apply_5, sub_left_inj, ledgerAct_Q, Lstar_Q] at e5
  exact relabel_eq_one_of_heads γ e0 e1 e2 e4 e5

/-- The action on the 20 chart coordinates is faithful. -/
theorem relabel_faithful (γ : Relabel) (h : ∀ b, act20 γ b = b) : γ = 1 := by
  by_contra hγ
  exact act20_moved γ hγ (h bStar)

/-- The fixed set of a non-identity relabelling has empty interior. -/
theorem fixed_interior_empty (γ : Relabel) (hγ : γ ≠ 1) :
    interior {b : Fin 20 → ℝ | act20 γ b = b} = ∅ := by
  by_contra hne
  obtain ⟨b1, hb1⟩ := Set.nonempty_iff_ne_empty.mpr hne
  exact act20_moved γ hγ (AffineComb.eq_of_interior_fixed (act20_affine γ) hb1 bStar)

theorem isOpen_moved (γ : Relabel) : IsOpen {b : Fin 20 → ℝ | act20 γ b ≠ b} :=
  isOpen_ne_fun (AffineComb.continuous20 (act20_affine γ)) continuous_id'

theorem dense_moved (γ : Relabel) (hγ : γ ≠ 1) : Dense {b : Fin 20 → ℝ | act20 γ b ≠ b} :=
  interior_eq_empty_iff_dense_compl.mp (fixed_interior_empty γ hγ)

/-- The two topology gates of RobustBranchCore.dense_avoids_relabel_fixed_points for
`ledgerRelabel := act20`. -/
theorem relabel_gates :
    (∀ γ : Relabel, γ ≠ 1 → IsOpen {b : Fin 20 → ℝ | act20 γ b ≠ b}) ∧
      (∀ γ : Relabel, γ ≠ 1 → Dense {b : Fin 20 → ℝ | act20 γ b ≠ b}) :=
  ⟨fun γ _ => isOpen_moved γ, dense_moved⟩

/-- Chart points off every non-identity fixed set are dense. -/
theorem dense_avoids : Dense {b : Fin 20 → ℝ | ∀ γ : Relabel, γ ≠ 1 → act20 γ b ≠ b} := by
  have ho : ∀ γ : {γ : Relabel // γ ≠ 1}, IsOpen {b : Fin 20 → ℝ | act20 γ.1 b ≠ b} :=
    fun γ => isOpen_moved γ.1
  have hd : ∀ γ : {γ : Relabel // γ ≠ 1}, Dense {b : Fin 20 → ℝ | act20 γ.1 b ≠ b} :=
    fun γ => dense_moved γ.1 γ.2
  refine Dense.mono ?_ (dense_iInter_of_isOpen ho hd)
  intro b hb γ hγ
  exact Set.mem_iInter.mp hb ⟨γ, hγ⟩

end
end Glennie.Compact.Affine20
