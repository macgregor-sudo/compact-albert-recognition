/- The 1296-element relabelling group and the raw
54-entry ledger.
  * `Relabel`: a frame order σ ∈ S3 and one outcome permutation ℓ_a ∈ S3 per frame slot,
    with the wreath (semidirect) multiplication; `card_relabel : Fintype.card Relabel = 1296`.
  * `relabelTriple γ T a i = T (σ a) (ℓ_a i)` (the action of the RobustBranches
    `relabel`). It is a right action: `relabelTriple (γ * δ) = relabelTriple δ ∘ relabelTriple γ`.
  * `ledger54`: the complete raw ledger (C, P, Q, R; R indexed (k, i)).
  * `ledgerAct γ`: the induced permutation of the 54 coordinates;
    `ledger54_relabel : ledger54 (relabelTriple γ T) = ledgerAct γ (ledger54 T)` for every
    triple (no frame hypothesis), from the symmetry of the trace form.
  * `ledger54_map`: invariance under every `CompactAutomorphism`.
Finite facts about Fin 3 are kernel-checked Boolean checks (`decide +kernel` on lists of
Fin 3, no reals). No chart, rank or analytic statement is made here.
Proof method: projections of the ledger are related to their
values only through rfl lemmas on variables (`ledger54_C/P/Q/R`, `ledgerAct_C/P/Q/R`,
`pairExt_xy`) used by rw/simp only; no rfl, exact or show compares two different
Albert-valued structures. -/
module

public import Glennie.Automorphism
public import Glennie.Native.AlgebraLaws
public import Mathlib.Data.Fintype.OfMap
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace Glennie.Compact.Affine20

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Triples and the 54-entry ledger -/

/-- Three ordered frames of three atoms each. -/
abbrev Triple := Fin 3 → Fin 3 → Albert

/-- The complete raw ledger: the 27 triple traces C, then the pair blocks P, Q, R
(R indexed (k, i)). -/
abbrev Ledger54 :=
  (Fin 3 → Fin 3 → Fin 3 → ℝ) × (Fin 3 → Fin 3 → ℝ) × (Fin 3 → Fin 3 → ℝ) ×
    (Fin 3 → Fin 3 → ℝ)

/-- The 54-entry raw ledger of a triple: C = T((p_i o q_j) o r_k), P = T(p_i o q_j),
Q = T(q_j o r_k), R = T(r_k o p_i). -/
def ledger54 (T : Triple) : Ledger54 :=
  (ledger (T 0) (T 1) (T 2), fun i j => inner (T 0 i) (T 1 j),
    fun j k => inner (T 1 j) (T 2 k), fun k i => inner (T 2 k) (T 0 i))

/-- Fin 3 has exactly the elements 0, 1, 2 (kernel-checked Boolean list check). -/
theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  have hb : (List.finRange 3).all (fun i => decide (i = 0 ∨ i = 1 ∨ i = 2)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp hb i (List.mem_finRange i))

/-! ## The relabelling group (S3)^3 ⋊ S3 -/

/-- A relabelling: a frame order and one outcome permutation per frame slot. -/
@[ext] structure Relabel where
  order : Equiv.Perm (Fin 3)
  labels : Fin 3 → Equiv.Perm (Fin 3)

namespace Relabel

instance : Mul Relabel :=
  ⟨fun γ δ => ⟨γ.order * δ.order, fun a => γ.labels (δ.order a) * δ.labels a⟩⟩

instance : One Relabel := ⟨⟨1, fun _ => 1⟩⟩

instance : Inv Relabel := ⟨fun γ => ⟨γ.order⁻¹, fun a => (γ.labels (γ.order⁻¹ a))⁻¹⟩⟩

@[simp] theorem mul_order (γ δ : Relabel) : (γ * δ).order = γ.order * δ.order := rfl

@[simp] theorem mul_labels (γ δ : Relabel) (a : Fin 3) :
    (γ * δ).labels a = γ.labels (δ.order a) * δ.labels a := rfl

@[simp] theorem one_order : (1 : Relabel).order = 1 := rfl

@[simp] theorem one_labels (a : Fin 3) : (1 : Relabel).labels a = 1 := rfl

@[simp] theorem inv_order (γ : Relabel) : γ⁻¹.order = γ.order⁻¹ := rfl

@[simp] theorem inv_labels (γ : Relabel) (a : Fin 3) :
    γ⁻¹.labels a = (γ.labels (γ.order⁻¹ a))⁻¹ := rfl

/-- The group structure; `Mul`, `One` and `Inv` are the instances above (the pattern of
Mathlib's `Equiv.Perm.permGroup`). -/
instance : Group Relabel where
  mul_assoc γ δ ε := Relabel.ext (by simp [mul_assoc]) (by funext a; simp [mul_assoc])
  one_mul γ := Relabel.ext (by simp) (by funext a; simp)
  mul_one γ := Relabel.ext (by simp) (by funext a; simp)
  inv_mul_cancel γ := Relabel.ext (by simp) (by funext a; simp)

/-- Relabellings as four permutations (order, labels 0, labels 1, labels 2). -/
def equivProd : Relabel ≃
    Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) where
  toFun γ := (γ.order, γ.labels 0, γ.labels 1, γ.labels 2)
  invFun p := ⟨p.1, ![p.2.1, p.2.2.1, p.2.2.2]⟩
  left_inv γ := by
    apply Relabel.ext
    · rfl
    · funext a
      rcases fin3_cases a with rfl | rfl | rfl <;> rfl
  right_inv _ := rfl

instance : Fintype Relabel := Fintype.ofEquiv _ equivProd.symm

/-- There are exactly (3!)^4 = 1296 relabellings. -/
theorem card_relabel : Fintype.card Relabel = 1296 := by
  rw [Fintype.card_congr equivProd]
  simp only [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin]
  all_goals decide

end Relabel

/-- The action on triples: slot a reads frame σ a, relabelled by ℓ_a. -/
def relabelTriple (γ : Relabel) (T : Triple) : Triple :=
  fun a i => T (γ.order a) (γ.labels a i)

theorem relabelTriple_apply (γ : Relabel) (T : Triple) (a i : Fin 3) :
    relabelTriple γ T a i = T (γ.order a) (γ.labels a i) := rfl

theorem relabelTriple_one (T : Triple) : relabelTriple 1 T = T := rfl

/-- A right action. -/
theorem relabelTriple_mul (γ δ : Relabel) (T : Triple) :
    relabelTriple (γ * δ) T = relabelTriple δ (relabelTriple γ T) := rfl

/-- Pointwise transport by a compact automorphism. -/
def mapAtoms (g : CompactAutomorphism) (T : Triple) : Triple :=
  fun a i => g.equiv (T a i)

theorem mapAtoms_apply (g : CompactAutomorphism) (T : Triple) (a i : Fin 3) :
    mapAtoms g T a i = g.equiv (T a i) := rfl

theorem mapAtoms_slot (g : CompactAutomorphism) (T : Triple) (a : Fin 3) :
    mapAtoms g T a = fun i => g.equiv (T a i) := rfl

theorem mapAtoms_relabel (g : CompactAutomorphism) (γ : Relabel) (T : Triple) :
    mapAtoms g (relabelTriple γ T) = relabelTriple γ (mapAtoms g T) := rfl

/-! Projections of the 54-entry ledger, on variables. Proofs rewrite with these before any
comparison, so no unification has to unfold Albert products. -/

theorem ledger54_C (T : Triple) (i j k : Fin 3) :
    (ledger54 T).1 i j k = ledger (T 0) (T 1) (T 2) i j k := rfl

theorem ledger54_P (T : Triple) (i j : Fin 3) :
    (ledger54 T).2.1 i j = inner (T 0 i) (T 1 j) := rfl

theorem ledger54_Q (T : Triple) (j k : Fin 3) :
    (ledger54 T).2.2.1 j k = inner (T 1 j) (T 2 k) := rfl

theorem ledger54_R (T : Triple) (k i : Fin 3) :
    (ledger54 T).2.2.2 k i = inner (T 2 k) (T 0 i) := rfl

theorem ledger54_map (g : CompactAutomorphism) (T : Triple) :
    ledger54 (mapAtoms g T) = ledger54 T := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext i j k
    rw [ledger54_C, ledger54_C, mapAtoms_slot, mapAtoms_slot, mapAtoms_slot]
    exact g.ledger_map (T 0) (T 1) (T 2) i j k
  · funext i j
    rw [ledger54_P, ledger54_P, mapAtoms_apply, mapAtoms_apply]
    exact g.inner_map (T 0 i) (T 1 j)
  · funext j k
    rw [ledger54_Q, ledger54_Q, mapAtoms_apply, mapAtoms_apply]
    exact g.inner_map (T 1 j) (T 2 k)
  · funext k i
    rw [ledger54_R, ledger54_R, mapAtoms_apply, mapAtoms_apply]
    exact g.inner_map (T 2 k) (T 0 i)

/-! ## Finite facts about Fin 3 (kernel-checked Boolean lists) -/

theorem pair3_cases (f g : Fin 3) (h : f ≠ g) :
    (f = 0 ∧ g = 1) ∨ (f = 1 ∧ g = 0) ∨ (f = 1 ∧ g = 2) ∨ (f = 2 ∧ g = 1) ∨
      (f = 2 ∧ g = 0) ∨ (f = 0 ∧ g = 2) := by
  have hb : (List.finRange 3).all (fun f => (List.finRange 3).all (fun g =>
      decide (f ≠ g → (f = 0 ∧ g = 1) ∨ (f = 1 ∧ g = 0) ∨ (f = 1 ∧ g = 2) ∨
        (f = 2 ∧ g = 1) ∨ (f = 2 ∧ g = 0) ∨ (f = 0 ∧ g = 2)))) = true := by
    decide +kernel
  have h1 := List.all_eq_true.mp hb f (List.mem_finRange f)
  exact of_decide_eq_true (List.all_eq_true.mp h1 g (List.mem_finRange g)) h

theorem perm3_cases (a b c : Fin 3) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (a = 0 ∧ b = 1 ∧ c = 2) ∨ (a = 0 ∧ b = 2 ∧ c = 1) ∨ (a = 1 ∧ b = 0 ∧ c = 2) ∨
      (a = 1 ∧ b = 2 ∧ c = 0) ∨ (a = 2 ∧ b = 0 ∧ c = 1) ∨ (a = 2 ∧ b = 1 ∧ c = 0) := by
  have hb : (List.finRange 3).all (fun a => (List.finRange 3).all (fun b =>
      (List.finRange 3).all (fun c => decide (a ≠ b → b ≠ c → a ≠ c →
        (a = 0 ∧ b = 1 ∧ c = 2) ∨ (a = 0 ∧ b = 2 ∧ c = 1) ∨ (a = 1 ∧ b = 0 ∧ c = 2) ∨
          (a = 1 ∧ b = 2 ∧ c = 0) ∨ (a = 2 ∧ b = 0 ∧ c = 1) ∨
            (a = 2 ∧ b = 1 ∧ c = 0))))) = true := by
    decide +kernel
  have h1 := List.all_eq_true.mp hb a (List.mem_finRange a)
  have h2 := List.all_eq_true.mp h1 b (List.mem_finRange b)
  exact of_decide_eq_true (List.all_eq_true.mp h2 c (List.mem_finRange c)) hab hbc hac

/-! ## Symmetry of the triple trace -/

theorem c_swap (x y z : Albert) :
    trace (jordan (jordan x y) z) = trace (jordan (jordan y x) z) := by
  rw [jordan_comm x y]

theorem c_cycle (x y z : Albert) :
    trace (jordan (jordan x y) z) = trace (jordan (jordan y z) x) := by
  change inner (jordan x y) z = inner (jordan y z) x
  rw [inner_jordan_associative, inner_comm]

/-- The symmetrisation of the triple trace over the six orders. -/
def csym (x y z : Albert) : ℝ :=
  (trace (jordan (jordan x y) z) + trace (jordan (jordan y x) z) +
    trace (jordan (jordan y z) x) + trace (jordan (jordan z y) x) +
    trace (jordan (jordan z x) y) + trace (jordan (jordan x z) y)) / 6

/-- The triple trace is totally symmetric, hence equal to its symmetrisation. -/
theorem c_eq_csym (x y z : Albert) : trace (jordan (jordan x y) z) = csym x y z := by
  unfold csym
  linarith [c_swap x y z, c_cycle x y z, c_cycle y z x, c_swap z x y, c_swap y z x]

/-! ## The induced action on the 54 coordinates -/

/-- The overlap between atom (f, u) and atom (g, w), read from the three pair blocks
(0 on the diagonal f = g, which the action never uses). -/
def pairExt (L : Ledger54) (f g u w : Fin 3) : ℝ :=
  (![![fun _ _ => 0, fun u w => L.2.1 u w, fun u w => L.2.2.2 w u],
      ![fun u w => L.2.1 w u, fun _ _ => 0, fun u w => L.2.2.1 u w],
      ![fun u w => L.2.2.2 u w, fun u w => L.2.2.1 w u, fun _ _ => 0]] :
    Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) f g u w

/-- After relabelling by γ, the outcome index carried by frame a in the C cell (i, j, k). -/
def slotIndex (γ : Relabel) (i j k a : Fin 3) : Fin 3 :=
  if γ.order 0 = a then γ.labels 0 i else if γ.order 1 = a then γ.labels 1 j else γ.labels 2 k

/-- The coordinate permutation of the 54-entry ledger induced by γ. -/
def ledgerAct (γ : Relabel) (L : Ledger54) : Ledger54 :=
  (fun i j k => L.1 (slotIndex γ i j k 0) (slotIndex γ i j k 1) (slotIndex γ i j k 2),
    fun i j => pairExt L (γ.order 0) (γ.order 1) (γ.labels 0 i) (γ.labels 1 j),
    fun j k => pairExt L (γ.order 1) (γ.order 2) (γ.labels 1 j) (γ.labels 2 k),
    fun k i => pairExt L (γ.order 2) (γ.order 0) (γ.labels 2 k) (γ.labels 0 i))

theorem ledgerAct_C (γ : Relabel) (L : Ledger54) (i j k : Fin 3) :
    (ledgerAct γ L).1 i j k =
      L.1 (slotIndex γ i j k 0) (slotIndex γ i j k 1) (slotIndex γ i j k 2) := rfl

theorem ledgerAct_P (γ : Relabel) (L : Ledger54) (i j : Fin 3) :
    (ledgerAct γ L).2.1 i j =
      pairExt L (γ.order 0) (γ.order 1) (γ.labels 0 i) (γ.labels 1 j) := rfl

theorem ledgerAct_Q (γ : Relabel) (L : Ledger54) (j k : Fin 3) :
    (ledgerAct γ L).2.2.1 j k =
      pairExt L (γ.order 1) (γ.order 2) (γ.labels 1 j) (γ.labels 2 k) := rfl

theorem ledgerAct_R (γ : Relabel) (L : Ledger54) (k i : Fin 3) :
    (ledgerAct γ L).2.2.2 k i =
      pairExt L (γ.order 2) (γ.order 0) (γ.labels 2 k) (γ.labels 0 i) := rfl

theorem pairExt_00 (L : Ledger54) (u w : Fin 3) : pairExt L 0 0 u w = 0 := rfl

theorem pairExt_11 (L : Ledger54) (u w : Fin 3) : pairExt L 1 1 u w = 0 := rfl

theorem pairExt_22 (L : Ledger54) (u w : Fin 3) : pairExt L 2 2 u w = 0 := rfl

theorem pairExt_01 (L : Ledger54) (u w : Fin 3) : pairExt L 0 1 u w = L.2.1 u w := rfl

theorem pairExt_10 (L : Ledger54) (u w : Fin 3) : pairExt L 1 0 u w = L.2.1 w u := rfl

theorem pairExt_12 (L : Ledger54) (u w : Fin 3) : pairExt L 1 2 u w = L.2.2.1 u w := rfl

theorem pairExt_21 (L : Ledger54) (u w : Fin 3) : pairExt L 2 1 u w = L.2.2.1 w u := rfl

theorem pairExt_20 (L : Ledger54) (u w : Fin 3) : pairExt L 2 0 u w = L.2.2.2 u w := rfl

theorem pairExt_02 (L : Ledger54) (u w : Fin 3) : pairExt L 0 2 u w = L.2.2.2 w u := rfl

theorem pairExt_ledger54 (T : Triple) (f g u w : Fin 3) (hfg : f ≠ g) :
    pairExt (ledger54 T) f g u w = inner (T f u) (T g w) := by
  rcases pair3_cases f g hfg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [pairExt_01, ledger54_P]
  · rw [pairExt_10, ledger54_P]
    exact inner_comm _ _
  · rw [pairExt_12, ledger54_Q]
  · rw [pairExt_21, ledger54_Q]
    exact inner_comm _ _
  · rw [pairExt_20, ledger54_R]
  · rw [pairExt_02, ledger54_R]
    exact inner_comm _ _

theorem ledger54_relabel_C (γ : Relabel) (T : Triple) (i j k : Fin 3) :
    (ledger54 (relabelTriple γ T)).1 i j k = (ledgerAct γ (ledger54 T)).1 i j k := by
  have h01 : γ.order 0 ≠ γ.order 1 := γ.order.injective.ne (by decide)
  have h12 : γ.order 1 ≠ γ.order 2 := γ.order.injective.ne (by decide)
  have h02 : γ.order 0 ≠ γ.order 2 := γ.order.injective.ne (by decide)
  rw [ledger54_C, ledgerAct_C, ledger54_C]
  simp only [ledger, relabelTriple_apply]
  rcases perm3_cases _ _ _ h01 h12 h02 with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ |
    ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ <;>
    simp [slotIndex, e0, e1, e2, c_eq_csym] <;>
    (simp only [csym]; ring)

/-- Raw-ledger equivariance: relabelling a triple permutes its 54 ledger coordinates. -/
theorem ledger54_relabel (γ : Relabel) (T : Triple) :
    ledger54 (relabelTriple γ T) = ledgerAct γ (ledger54 T) := by
  have h01 : γ.order 0 ≠ γ.order 1 := γ.order.injective.ne (by decide)
  have h12 : γ.order 1 ≠ γ.order 2 := γ.order.injective.ne (by decide)
  have h20 : γ.order 2 ≠ γ.order 0 := γ.order.injective.ne (by decide)
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext i j k
    exact ledger54_relabel_C γ T i j k
  · funext i j
    rw [ledger54_P, relabelTriple_apply, relabelTriple_apply, ledgerAct_P,
      pairExt_ledger54 T _ _ _ _ h01]
  · funext j k
    rw [ledger54_Q, relabelTriple_apply, relabelTriple_apply, ledgerAct_Q,
      pairExt_ledger54 T _ _ _ _ h12]
  · funext k i
    rw [ledger54_R, relabelTriple_apply, relabelTriple_apply, ledgerAct_R,
      pairExt_ledger54 T _ _ _ _ h20]

/-- Ledger form of "a product automorphism after a relabelling": the ledger of
g·(γ·T) is γ acting on the ledger of T. -/
theorem ledger54_map_relabel (g : CompactAutomorphism) (γ : Relabel) (T : Triple) :
    ledger54 (mapAtoms g (relabelTriple γ T)) = ledgerAct γ (ledger54 T) := by
  rw [ledger54_map, ledger54_relabel]

end
end Glennie.Compact.Affine20
