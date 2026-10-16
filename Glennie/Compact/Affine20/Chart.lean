/- The genuine affine-20 ledger domain and its chart.
  * `InDomain L`: the margin identities. Each pair block is doubly stochastic, and the
    triple block C has the pair blocks as its three margins.
  * `ledger54_inDomain`: every triple of actual native frames lies in the domain
    (`ledger_margin3`, the algebra of the `ledger_last_marginal`, and the `ledger_cyclic`, Glennie.Theorems.Frames). Every field first rewrites the ledger
    projections with the variable-level lemmas `ledger54_C/P/Q/R` (Relabel).
  * `encode20` reads 20 coordinates: the 2x2 heads of P-1/3, Q-1/3, R-1/3 (12) and the 2x2x2
    head of the centred tensor H = C - (P + Q + R)/3 + 2/9 (8). `decode20` rebuilds all 54
    entries from 20 numbers.
  * `decode_encode`: decode20 (encode20 L) = L for every L in the domain, through generic
    zero-margin reconstruction lemmas (`ext3_reconstruct`, `lift4_reconstruct`,
    `lift8_reconstruct`); `decode_encode_frames` for actual frames.
  * `AffineComb f`: f preserves affine combinations. It holds for encode20, decode20 and
    every `ledgerAct γ`, and it is closed under composition.
  * `act20 γ = encode20 ∘ ledgerAct γ ∘ decode20`, the relabelling on chart coordinates;
    `act20_affine`, and `relabel_ledger`: for actual frames,
    act20 γ (encode20 (ledger54 T)) = encode20 (ledger54 (relabelTriple γ T)).
No rank, inverse-function, fixed-point or analytic statement is made here.
Proof method: index splits use the Boolean lemmas `fin3_cases`/`fin20_cases` (no
`fin_cases`); coordinates and projections are rewritten only with rfl lemmas on variables
(`encode20_apply_n`, `decode20_C/P/Q/R`, `ext3_zero/one/two`, `ledgerAct_*`, `pairExt_xy`)
and the Prod/Pi pointwise lemmas under `simp only`, then closed by `ring`. -/
module

public import Glennie.Compact.Affine20.Relabel
public import Glennie.Theorems.Frames
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Glennie.Compact.Affine20

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## The genuine affine domain -/

/-- The margin identities satisfied by the ledger of any triple of frames. -/
structure InDomain (L : Ledger54) : Prop where
  P_row : ∀ i, L.2.1 i 0 + L.2.1 i 1 + L.2.1 i 2 = 1
  P_col : ∀ j, L.2.1 0 j + L.2.1 1 j + L.2.1 2 j = 1
  Q_row : ∀ j, L.2.2.1 j 0 + L.2.2.1 j 1 + L.2.2.1 j 2 = 1
  Q_col : ∀ k, L.2.2.1 0 k + L.2.2.1 1 k + L.2.2.1 2 k = 1
  R_row : ∀ k, L.2.2.2 k 0 + L.2.2.2 k 1 + L.2.2.2 k 2 = 1
  R_col : ∀ i, L.2.2.2 0 i + L.2.2.2 1 i + L.2.2.2 2 i = 1
  C_k : ∀ i j, L.1 i j 0 + L.1 i j 1 + L.1 i j 2 = L.2.1 i j
  C_i : ∀ j k, L.1 0 j k + L.1 1 j k + L.1 2 j k = L.2.2.1 j k
  C_j : ∀ k i, L.1 i 0 k + L.1 i 1 k + L.1 i 2 k = L.2.2.2 k i

theorem pair_row (p q : Fin 3 → Albert) (hp : Frame p) (hq : Frame q) (i : Fin 3) :
    inner (p i) (q 0) + inner (p i) (q 1) + inner (p i) (q 2) = 1 := by
  rw [← inner_add_right, ← inner_add_right, hq.sum_unit, inner_unit_right, hp.trace_one]

theorem pair_col (p q : Fin 3 → Albert) (hp : Frame p) (hq : Frame q) (j : Fin 3) :
    inner (p 0) (q j) + inner (p 1) (q j) + inner (p 2) (q j) = 1 := by
  rw [inner_comm (p 0), inner_comm (p 1), inner_comm (p 2)]
  exact pair_row q p hq hp j

/-- The last-index margin of the triple ledger, written out over the three outcomes with
this file's numerals (the same algebra as the `ledger_last_marginal`). -/
theorem ledger_margin3 (p q r : Fin 3 → Albert) (hr : Frame r) (i j : Fin 3) :
    ledger p q r i j 0 + ledger p q r i j 1 + ledger p q r i j 2 = inner (p i) (q j) := by
  simp only [ledger]
  rw [← trace_add, ← trace_add, ← jordan_add_right, ← jordan_add_right, hr.sum_unit,
    jordan_unit_right]
  rfl

/-- Every triple of actual frames has its ledger in the affine domain. Each field first
rewrites the ledger projections with the variable-level lemmas `ledger54_C/P/Q/R`, so no
unification has to unfold Albert products. -/
theorem ledger54_inDomain (T : Triple) (hT : ∀ a, Frame (T a)) : InDomain (ledger54 T) where
  P_row i := by
    simp only [ledger54_P]
    exact pair_row (T 0) (T 1) (hT 0) (hT 1) i
  P_col j := by
    simp only [ledger54_P]
    exact pair_col (T 0) (T 1) (hT 0) (hT 1) j
  Q_row j := by
    simp only [ledger54_Q]
    exact pair_row (T 1) (T 2) (hT 1) (hT 2) j
  Q_col k := by
    simp only [ledger54_Q]
    exact pair_col (T 1) (T 2) (hT 1) (hT 2) k
  R_row k := by
    simp only [ledger54_R]
    exact pair_row (T 2) (T 0) (hT 2) (hT 0) k
  R_col i := by
    simp only [ledger54_R]
    exact pair_col (T 2) (T 0) (hT 2) (hT 0) i
  C_k i j := by
    simp only [ledger54_C, ledger54_P]
    exact ledger_margin3 (T 0) (T 1) (T 2) (hT 2) i j
  C_i j k := by
    simp only [ledger54_C, ledger54_Q]
    rw [ledger_cyclic (T 0) (T 1) (T 2) 0 j k, ledger_cyclic (T 0) (T 1) (T 2) 1 j k,
      ledger_cyclic (T 0) (T 1) (T 2) 2 j k]
    exact ledger_margin3 (T 1) (T 2) (T 0) (hT 0) j k
  C_j k i := by
    simp only [ledger54_C, ledger54_R]
    rw [ledger_cyclic (T 0) (T 1) (T 2) i 0 k, ledger_cyclic (T 0) (T 1) (T 2) i 1 k,
      ledger_cyclic (T 0) (T 1) (T 2) i 2 k, ledger_cyclic (T 1) (T 2) (T 0) 0 k i,
      ledger_cyclic (T 1) (T 2) (T 0) 1 k i, ledger_cyclic (T 1) (T 2) (T 0) 2 k i]
    exact ledger_margin3 (T 2) (T 0) (T 1) (hT 1) k i

/-! ## Zero-margin reconstruction -/

/-- (x, y, -(x + y)). -/
def ext3 (x y : ℝ) : Fin 3 → ℝ := ![x, y, -(x + y)]

/-- The 3x3 matrix with zero row and column sums and top-left 2x2 block (a b; c d). -/
def lift4 (a b c d : ℝ) (i j : Fin 3) : ℝ := ext3 (ext3 a b j) (ext3 c d j) i

/-- The 3x3x3 tensor with zero margins and 2x2x2 head (h_abc). -/
def lift8 (h000 h001 h010 h011 h100 h101 h110 h111 : ℝ) (i j k : Fin 3) : ℝ :=
  ext3 (ext3 (ext3 h000 h001 k) (ext3 h010 h011 k) j)
    (ext3 (ext3 h100 h101 k) (ext3 h110 h111 k) j) i

theorem ext3_zero (x y : ℝ) : ext3 x y 0 = x := rfl

theorem ext3_one (x y : ℝ) : ext3 x y 1 = y := rfl

theorem ext3_two (x y : ℝ) : ext3 x y 2 = -(x + y) := rfl

theorem ext3_reconstruct (v : Fin 3 → ℝ) (h : v 0 + v 1 + v 2 = 0) (i : Fin 3) :
    ext3 (v 0) (v 1) i = v i := by
  rcases fin3_cases i with rfl | rfl | rfl
  · exact ext3_zero _ _
  · exact ext3_one _ _
  · rw [ext3_two]
    linarith

theorem lift4_reconstruct (M : Fin 3 → Fin 3 → ℝ) (hr : ∀ i, M i 0 + M i 1 + M i 2 = 0)
    (hc : ∀ j, M 0 j + M 1 j + M 2 j = 0) (i j : Fin 3) :
    lift4 (M 0 0) (M 0 1) (M 1 0) (M 1 1) i j = M i j := by
  unfold lift4
  rw [ext3_reconstruct (M 0) (hr 0) j, ext3_reconstruct (M 1) (hr 1) j]
  exact ext3_reconstruct (fun l => M l j) (hc j) i

theorem lift8_reconstruct (H : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hx : ∀ j k, H 0 j k + H 1 j k + H 2 j k = 0)
    (hy : ∀ i k, H i 0 k + H i 1 k + H i 2 k = 0)
    (hz : ∀ i j, H i j 0 + H i j 1 + H i j 2 = 0) (i j k : Fin 3) :
    lift8 (H 0 0 0) (H 0 0 1) (H 0 1 0) (H 0 1 1) (H 1 0 0) (H 1 0 1) (H 1 1 0) (H 1 1 1)
      i j k = H i j k := by
  unfold lift8
  rw [ext3_reconstruct (H 0 0) (hz 0 0) k, ext3_reconstruct (H 0 1) (hz 0 1) k,
    ext3_reconstruct (H 1 0) (hz 1 0) k, ext3_reconstruct (H 1 1) (hz 1 1) k,
    ext3_reconstruct (fun l => H 0 l k) (hy 0 k) j, ext3_reconstruct (fun l => H 1 l k) (hy 1 k) j]
  exact ext3_reconstruct (fun l => H l j k) (hx j k) i

/-! ## The chart -/

/-- The centred triple tensor H = C - (P + Q + R)/3 + 2/9. -/
def centred (L : Ledger54) (i j k : Fin 3) : ℝ :=
  L.1 i j k - (L.2.1 i j + L.2.2.1 j k + L.2.2.2 k i) / 3 + 2 / 9

/-- The 20 chart coordinates: 2x2 heads of P - 1/3, Q - 1/3, R - 1/3, and the 2x2x2 head of
the centred tensor. -/
def encode20 (L : Ledger54) : Fin 20 → ℝ :=
  ![L.2.1 0 0 - 1 / 3, L.2.1 0 1 - 1 / 3, L.2.1 1 0 - 1 / 3, L.2.1 1 1 - 1 / 3,
    L.2.2.1 0 0 - 1 / 3, L.2.2.1 0 1 - 1 / 3, L.2.2.1 1 0 - 1 / 3, L.2.2.1 1 1 - 1 / 3,
    L.2.2.2 0 0 - 1 / 3, L.2.2.2 0 1 - 1 / 3, L.2.2.2 1 0 - 1 / 3, L.2.2.2 1 1 - 1 / 3,
    centred L 0 0 0, centred L 0 0 1, centred L 0 1 0, centred L 0 1 1,
    centred L 1 0 0, centred L 1 0 1, centred L 1 1 0, centred L 1 1 1]

def decP (v : Fin 20 → ℝ) (i j : Fin 3) : ℝ := 1 / 3 + lift4 (v 0) (v 1) (v 2) (v 3) i j

def decQ (v : Fin 20 → ℝ) (j k : Fin 3) : ℝ := 1 / 3 + lift4 (v 4) (v 5) (v 6) (v 7) j k

def decR (v : Fin 20 → ℝ) (k i : Fin 3) : ℝ := 1 / 3 + lift4 (v 8) (v 9) (v 10) (v 11) k i

def decC (v : Fin 20 → ℝ) (i j k : Fin 3) : ℝ :=
  lift8 (v 12) (v 13) (v 14) (v 15) (v 16) (v 17) (v 18) (v 19) i j k +
    (decP v i j + decQ v j k + decR v k i) / 3 - 2 / 9

/-- The 54 entries rebuilt from the 20 chart coordinates. -/
def decode20 (v : Fin 20 → ℝ) : Ledger54 := (decC v, decP v, decQ v, decR v)

theorem decode20_C (v : Fin 20 → ℝ) : (decode20 v).1 = decC v := rfl

theorem decode20_P (v : Fin 20 → ℝ) : (decode20 v).2.1 = decP v := rfl

theorem decode20_Q (v : Fin 20 → ℝ) : (decode20 v).2.2.1 = decQ v := rfl

theorem decode20_R (v : Fin 20 → ℝ) : (decode20 v).2.2.2 = decR v := rfl

/-! Coordinate values of the chart (rfl on a variable ledger). -/

theorem encode20_apply_0 (L : Ledger54) : encode20 L 0 = L.2.1 0 0 - 1 / 3 := rfl

theorem encode20_apply_1 (L : Ledger54) : encode20 L 1 = L.2.1 0 1 - 1 / 3 := rfl

theorem encode20_apply_2 (L : Ledger54) : encode20 L 2 = L.2.1 1 0 - 1 / 3 := rfl

theorem encode20_apply_3 (L : Ledger54) : encode20 L 3 = L.2.1 1 1 - 1 / 3 := rfl

theorem encode20_apply_4 (L : Ledger54) : encode20 L 4 = L.2.2.1 0 0 - 1 / 3 := rfl

theorem encode20_apply_5 (L : Ledger54) : encode20 L 5 = L.2.2.1 0 1 - 1 / 3 := rfl

theorem encode20_apply_6 (L : Ledger54) : encode20 L 6 = L.2.2.1 1 0 - 1 / 3 := rfl

theorem encode20_apply_7 (L : Ledger54) : encode20 L 7 = L.2.2.1 1 1 - 1 / 3 := rfl

theorem encode20_apply_8 (L : Ledger54) : encode20 L 8 = L.2.2.2 0 0 - 1 / 3 := rfl

theorem encode20_apply_9 (L : Ledger54) : encode20 L 9 = L.2.2.2 0 1 - 1 / 3 := rfl

theorem encode20_apply_10 (L : Ledger54) : encode20 L 10 = L.2.2.2 1 0 - 1 / 3 := rfl

theorem encode20_apply_11 (L : Ledger54) : encode20 L 11 = L.2.2.2 1 1 - 1 / 3 := rfl

theorem encode20_apply_12 (L : Ledger54) : encode20 L 12 = centred L 0 0 0 := rfl

theorem encode20_apply_13 (L : Ledger54) : encode20 L 13 = centred L 0 0 1 := rfl

theorem encode20_apply_14 (L : Ledger54) : encode20 L 14 = centred L 0 1 0 := rfl

theorem encode20_apply_15 (L : Ledger54) : encode20 L 15 = centred L 0 1 1 := rfl

theorem encode20_apply_16 (L : Ledger54) : encode20 L 16 = centred L 1 0 0 := rfl

theorem encode20_apply_17 (L : Ledger54) : encode20 L 17 = centred L 1 0 1 := rfl

theorem encode20_apply_18 (L : Ledger54) : encode20 L 18 = centred L 1 1 0 := rfl

theorem encode20_apply_19 (L : Ledger54) : encode20 L 19 = centred L 1 1 1 := rfl

/-- Fin 20 has exactly the elements 0, …, 19 (kernel-checked Boolean list check). -/
theorem fin20_cases (n : Fin 20) :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨
      n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨
        n = 19 := by
  have hb : (List.finRange 20).all (fun n => decide (n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨
      n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨
        n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp hb n (List.mem_finRange n))

theorem decP_encode (L : Ledger54) (h : InDomain L) (i j : Fin 3) :
    decP (encode20 L) i j = L.2.1 i j := by
  have hr : ∀ i, (L.2.1 i 0 - 1 / 3) + (L.2.1 i 1 - 1 / 3) + (L.2.1 i 2 - 1 / 3) = 0 := by
    intro i
    linarith [h.P_row i]
  have hc : ∀ j, (L.2.1 0 j - 1 / 3) + (L.2.1 1 j - 1 / 3) + (L.2.1 2 j - 1 / 3) = 0 := by
    intro j
    linarith [h.P_col j]
  have key : lift4 (encode20 L 0) (encode20 L 1) (encode20 L 2) (encode20 L 3) i j =
      L.2.1 i j - 1 / 3 :=
    lift4_reconstruct (fun i j => L.2.1 i j - 1 / 3) hr hc i j
  show 1 / 3 + lift4 (encode20 L 0) (encode20 L 1) (encode20 L 2) (encode20 L 3) i j =
    L.2.1 i j
  rw [key]
  ring

theorem decQ_encode (L : Ledger54) (h : InDomain L) (j k : Fin 3) :
    decQ (encode20 L) j k = L.2.2.1 j k := by
  have hr : ∀ j, (L.2.2.1 j 0 - 1 / 3) + (L.2.2.1 j 1 - 1 / 3) + (L.2.2.1 j 2 - 1 / 3) = 0 := by
    intro j
    linarith [h.Q_row j]
  have hc : ∀ k, (L.2.2.1 0 k - 1 / 3) + (L.2.2.1 1 k - 1 / 3) + (L.2.2.1 2 k - 1 / 3) = 0 := by
    intro k
    linarith [h.Q_col k]
  have key : lift4 (encode20 L 4) (encode20 L 5) (encode20 L 6) (encode20 L 7) j k =
      L.2.2.1 j k - 1 / 3 :=
    lift4_reconstruct (fun j k => L.2.2.1 j k - 1 / 3) hr hc j k
  show 1 / 3 + lift4 (encode20 L 4) (encode20 L 5) (encode20 L 6) (encode20 L 7) j k =
    L.2.2.1 j k
  rw [key]
  ring

theorem decR_encode (L : Ledger54) (h : InDomain L) (k i : Fin 3) :
    decR (encode20 L) k i = L.2.2.2 k i := by
  have hr : ∀ k, (L.2.2.2 k 0 - 1 / 3) + (L.2.2.2 k 1 - 1 / 3) + (L.2.2.2 k 2 - 1 / 3) = 0 := by
    intro k
    linarith [h.R_row k]
  have hc : ∀ i, (L.2.2.2 0 i - 1 / 3) + (L.2.2.2 1 i - 1 / 3) + (L.2.2.2 2 i - 1 / 3) = 0 := by
    intro i
    linarith [h.R_col i]
  have key : lift4 (encode20 L 8) (encode20 L 9) (encode20 L 10) (encode20 L 11) k i =
      L.2.2.2 k i - 1 / 3 :=
    lift4_reconstruct (fun k i => L.2.2.2 k i - 1 / 3) hr hc k i
  show 1 / 3 + lift4 (encode20 L 8) (encode20 L 9) (encode20 L 10) (encode20 L 11) k i =
    L.2.2.2 k i
  rw [key]
  ring

theorem decC_encode (L : Ledger54) (h : InDomain L) (i j k : Fin 3) :
    decC (encode20 L) i j k = L.1 i j k := by
  have hx : ∀ j k, centred L 0 j k + centred L 1 j k + centred L 2 j k = 0 := by
    intro j k
    simp only [centred]
    linarith [h.C_i j k, h.P_col j, h.R_row k]
  have hy : ∀ i k, centred L i 0 k + centred L i 1 k + centred L i 2 k = 0 := by
    intro i k
    simp only [centred]
    linarith [h.C_j k i, h.P_row i, h.Q_col k]
  have hz : ∀ i j, centred L i j 0 + centred L i j 1 + centred L i j 2 = 0 := by
    intro i j
    simp only [centred]
    linarith [h.C_k i j, h.Q_row j, h.R_col i]
  have key : lift8 (encode20 L 12) (encode20 L 13) (encode20 L 14) (encode20 L 15)
      (encode20 L 16) (encode20 L 17) (encode20 L 18) (encode20 L 19) i j k = centred L i j k :=
    lift8_reconstruct (centred L) hx hy hz i j k
  show lift8 (encode20 L 12) (encode20 L 13) (encode20 L 14) (encode20 L 15)
      (encode20 L 16) (encode20 L 17) (encode20 L 18) (encode20 L 19) i j k +
      (decP (encode20 L) i j + decQ (encode20 L) j k + decR (encode20 L) k i) / 3 - 2 / 9 =
    L.1 i j k
  rw [key, decP_encode L h, decQ_encode L h, decR_encode L h]
  simp only [centred]
  ring

/-- On the genuine domain the chart is inverted by decode20. -/
theorem decode_encode (L : Ledger54) (h : InDomain L) : decode20 (encode20 L) = L := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · rw [decode20_C]
    funext i j k
    exact decC_encode L h i j k
  · rw [decode20_P]
    funext i j
    exact decP_encode L h i j
  · rw [decode20_Q]
    funext j k
    exact decQ_encode L h j k
  · rw [decode20_R]
    funext k i
    exact decR_encode L h k i

/-- The chart inverts on the ledger of every triple of actual frames. -/
theorem decode_encode_frames (T : Triple) (hT : ∀ a, Frame (T a)) :
    decode20 (encode20 (ledger54 T)) = ledger54 T :=
  decode_encode _ (ledger54_inDomain T hT)

/-- The chart is injective on the genuine domain. -/
theorem encode20_injOn {L L' : Ledger54} (h : InDomain L) (h' : InDomain L')
    (he : encode20 L = encode20 L') : L = L' := by
  rw [← decode_encode L h, ← decode_encode L' h', he]

/-! ## Affine maps (preservation of affine combinations) -/

/-- `f` preserves affine combinations: f (x + t (y - x)) = f x + t (f y - f x). -/
def AffineComb {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (f : E → F) : Prop :=
  ∀ (x y : E) (t : ℝ), f (x + t • (y - x)) = f x + t • (f y - f x)

theorem AffineComb.comp {E F G : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] [AddCommGroup G] [Module ℝ G] {f : E → F} {g : F → G}
    (hg : AffineComb g) (hf : AffineComb f) : AffineComb (fun x => g (f x)) := by
  intro x y t
  show g (f (x + t • (y - x))) = g (f x) + t • (g (f y) - g (f x))
  rw [hf x y t]
  exact hg (f x) (f y) t

/-! The proofs below split indices with the Boolean case lemmas, rewrite only with
variable-level rfl lemmas and the Prod/Pi pointwise lemmas (`simp only`), and close with
`ring`. No step compares two different structures by unfolding. -/

theorem encode20_affine : AffineComb encode20 := by
  intro x y t
  funext n
  rcases fin20_cases n with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [encode20_apply_0, encode20_apply_1, encode20_apply_2, encode20_apply_3,
      encode20_apply_4, encode20_apply_5, encode20_apply_6, encode20_apply_7, encode20_apply_8,
      encode20_apply_9, encode20_apply_10, encode20_apply_11, encode20_apply_12,
      encode20_apply_13, encode20_apply_14, encode20_apply_15, encode20_apply_16,
      encode20_apply_17, encode20_apply_18, encode20_apply_19, centred, Prod.fst_add,
      Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;>
    ring

theorem decode20_affine : AffineComb decode20 := by
  intro x y t
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext i j k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases j with rfl | rfl | rfl <;>
      rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [decode20_C, decode20_P, decode20_Q, decode20_R, decC, decP, decQ, decR, lift8,
        lift4, ext3_zero, ext3_one, ext3_two, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
        Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul] <;>
      ring
  · funext i j
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases j with rfl | rfl | rfl <;>
      simp only [decode20_P, decP, lift4, ext3_zero, ext3_one, ext3_two, Prod.fst_add,
        Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;>
      ring
  · funext j k
    rcases fin3_cases j with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [decode20_Q, decQ, lift4, ext3_zero, ext3_one, ext3_two, Prod.fst_add,
        Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;>
      ring
  · funext k i
    rcases fin3_cases k with rfl | rfl | rfl <;> rcases fin3_cases i with rfl | rfl | rfl <;>
      simp only [decode20_R, decR, lift4, ext3_zero, ext3_one, ext3_two, Prod.fst_add,
        Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;>
      ring

theorem pairExt_affine (x y : Ledger54) (t : ℝ) (f g u w : Fin 3) :
    pairExt (x + t • (y - x)) f g u w =
      pairExt x f g u w + t * (pairExt y f g u w - pairExt x f g u w) := by
  rcases fin3_cases f with rfl | rfl | rfl <;> rcases fin3_cases g with rfl | rfl | rfl <;>
    simp only [pairExt_00, pairExt_01, pairExt_02, pairExt_10, pairExt_11, pairExt_12,
      pairExt_20, pairExt_21, pairExt_22, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;>
    ring

theorem ledgerAct_affine (γ : Relabel) : AffineComb (ledgerAct γ) := by
  intro x y t
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext i j k
    simp only [ledgerAct_C, Prod.fst_add, Prod.fst_sub, Prod.smul_fst, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
  · funext i j
    simp only [ledgerAct_P, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact pairExt_affine x y t _ _ _ _
  · funext j k
    simp only [ledgerAct_Q, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact pairExt_affine x y t _ _ _ _
  · funext k i
    simp only [ledgerAct_R, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact pairExt_affine x y t _ _ _ _

/-! ## The relabelling action in chart coordinates -/

/-- γ acting on the 20 chart coordinates. -/
def act20 (γ : Relabel) (b : Fin 20 → ℝ) : Fin 20 → ℝ := encode20 (ledgerAct γ (decode20 b))

theorem act20_affine (γ : Relabel) : AffineComb (act20 γ) :=
  AffineComb.comp (f := decode20) (g := fun L => encode20 (ledgerAct γ L))
    (AffineComb.comp (f := ledgerAct γ) (g := encode20) encode20_affine (ledgerAct_affine γ))
    decode20_affine

/-- Chart equivariance for actual frame triples: relabelling the triple moves its chart
point by `act20`. -/
theorem relabel_ledger (γ : Relabel) (T : Triple) (hT : ∀ a, Frame (T a)) :
    act20 γ (encode20 (ledger54 T)) = encode20 (ledger54 (relabelTriple γ T)) := by
  unfold act20
  rw [decode_encode _ (ledger54_inDomain T hT), ledger54_relabel γ T]

/-- Product automorphisms do not move the chart point. -/
theorem encode20_map (g : CompactAutomorphism) (T : Triple) :
    encode20 (ledger54 (mapAtoms g T)) = encode20 (ledger54 T) := by
  rw [ledger54_map]

end
end Glennie.Compact.Affine20
