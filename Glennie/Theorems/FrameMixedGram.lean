module

public import Glennie.Native.TraceOneU
public import Glennie.Theorems.Frames
public import Glennie.Theorems.UniformMixedGram
public import Mathlib.Tactic.FinCases
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/- The uniform mixed-product Gram table is derived in the native compact algebra. -/

@[expose] public section
namespace Glennie
noncomputable section

set_option maxHeartbeats 2000000

theorem traceOne_idempotent_L_square (p q : Albert)
    (hp : jordan p p = p) (ht : trace p = 1) :
    jordan p (jordan p q) = (1 / 2 : ℝ) • (inner p q • p + jordan p q) := by
  calc
    _ = (1 / 2 : ℝ) • (U p q + jordan p q) := by unfold U; rw [hp]; module
    _ = _ := by rw [traceOne_idempotent_U p q hp ht]

/-- Orthogonal idempotents have commuting multiplication operators. -/
theorem orthogonal_idempotents_L_commute (p k y : Albert)
    (hp : jordan p p = p) (hk : jordan k k = k) (hpk : jordan p k = 0) :
    jordan p (jordan k y) = jordan k (jordan p y) := by
  have hkp : jordan k p = 0 := by rw [jordan_comm]; exact hpk
  have hs : jordan (p-k) (p-k) = p+k := by
    simp [jordan_sub_left, jordan_sub_right, hp, hk, hpk, hkp]
  have hj := jordan_identity (p-k) y
  rw [hs] at hj
  have heq : (2 : ℝ) • (jordan k (jordan p y) - jordan p (jordan k y)) = 0 := by
    calc
      _ = jordan (jordan (p-k) y) (p+k) - jordan (p-k) (jordan y (p+k)) := by
        simp only [jordan_sub_left, jordan_sub_right, jordan_add_left, jordan_add_right,
          jordan_comm (jordan p y) p, jordan_comm (jordan p y) k,
          jordan_comm (jordan k y) p, jordan_comm (jordan k y) k,
          jordan_comm y p, jordan_comm y k]
        module
      _ = 0 := sub_eq_zero.mpr hj
  have hhalf := congrArg (fun z : Albert => (1 / 2 : ℝ) • z) heq
  have hz : jordan k (jordan p y) - jordan p (jordan k y) = 0 := by
    simpa only [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num,
      one_smul, smul_zero] using hhalf
  exact (sub_eq_zero.mp hz).symm

theorem traceOne_mixed_inner (p q r : Albert)
    (hp : jordan p p = p) (ht : trace p = 1) :
    inner (jordan p q) (jordan p r) =
      (inner p q * inner p r + inner p (jordan q r)) / 2 := by
  have ha : inner q (jordan p r) = inner p (jordan q r) := by
    rw [jordan_comm p r, ← inner_jordan_associative, inner_comm]
  rw [jordan_comm p q, inner_jordan_associative,
    traceOne_idempotent_L_square p r hp ht, inner_smul_right,
    inner_add_right, inner_smul_right, inner_comm q p, ha]
  ring

private theorem symmetric_three_zero_rows (B : Fin 3 → Fin 3 → ℝ)
    (hsym : ∀ j l, B j l = B l j) (hdiag : ∀ j, B j j = 1 / 18)
    (hrow : ∀ j, ∑ l, B j l = 0) (j l : Fin 3) (hne : j ≠ l) :
    B j l = -1 / 36 := by
  have h0 := hrow 0
  have h1 := hrow 1
  have h2 := hrow 2
  have h01 := hsym 0 1
  have h02 := hsym 0 2
  have h12 := hsym 1 2
  simp only [Fin.sum_univ_three, hdiag] at h0 h1 h2
  have ho01 : B 0 1 = -1/36 := by linarith
  have ho02 : B 0 2 = -1/36 := by linarith
  have ho12 : B 1 2 = -1/36 := by linarith
  have ho10 := h01.symm.trans ho01
  have ho20 := h02.symm.trans ho02
  have ho21 := h12.symm.trans ho12
  fin_cases j <;> fin_cases l
  · exact (hne rfl).elim
  · exact ho01
  · exact ho02
  · exact ho10
  · exact (hne rfl).elim
  · exact ho12
  · exact ho20
  · exact ho21
  · exact (hne rfl).elim

theorem uniform_pair_same_row (p q : Fin 3 → Albert)
    (hp : Frame p) (hq : Frame q) (hu : ∀ i j, inner (p i) (q j) = 1 / 3)
    (i j l : Fin 3) :
    inner (jordan (p i) (q j)) (jordan (p i) (q l)) =
      if j = l then 2 / 9 else 1 / 18 := by
  rw [traceOne_mixed_inner _ _ _ (hp.idempotent i) (hp.trace_one i), hu, hu]
  by_cases h : j = l
  · subst l
    rw [hq.idempotent, hu]
    norm_num
  · rw [hq.orthogonal j l h, inner, jordan_zero_right]
    norm_num [h, trace]

theorem uniform_pair_same_column (p q : Fin 3 → Albert)
    (hp : Frame p) (hq : Frame q) (hu : ∀ i j, inner (p i) (q j) = 1 / 3)
    (i k j : Fin 3) :
    inner (jordan (p i) (q j)) (jordan (p k) (q j)) =
      if i = k then 2 / 9 else 1 / 18 := by
  rw [jordan_comm (p i) (q j), jordan_comm (p k) (q j)]
  exact uniform_pair_same_row q p hq hp (fun j i => by rw [inner_comm, hu]) j i k

/-- Every uniformly overlapping pair of native frames has this exact 9-by-9 Gram table. -/
theorem uniform_pair_mixed_gram (p q : Fin 3 → Albert)
    (hp : Frame p) (hq : Frame q) (hu : ∀ i j, inner (p i) (q j) = 1 / 3)
    (i j k l : Fin 3) :
    inner (jordan (p i) (q j)) (jordan (p k) (q l)) =
      UniformMixedGram.gramEntry i j k l := by
  by_cases hik : i = k
  · subst k
    simpa [UniformMixedGram.gramEntry] using uniform_pair_same_row p q hp hq hu i j l
  · by_cases hjl : j = l
    · subst l
      simpa [UniformMixedGram.gramEntry, hik] using uniform_pair_same_column p q hp hq hu i k j
    · let B : Fin 3 → Fin 3 → ℝ := fun j l =>
        inner (jordan (p i) (q j)) (jordan (p k) (q l))
      have hsym : ∀ j l, B j l = B l j := by
        intro j l
        dsimp [B]
        calc
          _ = inner (q j) (jordan (p i) (jordan (p k) (q l))) := by
            rw [jordan_comm (p i) (q j), inner_jordan_associative]
          _ = inner (q j) (jordan (p k) (jordan (p i) (q l))) := by
            rw [orthogonal_idempotents_L_commute _ _ _ (hp.idempotent i)
              (hp.idempotent k) (hp.orthogonal i k hik)]
          _ = _ := by rw [← inner_jordan_associative, jordan_comm (q j) (p k), inner_comm]
      have hdiag : ∀ j, B j j = 1 / 18 := by
        intro j
        exact (uniform_pair_same_column p q hp hq hu i k j).trans (if_neg hik)
      have hrow : ∀ j, ∑ l, B j l = 0 := by
        intro j
        dsimp [B]
        simp only [Fin.sum_univ_three]
        rw [← inner_add_right, ← inner_add_right, ← jordan_add_right,
          ← jordan_add_right, hq.sum_unit, jordan_unit_right]
        rw [jordan_comm (p i) (q j), inner_jordan_associative,
          hp.orthogonal i k hik, inner, jordan_zero_right]
        simp [trace]
      have h := symmetric_three_zero_rows B hsym hdiag hrow j l hjl
      simpa [B, UniformMixedGram.gramEntry, hik, hjl] using h

def mixedCombination (p q : Fin 3 → Albert) (a : Fin 3 → Fin 3 → ℝ) : Albert :=
  ∑ i, ∑ j, a i j • jordan (p i) (q j)

theorem uniform_pair_combination_inner (p q : Fin 3 → Albert)
    (hp : Frame p) (hq : Frame q) (hu : ∀ i j, inner (p i) (q j) = 1 / 3)
    (a : Fin 3 → Fin 3 → ℝ) :
    inner (mixedCombination p q a) (mixedCombination p q a) =
      UniformMixedGram.quadratic a := by
  simp only [mixedCombination, UniformMixedGram.quadratic, Fin.sum_univ_three,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    uniform_pair_mixed_gram p q hp hq hu]
  ring

/-- All nine native mixed products are independent; no sector-normalization premise. -/
theorem uniform_pair_mixed_independent (p q : Fin 3 → Albert)
    (hp : Frame p) (hq : Frame q) (hu : ∀ i j, inner (p i) (q j) = 1 / 3)
    (a : Fin 3 → Fin 3 → ℝ) :
    mixedCombination p q a = 0 ↔ ∀ i j, a i j = 0 := by
  constructor
  · intro hz
    apply (UniformMixedGram.quadratic_eq_zero_iff a).mp
    rw [← uniform_pair_combination_inner p q hp hq hu, hz]
    simp [inner, trace]
  · intro hz
    simp [mixedCombination, hz]

/-- The standard library linear-independence predicate for the nine native products. -/
theorem uniform_pair_mixed_linearIndependent (p q : Fin 3 → Albert)
    (hp : Frame p) (hq : Frame q) (hu : ∀ i j, inner (p i) (q j) = 1 / 3) :
    LinearIndependent ℝ (fun u : Fin 3 × Fin 3 => jordan (p u.1) (q u.2)) := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha u
  have hz : mixedCombination p q (fun i j => a (i,j)) = 0 := by
    simpa only [mixedCombination, Fintype.sum_prod_type] using ha
  exact (uniform_pair_mixed_independent p q hp hq hu _).mp hz u.1 u.2

/-- A uniform ledger gives the native pairings of every frame projector. -/
theorem uniformLedger_mixed_projector_perp (p q r : Fin 3 → Albert)
    (hr : Frame r) (hu : UniformLedger p q r) (i j k : Fin 3) :
    inner (jordan (p i) (q j)) (r k - (1 / 3 : ℝ) • (1 : Albert)) = 0 := by
  have hk : inner (jordan (p i) (q j)) (r k) = 1 / 9 := hu i j k
  have hunit : inner (jordan (p i) (q j)) (1 : Albert) = 1 / 3 := by
    rw [inner, jordan_unit_right]
    exact uniformLedger_pair_overlap p q r hr hu i j
  rw [inner_sub_right, inner_smul_right, hk, hunit]
  norm_num

theorem uniformLedger_mixed_encoder_perp (p q r : Fin 3 → Albert)
    (hu : UniformLedger p q r) (i j : Fin 3) :
    inner (jordan (p i) (q j)) (encoder r) = 0 := by
  have h0 : inner (jordan (p i) (q j)) (r 0) = 1 / 9 := hu i j 0
  have h2 : inner (jordan (p i) (q j)) (r 2) = 1 / 9 := hu i j 2
  rw [encoder, inner_sub_right, h2, h0]
  norm_num

theorem uniformLedger_mixed_encoder_square_perp (p q r : Fin 3 → Albert)
    (hr : Frame r) (hu : UniformLedger p q r) (i j : Fin 3) :
    inner (jordan (p i) (q j))
      (jordan (encoder r) (encoder r) - (2 / 3 : ℝ) • (1 : Albert)) = 0 := by
  have h0 : inner (jordan (p i) (q j)) (r 0) = 1 / 9 := hu i j 0
  have h2 : inner (jordan (p i) (q j)) (r 2) = 1 / 9 := hu i j 2
  have hunit : inner (jordan (p i) (q j)) (1 : Albert) = 1 / 3 := by
    rw [inner, jordan_unit_right]
    exact uniformLedger_pair_overlap p q r hr hu i j
  rw [frame_encoder_square r hr, inner_sub_right, inner_add_right,
    inner_smul_right, h2, h0, hunit]
  norm_num

end
end Glennie
