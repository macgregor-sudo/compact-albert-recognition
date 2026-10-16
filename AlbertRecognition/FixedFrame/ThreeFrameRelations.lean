/- Actual three-frame coefficient relations for the bounded algebraic gate.
The coarse action data below are explicitly intermediate obligations.  They
must be constructed from the arbitrary-cubic Jacobi kernel by native frame
pullback and the derived scalar-block theorem; this file does not assume or
claim that construction, unknown invariance, or the final recognition theorem. -/
module

public import AlbertRecognition.CubicOperators

@[expose] public section
namespace AlbertRecognition.FixedFrame
noncomputable section
open Glennie

/-- Intermediate coarse action data on the three actual native frames.
No full operator proportionality, Jordan identity, or unknown invariance is a
field.  Existence from A(q referenceCubic)B=0 remains a separate obligation. -/
structure ThreeFrameScalarData (B : SymmetricCubic) where
  a : Fin 3 → ℝ
  b : Fin 3 → ℝ
  c : Fin 3 → ℝ
  on_h_self : ∀ i, KB B (h i) (h i) = a i • h i
  on_complementary_diagonal : ∀ (i j : Fin 3), i ≠ j →
    KB B (h i) (h j + (1/2 : ℝ) • h i) =
      b i • (h j + (1/2 : ℝ) • h i)
  on_X01 : ∀ u : Octonion,
    KB B (h 0) (X01 u) = c 0 • X01 u ∧
    KB B (h 1) (X01 u) = c 1 • X01 u ∧
    KB B (h 2) (X01 u) = b 2 • X01 u
  on_X02 : ∀ u : Octonion,
    KB B (h 0) (X02 u) = c 0 • X02 u ∧
    KB B (h 1) (X02 u) = b 1 • X02 u ∧
    KB B (h 2) (X02 u) = c 2 • X02 u
  on_X12 : ∀ u : Octonion,
    KB B (h 0) (X12 u) = b 0 • X12 u ∧
    KB B (h 1) (X12 u) = c 1 • X12 u ∧
    KB B (h 2) (X12 u) = c 2 • X12 u

/-- Distinct actual h_i are independent, proved by their native diagonal values. -/
theorem h_pair_coefficients (i j : Fin 3) (hij : i ≠ j)
    (u v r s : ℝ) (heq : u • h i + v • h j = r • h i + s • h j) :
    u = r ∧ v = s := by
  have h0 := congrArg (fun x : V => (x : Albert).d0) heq
  have h1 := congrArg (fun x : V => (x : Albert).d1) heq
  have h2 := congrArg (fun x : V => (x : Albert).d2) heq
  fin_cases i <;> fin_cases j
  all_goals first | exact False.elim (hij rfl) | skip
  all_goals norm_num [h, e, unit] at h0 h1 h2
  all_goals constructor <;> linarith

/-- The complementary diagonal action gives the actual cross-h formula. -/
theorem ThreeFrameScalarData.cross_h {B : SymmetricCubic}
    (data : ThreeFrameScalarData B) (i j : Fin 3) (hij : i ≠ j) :
    KB B (h i) (h j) =
      data.b i • h j + ((data.b i - data.a i)/2) • h i := by
  calc
    KB B (h i) (h j) =
        KB B (h i) (h j + (1/2 : ℝ) • h i) -
          (1/2 : ℝ) • KB B (h i) (h i) := by
      rw [map_add, map_smul]
      module
    _ = data.b i • (h j + (1/2 : ℝ) • h i) -
        (1/2 : ℝ) • (data.a i • h i) := by
      rw [data.on_complementary_diagonal i j hij, data.on_h_self]
    _ = _ := by module

/-- Actual cubic symmetry forces the two diagonal coefficients to agree. -/
theorem ThreeFrameScalarData.a_eq_b_sub_two_b {B : SymmetricCubic}
    (data : ThreeFrameScalarData B) (i j : Fin 3) (hij : i ≠ j) :
    data.a i = data.b i - 2 * data.b j := by
  have hcross :
      ((data.b i - data.a i)/2) • h i + data.b i • h j =
        data.b j • h i + ((data.b j - data.a j)/2) • h j := by
    calc
      ((data.b i - data.a i)/2) • h i + data.b i • h j =
          KB B (h i) (h j) := by
        rw [data.cross_h i j hij]
        module
      _ = KB B (h j) (h i) := KB_comm B (h i) (h j)
      _ = _ := data.cross_h j i hij.symm
  have hc := (h_pair_coefficients i j hij
    ((data.b i - data.a i)/2) (data.b i) (data.b j)
    ((data.b j - data.a j)/2) hcross).1
  linarith

/-- h0+h1+h2=0 gives a sum of actual unknown multiplication operators. -/
theorem KB_h_sum_zero (B : SymmetricCubic) (v : V) :
    KB B (h 0) v + KB B (h 1) v + KB B (h 2) v = 0 := by
  have hs := congrArg (fun x : V => KB B x v) h_sum_zero
  simpa only [map_add, LinearMap.add_apply, map_zero, LinearMap.zero_apply] using hs

/-- The three literal raw-slot scalar equations use native octScalar1, not the
inherited unit on a pair of quaternions. -/
theorem ThreeFrameScalarData.slot_relations {B : SymmetricCubic}
    (data : ThreeFrameScalarData B) :
    data.c 0 + data.c 1 + data.b 2 = 0 ∧
      data.c 0 + data.b 1 + data.c 2 = 0 ∧
      data.b 0 + data.c 1 + data.c 2 = 0 := by
  have h01 := KB_h_sum_zero B (X01 (octScalar 1))
  obtain ⟨hx0,hx1,hx2⟩ := data.on_X01 (octScalar 1)
  rw [hx0,hx1,hx2] at h01
  have r01 := congrArg (fun x : V => (x : Albert).o01.1.re) h01
  have h02 := KB_h_sum_zero B (X02 (octScalar 1))
  obtain ⟨hy0,hy1,hy2⟩ := data.on_X02 (octScalar 1)
  rw [hy0,hy1,hy2] at h02
  have r02 := congrArg (fun x : V => (x : Albert).o02.1.re) h02
  have h12 := KB_h_sum_zero B (X12 (octScalar 1))
  obtain ⟨hz0,hz1,hz2⟩ := data.on_X12 (octScalar 1)
  rw [hz0,hz1,hz2] at h12
  have r12 := congrArg (fun x : V => (x : Albert).o12.1.re) h12
  norm_num [X01, X02, X12, octScalar] at r01 r02 r12
  exact ⟨r01,r02,r12⟩

/-- The actual three-frame equations force one common coefficient and the
reference ratio (-1,1,-1/2). This is an intermediate data theorem; the data
must still be derived from the Jacobi kernel, not assumed as a final endpoint. -/
theorem ThreeFrameScalarData.common_coefficients {B : SymmetricCubic}
    (data : ThreeFrameScalarData B) :
    ∃ b : ℝ, (∀ i, data.a i = -b) ∧ (∀ i, data.b i = b) ∧
      (∀ i, data.c i = -b/2) := by
  have h01 := data.a_eq_b_sub_two_b 0 1 (by decide)
  have h02 := data.a_eq_b_sub_two_b 0 2 (by decide)
  have h10 := data.a_eq_b_sub_two_b 1 0 (by decide)
  have h12 := data.a_eq_b_sub_two_b 1 2 (by decide)
  have h20 := data.a_eq_b_sub_two_b 2 0 (by decide)
  have hb12 : data.b 1 = data.b 2 := by linarith
  have hb02 : data.b 0 = data.b 2 := by linarith
  have hb : ∀ i : Fin 3, data.b i = data.b 0 := by
    intro i
    fin_cases i
    · change data.b (0 : Fin 3) = data.b 0
      rfl
    · change data.b (1 : Fin 3) = data.b 0
      exact hb12.trans hb02.symm
    · change data.b (2 : Fin 3) = data.b 0
      exact hb02.symm
  have ha : ∀ i : Fin 3, data.a i = -data.b 0 := by
    intro i
    fin_cases i
    · change data.a (0 : Fin 3) = -data.b 0
      rw [hb 1] at h01
      linarith only [h01]
    · change data.a (1 : Fin 3) = -data.b 0
      rw [hb 1] at h10
      linarith only [h10]
    · change data.a (2 : Fin 3) = -data.b 0
      rw [hb 2] at h20
      linarith only [h20]
  obtain ⟨hc01,hc02,hc12⟩ := data.slot_relations
  rw [hb 2] at hc01
  rw [hb 1] at hc02
  have hc : ∀ i : Fin 3, data.c i = -data.b 0/2 := by
    intro i
    fin_cases i
    · change data.c (0 : Fin 3) = -data.b 0/2
      linarith only [hc01, hc02, hc12]
    · change data.c (1 : Fin 3) = -data.b 0/2
      linarith only [hc01, hc02, hc12]
    · change data.c (2 : Fin 3) = -data.b 0/2
      linarith only [hc01, hc02, hc12]
  exact ⟨data.b 0,ha,hb,hc⟩

end
end AlbertRecognition.FixedFrame
