/- Native U positivity from coordinate identities, transport, and cone closure.
   No associative octonionic matrix multiplication is used. -/
module
public import Glennie.NativeSquareConeR01

@[expose] public section
namespace Glennie.NativeQuadraticPositiveR01
open Glennie Glennie.NativeSquareConeR01
noncomputable section
set_option autoImplicit false

/-- Native upper-slot convention: the 12 slot is conjugate(u) times v. -/
def rankOneColumn (r : ℝ) (u v : Octonion) : Albert :=
  ⟨r^2, octNormSq u, octNormSq v, r • u, r • v, octMul (octConj u) v⟩

theorem rankOneColumn_trace (r : ℝ) (u v : Octonion) :
    trace (rankOneColumn r u v) = r^2 + octNormSq u + octNormSq v := rfl

theorem rankOneColumn_trace_nonneg (r : ℝ) (u v : Octonion) :
    0 ≤ trace (rankOneColumn r u v) :=
  add_nonneg (add_nonneg (sq_nonneg r) (octNormSq_nonneg u)) (octNormSq_nonneg v)

/-- The only products needed are binary products and existing inverse-property laws. -/
theorem rankOneColumn_square (r : ℝ) (u v : Octonion) :
    jordan (rankOneColumn r u v) (rankOneColumn r u v) =
      trace (rankOneColumn r u v) • rankOneColumn r u v := by
  rw [rankOneColumn_trace]
  apply Albert.ext
  · simp only [jordan_d0, Albert.smul_d0, rankOneColumn,
      octDot_self, octNormSq_smul]
    ring
  · simp only [jordan_d1, Albert.smul_d1, rankOneColumn,
      octDot_self, octNormSq_smul, octNormSq_mul, octNormSq_conj]
    ring
  · simp only [jordan_d2, Albert.smul_d2, rankOneColumn,
      octDot_self, octNormSq_smul, octNormSq_mul, octNormSq_conj]
    ring
  · simp only [jordan_o01, Albert.smul_o01, rankOneColumn,
      octConj_mul, octConj_conj, octMul_smul_left, octMul_left_conj_cancel]
    module
  · simp only [jordan_o02, Albert.smul_o02, rankOneColumn,
      octMul_smul_left, octMul_left_conj_cancel]
    module
  · simp only [jordan_o12, Albert.smul_o12, rankOneColumn,
      octConj_smul, octMul_smul_left, octMul_smul_right]
    module

theorem rankOneColumn_positive (r : ℝ) (u v : Octonion) :
    Positive (rankOneColumn r u v) :=
  positive_of_quasiIdempotent _ _ (rankOneColumn_trace_nonneg r u v)
    (rankOneColumn_square r u v)

@[simp] private theorem octConj_zero_local : octConj (0 : Octonion) = 0 := by
  simp [octConj]

@[simp] private theorem octMul_zero_left_local (x : Octonion) :
    octMul 0 x = 0 := by
  simp [octMul]

@[simp] private theorem octMul_zero_right_local (x : Octonion) :
    octMul x 0 = 0 := by
  simp [octMul]

private theorem jordan_standardFrame_zero (a : Albert) :
    jordan a (standardFrame 0) =
      ⟨a.d0, 0, 0, (1 / 2 : ℝ) • a.o01, (1 / 2 : ℝ) • a.o02, 0⟩ := by
  apply Albert.ext
  all_goals simp [standardFrame, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul,
    octConj] <;> simp only [show ((0, 0) : Octonion) = 0 from rfl, add_zero]

/-- Coordinate expansion has degree two; isolate this from the cone proof. -/
theorem U_standardFrame_zero (a : Albert) :
    U a (standardFrame 0) = rankOneColumn a.d0 a.o01 a.o02 := by
  unfold U
  rw [jordan_standardFrame_zero]
  apply Albert.ext
  all_goals simp [standardFrame, rankOneColumn,
    jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
    octDot_coordinates, octDot_self, octMul_smul_left, octMul_smul_right,
    octConj_smul, octNormSq, Quaternion.normSq_def', smul_eq_mul]
  all_goals norm_num at *
  all_goals try ring
  all_goals module

theorem U_standardFrame_zero_positive (a : Albert) :
    Positive (U a (standardFrame 0)) := by
  rw [U_standardFrame_zero]
  exact rankOneColumn_positive a.d0 a.o01 a.o02

private theorem swap01_standardFrame_one :
    realSwap01Automorphism.equiv (standardFrame 1) = standardFrame 0 := by
  change realConjugateAlbert realSwap01 (standardFrame 1) = standardFrame 0
  rw [realSwap01_coordinates]
  simp [standardFrame, octConj]

private theorem swap02_standardFrame_two :
    realSwap02Automorphism.equiv (standardFrame 2) = standardFrame 0 := by
  change realConjugateAlbert realSwap02 (standardFrame 2) = standardFrame 0
  rw [realSwap02_coordinates]
  simp [standardFrame, octConj]

theorem U_standardFrame_positive (a : Albert) (i : Fin 3) :
    Positive (U a (standardFrame i)) := by
  fin_cases i
  · exact U_standardFrame_zero_positive a
  · change Positive (U a (standardFrame 1))
    apply (positive_map_iff realSwap01Automorphism _).mp
    rw [realSwap01Automorphism.map_U, swap01_standardFrame_one]
    exact U_standardFrame_zero_positive _
  · change Positive (U a (standardFrame 2))
    apply (positive_map_iff realSwap02Automorphism _).mp
    rw [realSwap02Automorphism.map_U, swap02_standardFrame_two]
    exact U_standardFrame_zero_positive _

theorem diagonal_resolution (x : Albert) (hx : IsDiagonal x) :
    x = x.d0 • standardFrame 0 + x.d1 • standardFrame 1 +
      x.d2 • standardFrame 2 := by
  apply Albert.ext
  all_goals simp [standardFrame, hx.1, hx.2.1, hx.2.2]

/-- Positivity of the quadratic representation for every native Albert amplitude. -/
theorem U_positive (a x : Albert) (hx : Positive x) : Positive (U a x) := by
  obtain ⟨g, hg⟩ := native_diagonalization x
  have hpos := positive_map g x hx
  have hn := positive_diagonal_nonneg (g.equiv x) hpos
  apply (positive_map_iff g _).mp
  rw [g.map_U, diagonal_resolution (g.equiv x) hg,
    U_add_argument, U_add_argument, U_smul_argument, U_smul_argument,
    U_smul_argument]
  exact positive_add _ _
    (positive_add _ _
      (positive_smul _ _ hn.1 (U_standardFrame_positive (g.equiv a) 0))
      (positive_smul _ _ hn.2.1 (U_standardFrame_positive (g.equiv a) 1)))
    (positive_smul _ _ hn.2.2 (U_standardFrame_positive (g.equiv a) 2))

/-- No amplitude positivity premise is needed, only the square bound for trace. -/
theorem U_positive_trace_le (a x : Albert) (hx : Positive x)
    (ha : Positive ((1 : Albert) - jordan a a)) :
    Positive (U a x) ∧ trace (U a x) ≤ trace x :=
  ⟨U_positive a x hx, trace_U_le a x hx ha⟩

end
end Glennie.NativeQuadraticPositiveR01
