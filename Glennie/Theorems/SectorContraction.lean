/- Small trace/adjugate
contractions against the full compact native SectorModel. No factor,
covariance, reduction, specialness or endpoint is assumed as a field. -/
module
public import Glennie.SectorModel

@[expose] public section
namespace Glennie.SectorContraction
noncomputable section

abbrev M3 := Matrix (Fin 3) (Fin 3) ℂ

/-- Newton's polarized matrix adjugate expression. Its equality with the actual
polar adjugate, where needed by native U, is a separate producer obligation. -/
def tracePolar (G B : M3) : M3 :=
  G*B+B*G-B.trace • G-G.trace • B+
    (B.trace*G.trace-(G*B).trace) • (1 : M3)

/-- Polynomial adjugate contraction, including every singular hidden matrix. -/
theorem hidden_adjugate_gram (M : M3) :
    M.conjTranspose * sectorAdjointAdjugate M = star M.det • (1 : M3) := by
  calc
    _ = (M.adjugate*M).conjTranspose := by
      simp only [sectorAdjointAdjugate,Matrix.conjTranspose_mul]
    _ = (M.det • (1 : M3)).conjTranspose := by rw [Matrix.adjugate_mul]
    _ = _ := by simp only [Matrix.conjTranspose_smul,Matrix.conjTranspose_one]

/-- Contract before expanding any hidden coordinates. This turns the cubic
hidden product into a determinant times one small complex trace. -/
theorem hidden_adjugate_trace (M S B : M3) :
    ((M*S).conjTranspose*(sectorAdjointAdjugate M*B)).trace =
      star M.det*(S.conjTranspose*B).trace := by
  calc
    _ = ((S.conjTranspose*(M.conjTranspose*sectorAdjointAdjugate M))*B).trace := by
      simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = ((S.conjTranspose*(star M.det • (1 : M3)))*B).trace := by
      rw [hidden_adjugate_gram]
    _ = _ := by
      simp only [Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul,
        Matrix.trace_smul,smul_eq_mul]

/-- For the actual anti-Hermitian adjugate commutator, retain the crucial minus
sign. No invertibility of M or nonzero determinant is used. -/
theorem hidden_cubic_real (M S B : M3) (hS : S.conjTranspose = -S) :
    2*((M*S).conjTranspose*(sectorAdjointAdjugate M*B)).trace.re =
      -2*(star M.det*(S*B).trace).re := by
  rw [hidden_adjugate_trace,hS,Matrix.neg_mul,Matrix.trace_neg]
  simp only [mul_neg,Complex.neg_re]
  ring

/-- The purely complex scalar part cancels by two cyclic rotations. -/
theorem trace_comm_mul_sum (X Y : M3) :
    ((X*Y-Y*X)*(X+Y)).trace = 0 := by
  have h1 : (X*Y*X).trace = (Y*X*X).trace := by
    rw [Matrix.mul_assoc,Matrix.trace_mul_comm X (Y*X)]
  have h2 : (X*Y*Y).trace = (Y*X*Y).trace := Matrix.trace_mul_cycle X Y Y
  simp only [Matrix.sub_mul,Matrix.mul_add,Matrix.trace_sub,Matrix.trace_add,h1,h2]
  ring

/-- Polarized adjugate trace self-adjointness, valid even for arbitrary matrices.
The proof normalizes only scalar traces; it expands no native coordinates. -/
theorem trace_polar_transfer (C G B : M3) :
    (C*tracePolar G B).trace = (G*tracePolar C B).trace := by
  have h1 : (C*(G*B)).trace = (G*(B*C)).trace := by
    rw [Matrix.trace_mul_cycle' C G B,Matrix.trace_mul_cycle' B C G]
  have h2 : (C*(B*G)).trace = (G*(C*B)).trace :=
    Matrix.trace_mul_cycle' C B G
  have h3 : (C*G).trace = (G*C).trace := Matrix.trace_mul_comm C G
  simp only [tracePolar,Matrix.mul_add,Matrix.mul_sub,Matrix.mul_smul,
    Matrix.mul_one,Matrix.trace_add,Matrix.trace_sub,Matrix.trace_smul,
    smul_eq_mul,Matrix.mul_assoc]
  rw [h1,h2,h3]
  ring

end
end Glennie.SectorContraction
