/- The positive native trace form as a real Hilbert space.
Diagonalizing a multiplication operator is not yet a Jordan-frame theorem. -/
module
public import Glennie.Native.CubicIdentity
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section
namespace Glennie
noncomputable section

def Albert.coordinateLinearEquiv : Albert ≃ₗ[ℝ] Albert.Coordinates where
  __ := Albert.coordinateAddEquiv
  map_smul' _ _ := rfl

instance : FiniteDimensional ℝ Albert := by
  letI : FiniteDimensional ℝ Albert.Coordinates := Module.Finite.prod
  exact Albert.coordinateLinearEquiv.symm.finiteDimensional

theorem albert_finrank : Module.finrank ℝ Albert = 27 := by
  rw [Albert.coordinateLinearEquiv.finrank_eq]
  simp [Albert.Coordinates, Octonion, Quaternion.finrank_eq_four]

instance : Inner ℝ Albert := ⟨Glennie.inner⟩

@[instance_reducible] def nativeInnerCore : InnerProductSpace.Core ℝ Albert where
  toInner := inferInstance
  conj_inner_symm x y := by
    change inner y x = inner x y
    exact inner_comm y x
  re_inner_nonneg := inner_self_nonneg
  definite x := (inner_self_eq_zero x).mp
  add_left := inner_add_left
  smul_left x y r := by
    change inner (r • x) y = r * inner x y
    exact inner_smul_left r x y

instance : NormedAddCommGroup Albert := nativeInnerCore.toNormedAddCommGroup

instance : InnerProductSpace ℝ Albert :=
  InnerProductSpace.ofCore nativeInnerCore.toCore

theorem hilbert_inner_eq_native (x y : Albert) :
    Inner.inner ℝ x y = Glennie.inner x y := rfl

theorem native_norm_sq (x : Albert) : ‖x‖ ^ 2 = inner x x := by
  exact real_inner_self_eq_norm_sq x |>.symm

theorem multiplication_isSymmetric (x : Albert) :
    (jordanLinear x).IsSymmetric := by
  intro y z
  change inner (jordan x y) z = inner y (jordan x z)
  rw [jordan_comm x y]
  exact inner_jordan_associative y x z

/-- Genuine orthonormal diagonalization of native multiplication by x.
This alone is not spectral decomposition of x into trace-one Jordan idempotents. -/
theorem multiplication_operator_eigenbasis (x : Albert) :
    ∃ (b : OrthonormalBasis (Fin 27) ℝ Albert) (eigenvalue : Fin 27 → ℝ),
      ∀ i, jordan x (b i) = eigenvalue i • b i := by
  let h := multiplication_isSymmetric x
  exact ⟨h.eigenvectorBasis albert_finrank, h.eigenvalues albert_finrank,
    h.apply_eigenvectorBasis albert_finrank⟩

theorem gram_posSemidef (x y z : Albert) : (gram x y z).PosSemidef :=
  Matrix.posSemidef_gram ℝ (fun i => traceless (triple x y z i))

theorem gram_det_nonneg (x y z : Albert) : 0 ≤ (gram x y z).det :=
  (gram_posSemidef x y z).det_nonneg

theorem gram_det_ne_zero_iff (x y z : Albert) :
    (gram x y z).det ≠ 0 ↔
      LinearIndependent ℝ (fun i => traceless (triple x y z i)) :=
  Matrix.det_gram_ne_zero_iff_linearIndependent (𝕜 := ℝ)
    (v := fun i => traceless (triple x y z i))

end
end Glennie
