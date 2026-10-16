/- Native compact diagonalization from actual automorphisms and a maximum.
No compact spectral theorem is an assumption of this proof. -/
module
public import Glennie.Compactness
public import Glennie.ScalarRotation
public import Glennie.Native.Triality
public import Glennie.Native.RealConjugation

@[expose] public section
namespace Glennie
noncomputable section

def HasMaximalDiagonalEnergy (x : Albert) : Prop :=
  ∀ g : CompactAutomorphism, diagonalEnergy (g.equiv x) ≤ diagonalEnergy x

theorem maximalDiagonalEnergy_after (x : Albert) (hx : HasMaximalDiagonalEnergy x)
    (g : CompactAutomorphism) (hg : diagonalEnergy (g.equiv x) = diagonalEnergy x) :
    HasMaximalDiagonalEnergy (g.equiv x) := by
  intro h
  rw [hg]
  exact hx (h.comp g)

theorem maximalDiagonalEnergy_slot12_zero (x : Albert) (hx : HasMaximalDiagonalEnergy x) :
    x.o12 = 0 := by
  by_contra hn
  obtain ⟨g, n, hn, h0, h1, h2, hslot⟩ := OctRelatedTriple.make_slot12_real x hn
  obtain ⟨c, s, hcs, he⟩ := exists_rotation_improving_energy x.d1 x.d2 n hn
  have hmax := hx ((realRotation12Automorphism c s hcs).comp g)
  change diagonalEnergy (realConjugateAlbert (realRotation12 c s) (g.equiv x)) ≤
    diagonalEnergy x at hmax
  unfold diagonalEnergy at hmax
  rw [realRotation12_d0, realRotation12_d1, realRotation12_d2,
    h0, h1, h2, hslot, octRe_scalar] at hmax
  nlinarith [he]

theorem realSwap01_diagonalEnergy (x : Albert) :
    diagonalEnergy (realSwap01Automorphism.equiv x) = diagonalEnergy x := by
  change diagonalEnergy (realConjugateAlbert realSwap01 x) = _
  rw [realSwap01_coordinates]
  simp only [diagonalEnergy]
  ring

theorem realSwap02_diagonalEnergy (x : Albert) :
    diagonalEnergy (realSwap02Automorphism.equiv x) = diagonalEnergy x := by
  change diagonalEnergy (realConjugateAlbert realSwap02 x) = _
  rw [realSwap02_coordinates]
  simp only [diagonalEnergy]
  ring

theorem maximalDiagonalEnergy_isDiagonal (x : Albert) (hx : HasMaximalDiagonalEnergy x) :
    IsDiagonal x := by
  have h12 := maximalDiagonalEnergy_slot12_zero x hx
  have h02 := maximalDiagonalEnergy_slot12_zero (realSwap01Automorphism.equiv x)
    (maximalDiagonalEnergy_after x hx _ (realSwap01_diagonalEnergy x))
  have h01 := maximalDiagonalEnergy_slot12_zero (realSwap02Automorphism.equiv x)
    (maximalDiagonalEnergy_after x hx _ (realSwap02_diagonalEnergy x))
  change (realConjugateAlbert realSwap01 x).o12 = 0 at h02
  change (realConjugateAlbert realSwap02 x).o12 = 0 at h01
  rw [realSwap01_coordinates] at h02
  rw [realSwap02_coordinates] at h01
  have h01' : x.o01 = 0 := by
    have h := congrArg octConj h01
    have hz : octConj (0 : Octonion) = 0 := by
      change (star (0 : Quaternion ℝ), -(0 : Quaternion ℝ)) = (0,0)
      simp only [star_zero, neg_zero]
    simpa only [octConj_conj, hz] using h
  exact ⟨h01', h02, h12⟩

/-- Diagonalization in the genuine native product/trace automorphism group. -/
theorem native_diagonalization (x : Albert) :
    ∃ g : CompactAutomorphism, IsDiagonal (g.equiv x) := by
  obtain ⟨g, hg⟩ := exists_diagonalEnergy_maximum x
  refine ⟨g, maximalDiagonalEnergy_isDiagonal _ ?_⟩
  intro h
  exact hg (h.comp g)

def standardFrame : Fin 3 → Albert :=
  ![⟨1,0,0,0,0,0⟩,⟨0,1,0,0,0,0⟩,⟨0,0,1,0,0,0⟩]

theorem standardFrame_isFrame : Frame standardFrame where
  trace_one i := by fin_cases i <;> norm_num [standardFrame, trace]
  idempotent i := by
    fin_cases i <;> apply Albert.ext <;>
      norm_num [standardFrame, jordan_d0, jordan_d1, jordan_d2, jordan_o01,
        jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj,
        octNormSq, Quaternion.normSq_def']
  orthogonal i j hij := by
    fin_cases i <;> fin_cases j <;> try contradiction
    all_goals apply Albert.ext <;>
      norm_num [standardFrame, jordan_d0, jordan_d1, jordan_d2, jordan_o01,
        jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj,
        octNormSq, Quaternion.normSq_def']
  sum_unit := by apply Albert.ext <;> norm_num [standardFrame, unit]

/-- The native compact spectral/frame statement, with all exceptional algebra
premises supplied by the explicit coordinate and automorphism construction. -/
theorem compact_spectral_decomposition : CompactSpectralDecomposition := by
  intro x
  obtain ⟨g, hg⟩ := native_diagonalization x
  let a : Fin 3 → ℝ := ![(g.equiv x).d0,(g.equiv x).d1,(g.equiv x).d2]
  have hrec : g.equiv x = ∑ i, a i • standardFrame i := by
    apply Albert.ext
    all_goals simp [a, standardFrame, Fin.sum_univ_three, hg.1, hg.2.1, hg.2.2]
  refine ⟨(fun i => g.symm.equiv (standardFrame i)), a,
    g.symm.map_frame standardFrame standardFrame_isFrame, ?_⟩
  apply g.equiv.injective
  simpa only [map_sum, map_smul, CompactAutomorphism.symm_apply,
    LinearEquiv.apply_symm_apply] using hrec

end
end Glennie
