module

public import Glennie.Compact.NearbyOrbits
public import Glennie.Native.FirstPairNormalization
public import Glennie.UnitShifts

/- Nearby pair normalization. `native_ordered_positive_pair` carries an arbitrary genuine frame onto the
diagonal frame `flatFrameP` and the second frame's encoder into the complex sector with slots 01
and 12 nonnegative real; it has no `1/3` and no `flatScale` in it, so it survives perturbation
untouched. The nine pairwise overlaps -- the P block -- then determine the three
diagonal entries AND the three square-diagonal entries of that encoder by subtraction and
addition (section 4), hence by `fe_complex_square_d0/d1/d2` the three complex slot norms, hence
by `fe_complex_cubic` with `frame_encoder_cubicNorm` the real part of the triangle, hence the
whole normalised second frame up to the sign of one imaginary part, which one constructed
octonion automorphism flips (sections 6, 7). The residual group is the colour SU(3) of
`sectorLeftSU3Automorphism`, which fixes the whole complex sector; the third frame's encoder
splits as `complexProjection` plus `hiddenAlbert (hiddenMatrix _)`, the ledger determines the
sector projection of that encoder and of its square (section 8), those determine the hidden Gram
matrix and -- through Newton's cubic norm and `inner_jordan_associative` -- the real part of the
hidden determinant (section 9), and `phi_of_diagonal_complex` says Phi is a nonzero multiple of
its imaginary part (section 11), so one shrink by the sign of Phi pins that too and the matrix
transport closes (sections 10, 12).

Providers and conventions.

  `Glennie.Native`: `inner_coordinates` :345, `inner_comm` :351, `jordan_comm` :296,
    `jordan_d0` :300, `jordan_d1` :306, `jordan_d2` :312, `jordan_o01` :318, `jordan_o02` :327,
    `jordan_o12` :336, `octMul` :32, `octConj` :35, `octRe` :36, `octScalar` :37, `octDot` :38,
    `octNormSq` :39, `octDot_coordinates` :67, `octDot_comm` :74, the `@[simp]` field
    projections of `+`/`-`/`•`/`0`/`1` :162-195, `phi` :221, `trace` :215, `inner` :216,
    `encoder` :235, `ledger` :236, `Frame` :228
  `Glennie.Native.AlgebraLaws`: `octDot_add_left` :79, `octDot_smul_left` :84,
    `jordan_add_left` :89, `jordan_add_right` :100, `jordan_smul_left` :103,
    `jordan_sub_left` :125, `jordan_sub_right` :128, `jordan_unit_left` :131,
    `jordan_unit_right` :138, `inner_add_left` :147, `inner_add_right` :150,
    `inner_smul_left` :153, `inner_smul_right` :156, `inner_sub_left` :165,
    `inner_sub_right` :168, `inner_jordan_associative` :172
  `Glennie.Native.Triality`: `octDot_sub_left` :23, `OctRelatedTriple` :133
  `Glennie.Sector`: `complexPart` :13, `complexOct` :15, `hiddenMatrix` :24, `hiddenAlbert` :27,
    `complexProjection` :31, `diagonalAlbert` :34, `complexAlbert` :36,
    `complex_hidden_decomposition` :45, `complex_hidden_orthogonal` :52, `hiddenAlbert_norm` :57,
    `sectorColumnGram` :65, `sectorFrobeniusSq` :68, `hidden_square_complexProjection` :72
  `Glennie.SectorModel`: `hiddenMatrix_hiddenAlbert` :60
  `Glennie.SectorSubspace`: `complexProjection_mem` :50, `complexProjection_eq_self` :53,
    `complexSector_mem_iff` :59, `complexSector_jordan` :67, `complexProjection_zero_of_perp` :84
  `Glennie.Obligations`: `IsDiagonal` :16, `OctInComplex` :19, `InComplexSector` :21
  `Glennie.Theorems.CubicNorm`: `newtonCubicNorm` (Newton's TRACE form) :15,
    `frame_encoder_cubicNorm` :31
  `Glennie.Theorems.Frames`: `frame_encoder_trace` :13, `frame_encoder_square` :18,
    `frame_encoder_norm` :30, `frame_projector_first` :36 with `_middle` and `_last`,
    `uniformLedger_pair_overlap` :65
  `Glennie.Theorems.ProjectorFrame`: `projectorFrame` :16
  `Glennie.Theorems.FrameSaturation`: `fe_complex_cubic` :17,
    `fe_complex_square_d0/d1/d2` :27,33,39
  `Glennie.Theorems.DiagonalFrames`: `frame_projectors_diagonal` :26
  `Glennie.Theorems.ComplexSectorSpan`: `complexProjection_sub` :20, `complexProjection_add` :24,
    `complexProjection_smul` :28, `complexProjection_unit` :32, `frame_in_complexSector` :36
  `Glennie.Theorems.OctonionAutomorphisms`: `DiagonalOctTriple` :68,
    `exists_octAutomorphism_to_i` :209
  `Glennie.Native.PairReduction`: `octInComplex_scalar` :18, `diagonalOctTriple_scalar` :25
  `Glennie.Theorems.SectorTransport`: `SectorMatrix` :16, `SectorUnitary` :17,
    `hiddenMatrix_of_inComplex` :290
  `Glennie.SectorFactor`: `phi_diagonal_complex_factor` :21, consumed through `UnitShifts`.
  `Glennie.UnitShifts`: `diagonalAlbert_eq` :18, `complexAlbert_eq` :22,
    `phi_of_diagonal_complex` :27, `diagonal_inComplex` :47.
  `Glennie.Automorphism`: `CompactAutomorphism.refl` :11, `.comp` :17, `comp_apply` :22,
    `.symm` :25, `symm_apply` :32, `map_unit` :35, `inner_map` :40, `phi_map` :49,
    `map_frame` :63, `encoder_map` :70, `ledger_map` :74
  `Glennie.Compactness`: `CompactAutomorphism` (NO `Group`/`Monoid`/`Mul`/`One`/`Inv`/
    `MulAction` instance and NO topology -- hence no continuity in the group variable is used
    anywhere below, and all composition is through `.comp`/`.symm` by hand)
  `Glennie.Compact.FlatBase`: `flatScale` :53, `flatXN` :61, `flatY1` :64, `reverseFrame` :183,
    `projectorFrame_neg_one_smul` :190, `flatFrameP` :207, `flatFrameQ` :208, `flatFrameR` :209,
    `flatFrameP_frame` :231, `flatFrameQ_frame` :236, `flatFrameP_encoder` :250,
    `flat_uniform` :272
  `Glennie.Compact.Affine20.Relabel`: `Triple` :47, `Ledger54` :51, `ledger54` :56,
    `mapAtoms` :142, `mapAtoms_apply` :145, `ledger54_C/P/Q/R` :157,160,164,167,
    `ledger54_map` :169, `fin3_cases` :61
  `Glennie.Compact.Sections.Reversal`: `phiOf` :267, `phiOf_apply` :269, `continuous_phiOf` :372

  `Glennie.NativeOrderedPositivePair.native_ordered_positive_pair` normalizes the first pair.
  `Glennie.sectorLeftSU3Automorphism`, `sectorLeftSU3_complex`, `sectorLeftSU3_hidden`,
    `sectorLeftSU3_fixes_complex`, and `compactAutomorphism_projectorFrame` supply the colour action.
  `NativeFixedPairHidden.native_fixed_pair_hidden_gram_phase` and
    `NativeFixedPairNormalization.native_fixed_pair_third_frame_normalization` concern the exact
    uniform ledger; the nearby argument uses general forms of their ingredients.
    `scaled_transport` is re-proved in general form in section 10.
  `Glennie.Compact.FrameTopology` supplies `flatBaseTriple`, `flatBaseTriple_frames`,
    `continuous_entry`, and `continuous_ledger54`.
  `Glennie.Compact.FlatOrbit` supplies `flatBaseRev3` and `flatBaseRev3_frames`.
  `Glennie.Compact.NearbyOrbits` supplies `LocalOrbitCompleteness`, `phiOf_mapAtoms`,
    `phiOf_flatBaseTriple_neg`, and `phiOf_flatBaseRev3_pos`.
  `Glennie.Native.FirstPairNormalization.native_flat_pair_normalization` is not invoked:
    section 7 generalizes its argument by removing the exact values. Its private helpers
    `frame_as_projector`, `frame_eq_of_encoder_eq`, `nonneg_sq_flatScale`,
    `complex_slot_data_of_square`, `uniform_complex_slot_data`, `flatQ_slots`,
    `encoder_to_flatQ`, `relatedTriple_flatXN`, `relatedTriple_fixes_flatFrameP`, and
    `real_real_conj_re` are re-derived or replaced here.

Neighbourhoods are shrunk by an explicit epsilon box on the P block, open by
`continuous_ledger54`, and one half-space of `phiOf`, open by `continuous_phiOf`.
The two sign sheets remain separate. The action is the diagonal `mapAtoms`;
no topology on `CompactAutomorphism`, continuity in a group variable, or derivative
of the existential sections of `native_flat_two_sections_full54` is used.

ON `octConj`. It is never APPLIED by this file, never composed with an automorphism and never
used to correct a sign -- the sign correction is the genuine automorphism of
`exists_octAutomorphism_to_i`. It occurs as a simp-lemma NAME in four places (the three
`fe_complex_square_o*` of section 5 and `octMul_zero_*`/`octConj_zero` of section 1a), because
the right-hand sides of the package's own `jordan_o01/o02/o12` literally contain
`octMul _ (octConj _)`. That is the same usage as in the `fe_complex_square_d0/d1/d2`
and `fe_complex_cubic`, whose simp sets also list `octConj`.
-/

@[expose] public section
namespace Glennie.Compact.PairNormNearby

open Glennie Glennie.Compact.FlatBase Glennie.Compact.Affine20
open Glennie.Compact.FrameTopology Glennie.Compact.FlatOrbit
open Glennie.Compact.Sections Glennie.Compact.NearbyOrbits
open Glennie.NativeOrderedPositivePair

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## 1. Pure arithmetic on reals and matrices

The arithmetic for `slot_nondegenerate` and `sector_slot_recovery` is isolated from
contexts carrying `Albert`, `Octonion` and `Complex.normSq (complexPart _)` atoms.
The lemmas use `linarith`, `linear_combination`, `calc` or a single `nlinarith` over
at most four hypotheses, and are called with explicit arguments. -/

theorem nonneg_sq_eq_of_sq_eq (a a' : ℝ) (ha : 0 ≤ a) (ha' : 0 ≤ a')
    (h : a ^ 2 = a' ^ 2) : a = a' := by
  have hprod : (a - a') * (a + a') = 0 := by linear_combination h
  rcases mul_eq_zero.mp hprod with h1 | h2
  · linarith
  · linarith

theorem half_lt_of_sq (a : ℝ) (ha : 0 ≤ a) (h : 1 / 4 < a ^ 2) : 1 / 2 < a := by
  nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (a + 1 / 2)]

theorem ne_zero_of_sq_eq_of_ne_zero (x x' : ℝ) (h : x ^ 2 = x' ^ 2) (hx : x ≠ 0) : x' ≠ 0 := by
  intro hz
  have hxx : x * x = 0 := by
    have hx2 : x ^ 2 = 0 := by rw [h, hz]; ring
    nlinarith [hx2]
  rcases mul_eq_zero.mp hxx with h1 | h1
  · exact hx h1
  · exact hx h1

/-- The one genuinely nonlinear step, isolated so that `nlinarith` sees four hypotheses and no
`Albert`. Everything else in this section is linear or `calc`. -/
theorem mul_lt_mul_nonneg (x bx y by' : ℝ)
    (hx0 : 0 ≤ x) (hx : x < bx) (hy0 : 0 ≤ y) (hy : y < by') : x * y < bx * by' := by
  nlinarith

theorem abs_prod_lt (x y bx by' : ℝ) (hx : |x| < bx) (hy : |y| < by') :
    |x * y| < bx * by' := by
  rw [abs_mul]
  exact mul_lt_mul_nonneg |x| bx |y| by' (abs_nonneg x) hx (abs_nonneg y) hy

theorem abs_prod_nonneg_lt (x y bx by' : ℝ) (hx : |x| < bx) (hy0 : 0 ≤ y) (hy : y < by') :
    |x * y| < bx * by' := by
  rw [abs_mul, abs_of_nonneg hy0]
  exact mul_lt_mul_nonneg |x| bx y by' (abs_nonneg x) hx hy0 hy

/-- Equal squares survive a common factor. -/
theorem mul_sq_eq_of_sq_eq (K X Y : ℝ) (h : X ^ 2 = Y ^ 2) :
    (K * X) ^ 2 = (K * Y) ^ 2 := by
  calc (K * X) ^ 2 = K ^ 2 * X ^ 2 := by ring
    _ = K ^ 2 * Y ^ 2 := by rw [h]
    _ = (K * Y) ^ 2 := by ring

/-- Equal norms and equal real parts give equal squared imaginary parts. Squaring the
real-part equality is not a linear step. -/
theorem im_sq_eq_of_normSq_eq (z w : ℂ) (hn : Complex.normSq z = Complex.normSq w)
    (hr : z.re = w.re) : z.im ^ 2 = w.im ^ 2 := by
  rw [Complex.normSq_apply, Complex.normSq_apply] at hn
  have hrr : z.re * z.re = w.re * w.re := by rw [hr]
  have h : z.im * z.im = w.im * w.im := by linarith
  calc z.im ^ 2 = z.im * z.im := by ring
    _ = w.im * w.im := h
    _ = w.im ^ 2 := by ring

/-- A homogeneous 2x2 real system with nonzero determinant has only the zero solution.
`linear_combination` eliminates each unknown exactly. -/
theorem two_by_two (A B C D X Y : ℝ)
    (h1 : A * X + B * Y = 0) (h2 : C * X + D * Y = 0)
    (hdet : A * D - B * C ≠ 0) : X = 0 ∧ Y = 0 := by
  have hX : (A * D - B * C) * X = 0 := by linear_combination D * h1 - B * h2
  have hY : (A * D - B * C) * Y = 0 := by linear_combination A * h2 - C * h1
  refine ⟨?_, ?_⟩
  · rcases mul_eq_zero.mp hX with h | h
    · exact absurd h hdet
    · exact h
  · rcases mul_eq_zero.mp hY with h | h
    · exact absurd h hdet
    · exact h

/-- `MatrixDetEstimate.determinant_gram_real` (`:21`) with `columnGram` unfolded.
`columnGram` lives in the sub-namespace `Glennie.MatrixDetEstimate`. -/
theorem normSq_det_eq_gram_det_re (M : Matrix (Fin 3) (Fin 3) ℂ) :
    Complex.normSq M.det = (M.conjTranspose * M).det.re := by
  rw [Matrix.det_mul, Matrix.det_conjTranspose]
  simp [Complex.mul_re, Complex.normSq_apply]

/-- **The whole real content of the epsilon box, as one real-only statement.** `D0 D1 D2` are the three
diagonal entries of the normalised second encoder, `e0 e1 e2` the three diagonal entries of its
square, `a b` the two nonnegative real slots, `v` the energy of slot 02 and `R Sg` its real and
imaginary parts. `E0 E1 E2` are `fe_complex_square_d0/d1/d2` and `C` is `fe_complex_cubic` with
`frame_encoder_cubicNorm`; all four are supplied by the caller.

Every step is `linarith` on the atoms `{D0^2, D1^2, D2^2, a^2, b^2, v, e0, e1, e2}` or a `calc`.
The margins are deliberately loose: `a^2 > 0.27` where `1/4` suffices, `|R| < 1/4` where `1/2`
suffices. If a `linarith` here is slow, LOOSEN the box (`1/50` to `1/100`) rather than sharpen
anything -- nothing downstream uses more than `0 < a`, `0 < b`, `Sg /= 0`. -/
theorem nondegenerate_core (a b D0 D1 D2 e0 e1 e2 v R Sg : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hD0 : |D0| < 1 / 25) (hD1 : |D1| < 1 / 25) (hD2 : |D2| < 1 / 25)
    (he0 : |e0 - 2 / 3| < 1 / 25) (he1 : |e1 - 2 / 3| < 1 / 25) (he2 : |e2 - 2 / 3| < 1 / 25)
    (hv0 : 0 ≤ v)
    (E0 : e0 = D0 ^ 2 + a ^ 2 + v)
    (E1 : e1 = D1 ^ 2 + a ^ 2 + b ^ 2)
    (E2 : e2 = D2 ^ 2 + v + b ^ 2)
    (C : 0 = D0 * D1 * D2 - D0 * b ^ 2 - D1 * v - D2 * a ^ 2 + 2 * (a * b * R))
    (hsplit : v = R ^ 2 + Sg ^ 2) :
    1 / 2 < a ∧ 1 / 2 < b ∧ Sg ≠ 0 := by
  obtain ⟨l0, r0⟩ := abs_lt.mp hD0
  obtain ⟨l1, r1⟩ := abs_lt.mp hD1
  obtain ⟨l2, r2⟩ := abs_lt.mp hD2
  obtain ⟨m0, n0⟩ := abs_lt.mp he0
  obtain ⟨m1, n1⟩ := abs_lt.mp he1
  obtain ⟨m2, n2⟩ := abs_lt.mp he2
  have q0 : D0 ^ 2 < (1 / 25 : ℝ) ^ 2 := sq_lt_sq' l0 r0
  have q1 : D1 ^ 2 < (1 / 25 : ℝ) ^ 2 := sq_lt_sq' l1 r1
  have q2 : D2 ^ 2 < (1 / 25 : ℝ) ^ 2 := sq_lt_sq' l2 r2
  have p0 : (0 : ℝ) ≤ D0 ^ 2 := sq_nonneg D0
  have p1 : (0 : ℝ) ≤ D1 ^ 2 := sq_nonneg D1
  have p2 : (0 : ℝ) ≤ D2 ^ 2 := sq_nonneg D2
  -- 2*a^2 = (e0 - D0^2) + (e1 - D1^2) - (e2 - D2^2), and cyclically; all linear
  have hasq : (1 : ℝ) / 4 < a ^ 2 := by linarith
  have hasq' : a ^ 2 < (1 : ℝ) / 2 := by linarith
  have hbsq : (1 : ℝ) / 4 < b ^ 2 := by linarith
  have hbsq' : b ^ 2 < (1 : ℝ) / 2 := by linarith
  have hvlb : (1 : ℝ) / 4 < v := by linarith
  have hvub : v < (1 : ℝ) / 2 := by linarith
  have halt : 1 / 2 < a := half_lt_of_sq a ha hasq
  have hblt : 1 / 2 < b := half_lt_of_sq b hb hbsq
  refine ⟨halt, hblt, ?_⟩
  have hab : (1 : ℝ) / 4 < a * b := by
    have h := mul_lt_mul_nonneg (1 / 2) a (1 / 2) b (by norm_num) halt (by norm_num) hblt
    linarith [h]
  -- every product term in the cubic is small
  have t1 : |D0 * b ^ 2| < (1 / 25 : ℝ) * (1 / 2) :=
    abs_prod_nonneg_lt D0 (b ^ 2) (1 / 25) (1 / 2) hD0 (sq_nonneg b) hbsq'
  have t2 : |D1 * v| < (1 / 25 : ℝ) * (1 / 2) :=
    abs_prod_nonneg_lt D1 v (1 / 25) (1 / 2) hD1 hv0 hvub
  have t3 : |D2 * a ^ 2| < (1 / 25 : ℝ) * (1 / 2) :=
    abs_prod_nonneg_lt D2 (a ^ 2) (1 / 25) (1 / 2) hD2 (sq_nonneg a) hasq'
  have t4 : |D0 * D1 * D2| < ((1 / 25 : ℝ) * (1 / 25)) * (1 / 25) :=
    abs_prod_lt (D0 * D1) D2 ((1 / 25) * (1 / 25)) (1 / 25)
      (abs_prod_lt D0 D1 (1 / 25) (1 / 25) hD0 hD1) hD2
  obtain ⟨u1, u2⟩ := abs_lt.mp t1
  obtain ⟨w1, w2⟩ := abs_lt.mp t2
  obtain ⟨x1, x2⟩ := abs_lt.mp t3
  obtain ⟨z1, z2⟩ := abs_lt.mp t4
  have hABR : |a * b * R| < (1 : ℝ) / 16 := by
    rw [abs_lt]
    exact ⟨by linarith, by linarith⟩
  have hABsq : (1 : ℝ) / 16 < (a * b) ^ 2 := by
    have h := mul_lt_mul_nonneg (1 / 4) (a * b) (1 / 4) (a * b)
      (by norm_num) hab (by norm_num) hab
    calc (1 : ℝ) / 16 = (1 / 4) * (1 / 4) := by norm_num
      _ < (a * b) * (a * b) := h
      _ = (a * b) ^ 2 := by ring
  obtain ⟨v1, v2⟩ := abs_lt.mp hABR
  have hb2 : (a * b * R) ^ 2 < ((1 : ℝ) / 16) ^ 2 := sq_lt_sq' v1 v2
  have hkey : R ^ 2 * (1 / 16) ≤ (a * b * R) ^ 2 := by
    calc R ^ 2 * (1 / 16) ≤ R ^ 2 * (a * b) ^ 2 :=
          mul_le_mul_of_nonneg_left hABsq.le (sq_nonneg R)
      _ = (a * b * R) ^ 2 := by ring
  have hR2 : R ^ 2 < (1 : ℝ) / 16 := by linarith
  have hSg : (0 : ℝ) < Sg ^ 2 := by linarith
  intro h
  rw [h] at hSg
  norm_num at hSg

/-! ## 1a. Four octonion facts about zero

These lemmas simplify `octMul 0 (octConj 0)` and related zero terms in
`jordan_flatXN` and `inner_diag_jordan_slots`. They follow from the definitions
(`Native.lean`). -/

theorem octConj_zero : octConj (0 : Octonion) = 0 := by
  apply Prod.ext <;> simp [octConj]

theorem octMul_zero_left (y : Octonion) : octMul 0 y = 0 := by
  apply Prod.ext <;> simp [octMul]

theorem octMul_zero_right (x : Octonion) : octMul x 0 = 0 := by
  apply Prod.ext <;> simp [octMul]

theorem octNormSq_zero : octNormSq (0 : Octonion) = 0 := by
  norm_num [octNormSq, Quaternion.normSq_def']

/-! ## 2. Two re-derivations of `private` lemmas

`frame_as_projector` and `frame_eq_of_encoder_eq` are `private` in `FirstPairNormalization`
(`:32`, `:41`) and again in `FixedPairNormalization` (`:51`). They contain no values, survive
perturbation untouched. -/

theorem frame_as_projector (p : Fin 3 → Albert) (hp : Frame p) :
    p = projectorFrame (encoder p) := by
  funext i
  fin_cases i
  · exact (frame_projector_first p hp).symm
  · exact (frame_projector_middle p hp).symm
  · exact (frame_projector_last p hp).symm

theorem frame_eq_of_encoder_eq (q s : Fin 3 → Albert) (hq : Frame q) (hs : Frame s)
    (m : CompactAutomorphism) (hEnc : m.equiv (encoder q) = encoder s) (i : Fin 3) :
    m.equiv (q i) = s i := by
  calc
    m.equiv (q i) = m.equiv (projectorFrame (encoder q) i) :=
        congrArg (fun x : Albert => m.equiv x) (congrFun (frame_as_projector q hq) i)
    _ = projectorFrame (m.equiv (encoder q)) i :=
        compactAutomorphism_projectorFrame m (encoder q) i
    _ = projectorFrame (encoder s) i := by rw [hEnc]
    _ = s i := congrFun (frame_as_projector s hs).symm i

/-! ## 3. The exact diagonal probes of the normalised first frame

This replaces `diagonal_frame_uniform_coordinates` (`Theorems/DiagonalFrames.lean`), the ONE
line of `uniform_complex_slot_data` that breaks: it needs `inner (p i) (q j) = 1/3` exactly, to
conclude `(q j).d_m = 1/3`. Because `native_ordered_positive_pair` lands the first frame on
`flatFrameP` EXACTLY, overlaps with `flatFrameP` ARE the diagonal entries, with no hypothesis at
all. Its underlying `diagonal_test_inner` is `private` there, so it is re-derived.

Note the index reversal, the easiest thing in the file to get wrong:
`flatXN = diag(1,0,-1)` and `projectorFrame`'s first slot is the `(-1)`-eigenprojector, so
`flatFrameP 0` probes `d2` and `flatFrameP 2` probes `d0`. -/

theorem jordan_flatXN : jordan flatXN flatXN = diagonalAlbert 1 0 1 := by
  apply Albert.ext
  · show (jordan flatXN flatXN).d0 = (1 : ℝ)
    rw [jordan_d0]
    simp [flatXN, octNormSq_zero]
  · show (jordan flatXN flatXN).d1 = (0 : ℝ)
    rw [jordan_d1]
    simp [flatXN, octNormSq_zero]
  · show (jordan flatXN flatXN).d2 = (1 : ℝ)
    rw [jordan_d2]
    simp [flatXN, octNormSq_zero]
  · show (jordan flatXN flatXN).o01 = 0
    rw [jordan_o01]
    simp [flatXN, octConj_zero, octMul_zero_left, octMul_zero_right]
  · show (jordan flatXN flatXN).o02 = 0
    rw [jordan_o02]
    simp [flatXN, octConj_zero, octMul_zero_left, octMul_zero_right]
  · show (jordan flatXN flatXN).o12 = 0
    rw [jordan_o12]
    simp [flatXN, octConj_zero, octMul_zero_left, octMul_zero_right]

theorem inner_diagonalAlbert (a b c : ℝ) (x : Albert) :
    inner (diagonalAlbert a b c) x = a * x.d0 + b * x.d1 + c * x.d2 := by
  simp [inner_coordinates, diagonalAlbert, octDot_coordinates]

theorem flatFrameP_zero_eq : flatFrameP 0 = diagonalAlbert 0 0 1 := by
  show (1 / 2 : ℝ) • (jordan flatXN flatXN - flatXN) = diagonalAlbert 0 0 1
  rw [jordan_flatXN]
  apply Albert.ext <;> simp [diagonalAlbert, flatXN] <;> norm_num

theorem flatFrameP_one_eq : flatFrameP 1 = diagonalAlbert 0 1 0 := by
  show (1 : Albert) - jordan flatXN flatXN = diagonalAlbert 0 1 0
  rw [jordan_flatXN]
  apply Albert.ext <;> simp [diagonalAlbert] <;> norm_num

theorem flatFrameP_two_eq : flatFrameP 2 = diagonalAlbert 1 0 0 := by
  show (1 / 2 : ℝ) • (jordan flatXN flatXN + flatXN) = diagonalAlbert 1 0 0
  rw [jordan_flatXN]
  apply Albert.ext <;> simp [diagonalAlbert, flatXN] <;> norm_num

theorem inner_flatFrameP_zero (x : Albert) : inner (flatFrameP 0) x = x.d2 := by
  rw [flatFrameP_zero_eq, inner_diagonalAlbert]; ring

theorem inner_flatFrameP_one (x : Albert) : inner (flatFrameP 1) x = x.d1 := by
  rw [flatFrameP_one_eq, inner_diagonalAlbert]; ring

theorem inner_flatFrameP_two (x : Albert) : inner (flatFrameP 2) x = x.d0 := by
  rw [flatFrameP_two_eq, inner_diagonalAlbert]; ring

theorem flatFrameP_isDiagonal (i : Fin 3) : IsDiagonal (flatFrameP i) :=
  frame_projectors_diagonal flatFrameP flatFrameP_frame
    (by rw [flatFrameP_encoder]; simp [IsDiagonal, flatXN]) i

theorem flatFrameP_inComplexSector (i : Fin 3) : InComplexSector (flatFrameP i) :=
  diagonal_inComplex _ (flatFrameP_isDiagonal i)

/-! ## 4. The P block determines six numbers, by subtraction and addition

These six replace the three exact values `1/3` of `uniform_complex_slot_data`. Nothing here
needs the overlaps to be uniform or even near uniform; `hPQ` is naming, not a hypothesis on the
values. There are exactly four independent numbers,
matching the four free parameters of a 3x3 matrix whose rows and columns all sum to one. -/

theorem normalised_diag_data (q : Fin 3 → Albert) (hq : Frame q) (P : Fin 3 → Fin 3 → ℝ)
    (hPQ : ∀ i j : Fin 3, inner (flatFrameP i) (q j) = P i j) :
    (encoder q).d0 = P 2 2 - P 2 0 ∧ (encoder q).d1 = P 1 2 - P 1 0 ∧
      (encoder q).d2 = P 0 2 - P 0 0 ∧
      (jordan (encoder q) (encoder q)).d0 = P 2 2 + P 2 0 ∧
      (jordan (encoder q) (encoder q)).d1 = P 1 2 + P 1 0 ∧
      (jordan (encoder q) (encoder q)).d2 = P 0 2 + P 0 0 := by
  have h20 : (q 0).d0 = P 2 0 := by rw [← inner_flatFrameP_two]; exact hPQ 2 0
  have h22 : (q 2).d0 = P 2 2 := by rw [← inner_flatFrameP_two]; exact hPQ 2 2
  have h10 : (q 0).d1 = P 1 0 := by rw [← inner_flatFrameP_one]; exact hPQ 1 0
  have h12 : (q 2).d1 = P 1 2 := by rw [← inner_flatFrameP_one]; exact hPQ 1 2
  have h00 : (q 0).d2 = P 0 0 := by rw [← inner_flatFrameP_zero]; exact hPQ 0 0
  have h02 : (q 2).d2 = P 0 2 := by rw [← inner_flatFrameP_zero]; exact hPQ 0 2
  have hsq := frame_encoder_square q hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (q 2).d0 - (q 0).d0 = _
    rw [h22, h20]
  · show (q 2).d1 - (q 0).d1 = _
    rw [h12, h10]
  · show (q 2).d2 - (q 0).d2 = _
    rw [h02, h00]
  · rw [hsq]
    show (q 2).d0 + (q 0).d0 = _
    rw [h22, h20]
  · rw [hsq]
    show (q 2).d1 + (q 0).d1 = _
    rw [h12, h10]
  · rw [hsq]
    show (q 2).d2 + (q 0).d2 = _
    rw [h02, h00]

/-! ## 5. The three complex-square SLOT formulas

The package has `fe_complex_square_d0/d1/d2` (`Theorems/FrameSaturation.lean`) for the
three DIAGONAL entries of a complex-sector square, fully general in `(d,e,f,u,v,w)`, but no slot
companions. These are the companions. The convention is pinned, not guessed: `fe_complex_cubic`
(`:17`) reads `d*e*f - d*normSq w - e*normSq v - f*normSq u + 2*(u*w*star v).re`, which is
exactly the determinant of the Hermitian matrix `[[d,u,v],[star u,e,w],[star v,star w,f]]`, so
`(u,v,w)` are the `(01,02,12)` entries with no conjugation and these three are that matrix
squared. Each also matches `jordan_o01/o02/o12` (`Native.lean`) specialised to
`x = y`. -/

theorem fe_complex_square_o01 (d e f : ℝ) (u v w : ℂ) :
    complexPart (jordan (complexAlbert d e f u v w) (complexAlbert d e f u v w)).o01 =
      u * (d + e) + v * star w := by
  apply Complex.ext
  all_goals
    simp [jordan_o01, complexAlbert, complexOct, complexPart, octMul, octConj,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      smul_eq_mul]
  all_goals ring

theorem fe_complex_square_o02 (d e f : ℝ) (u v w : ℂ) :
    complexPart (jordan (complexAlbert d e f u v w) (complexAlbert d e f u v w)).o02 =
      v * (d + f) + u * w := by
  apply Complex.ext
  all_goals
    simp [jordan_o02, complexAlbert, complexOct, complexPart, octMul, octConj,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      smul_eq_mul]
  all_goals ring

theorem fe_complex_square_o12 (d e f : ℝ) (u v w : ℂ) :
    complexPart (jordan (complexAlbert d e f u v w) (complexAlbert d e f u v w)).o12 =
      w * (e + f) + star u * v := by
  apply Complex.ext
  all_goals
    simp [jordan_o12, complexAlbert, complexOct, complexPart, octMul, octConj,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      smul_eq_mul]
  all_goals ring

/-! ### 5a. The three slot readers of `complexAlbert`

Each is `rfl` componentwise: `complexAlbert` is a plain constructor application, so `.o01`
iota-reduces to `complexOct u`, and `complexPart (complexOct u) = ⟨u.re, u.im⟩`. The componentwise
`Complex.ext` form is used rather than a bare `rfl` on the whole equation so that the proof does
not lean on structure eta. -/

theorem complexPart_complexAlbert_o01 (a b c : ℝ) (u v w : ℂ) :
    complexPart (complexAlbert a b c u v w).o01 = u := by
  apply Complex.ext <;> rfl

theorem complexPart_complexAlbert_o02 (a b c : ℝ) (u v w : ℂ) :
    complexPart (complexAlbert a b c u v w).o02 = v := by
  apply Complex.ext <;> rfl

theorem complexPart_complexAlbert_o12 (a b c : ℝ) (u v w : ℂ) :
    complexPart (complexAlbert a b c u v w).o12 = w := by
  apply Complex.ext <;> rfl

/-! ### 5b. Octonion bookkeeping inside the standard complex line -/

theorem complexPart_octScalar (a : ℝ) : complexPart (octScalar a) = (a : ℂ) := rfl

theorem normSq_complexPart_octScalar (a : ℝ) :
    Complex.normSq (complexPart (octScalar a)) = a ^ 2 := by
  rw [complexPart_octScalar, Complex.normSq_ofReal]; ring

/-- Two elements of the standard complex line with the same complex part are equal. The
chain used `octInComplex_slot_eq` (`FirstPairNormalization.lean`) instead, which additionally
required the real part to VANISH -- true on the flat fibre, false nearby, which is the precise
point at which step 5 of that proof breaks. -/
theorem octInComplex_ext (x x' : Octonion) (hx : OctInComplex x) (hx' : OctInComplex x')
    (h : complexPart x = complexPart x') : x = x' := by
  obtain ⟨hj, hk, hz⟩ := hx
  obtain ⟨hj', hk', hz'⟩ := hx'
  have hre : x.1.re = x'.1.re := congrArg Complex.re h
  have him : x.1.imI = x'.1.imI := congrArg Complex.im h
  apply Prod.ext
  · apply Quaternion.ext
    · exact hre
    · exact him
    · rw [hj, hj']
    · rw [hk, hk']
  · rw [hz, hz']

theorem octInComplex_zero : OctInComplex (0 : Octonion) := ⟨rfl, rfl, rfl⟩

theorem octInComplex_eq_zero (x : Octonion) (hx : OctInComplex x)
    (hre : (complexPart x).re = 0) (him : (complexPart x).im = 0) : x = 0 := by
  refine octInComplex_ext x 0 hx octInComplex_zero ?_
  apply Complex.ext
  · show (complexPart x).re = (complexPart (0 : Octonion)).re
    rw [hre]; rfl
  · show (complexPart x).im = (complexPart (0 : Octonion)).im
    rw [him]; rfl

theorem octInComplex_decomp (x : Octonion) (hx : OctInComplex x) :
    x = octScalar (complexPart x).re + (complexPart x).im • octI := by
  obtain ⟨hj, hk, hz⟩ := hx
  apply Prod.ext
  · apply Quaternion.ext <;> simp [octScalar, octI, quatI, complexPart, hj, hk]
  · simp [octScalar, octI, quatI, hz]


theorem octDot_inComplex (x x' : Octonion) (hx : OctInComplex x) (hx' : OctInComplex x') :
    octDot x x' = (complexPart x).re * (complexPart x').re +
      (complexPart x).im * (complexPart x').im := by
  obtain ⟨hj, hk, hz⟩ := hx
  obtain ⟨hj', hk', hz'⟩ := hx'
  rw [octDot_coordinates]
  simp [complexPart, hj, hk, hz, hj', hk', hz']

/-- `real_real_conj_re` of `FirstPairNormalization.lean`, which is `private` there. -/
theorem real_real_conj_re (a b : ℝ) (z : ℂ) :
    ((a : ℂ) * (b : ℂ) * star z).re = a * b * z.re := by
  have hs : (star z).re = z.re := rfl
  have hi : (star z).im = -z.im := rfl
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hs, hi]
  ring

theorem real_real_conj_im (a b : ℝ) (z : ℂ) :
    ((a : ℂ) * (b : ℂ) * star z).im = -(a * b * z.im) := by
  have hs : (star z).re = z.re := rfl
  have hi : (star z).im = -z.im := rfl
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hs, hi]
  ring

/-! ## 6. The slot data of a complex-sector frame encoder, with symbols for the numerals

This is `uniform_complex_slot_data` (`FirstPairNormalization.lean`) and
`complex_slot_data_of_square` (`:87`) with `0`, `2/3` and `1/3` replaced by variables. The
interior of both is `linarith` over `fe_complex_square_d*` and `fe_complex_cubic`, all of which
are already general in `(d,e,f,u,v,w)`; only the SUBSTITUTED VALUES broke. Stated as a
comparison, which is all the route consumes, so no formula has to be written down and no square
root is ever taken. -/

theorem slot_data_eq_of_diag_eq (y y' : Albert)
    (hc : InComplexSector y) (hc' : InComplexSector y')
    (hd0 : y.d0 = y'.d0) (hd1 : y.d1 = y'.d1) (hd2 : y.d2 = y'.d2)
    (hs0 : (jordan y y).d0 = (jordan y' y').d0)
    (hs1 : (jordan y y).d1 = (jordan y' y').d1)
    (hs2 : (jordan y y).d2 = (jordan y' y').d2)
    (hcub : newtonCubicNorm y = newtonCubicNorm y') :
    Complex.normSq (complexPart y.o01) = Complex.normSq (complexPart y'.o01) ∧
      Complex.normSq (complexPart y.o02) = Complex.normSq (complexPart y'.o02) ∧
      Complex.normSq (complexPart y.o12) = Complex.normSq (complexPart y'.o12) ∧
      (complexPart y.o01 * complexPart y.o12 * star (complexPart y.o02)).re =
        (complexPart y'.o01 * complexPart y'.o12 * star (complexPart y'.o02)).re := by
  have E0 := fe_complex_square_d0 y.d0 y.d1 y.d2
    (complexPart y.o01) (complexPart y.o02) (complexPart y.o12)
  have E1 := fe_complex_square_d1 y.d0 y.d1 y.d2
    (complexPart y.o01) (complexPart y.o02) (complexPart y.o12)
  have E2 := fe_complex_square_d2 y.d0 y.d1 y.d2
    (complexPart y.o01) (complexPart y.o02) (complexPart y.o12)
  have C := fe_complex_cubic y.d0 y.d1 y.d2
    (complexPart y.o01) (complexPart y.o02) (complexPart y.o12)
  rw [complexAlbert_eq y hc] at E0 E1 E2 C
  have E0' := fe_complex_square_d0 y'.d0 y'.d1 y'.d2
    (complexPart y'.o01) (complexPart y'.o02) (complexPart y'.o12)
  have E1' := fe_complex_square_d1 y'.d0 y'.d1 y'.d2
    (complexPart y'.o01) (complexPart y'.o02) (complexPart y'.o12)
  have E2' := fe_complex_square_d2 y'.d0 y'.d1 y'.d2
    (complexPart y'.o01) (complexPart y'.o02) (complexPart y'.o12)
  have C' := fe_complex_cubic y'.d0 y'.d1 y'.d2
    (complexPart y'.o01) (complexPart y'.o02) (complexPart y'.o12)
  rw [complexAlbert_eq y' hc'] at E0' E1' E2' C'
  -- each hypothesis is rewritten with exactly the diagonal equations that occur in it
  rw [hd0] at E0
  rw [hd1] at E1
  rw [hd2] at E2
  rw [hd0, hd1, hd2] at C
  rw [hs0] at E0
  rw [hs1] at E1
  rw [hs2] at E2
  rw [hcub] at C
  have h01 : Complex.normSq (complexPart y.o01) = Complex.normSq (complexPart y'.o01) := by
    linarith
  have h02 : Complex.normSq (complexPart y.o02) = Complex.normSq (complexPart y'.o02) := by
    linarith
  have h12 : Complex.normSq (complexPart y.o12) = Complex.normSq (complexPart y'.o12) := by
    linarith
  refine ⟨h01, h02, h12, ?_⟩
  rw [h01, h02, h12] at C
  linarith

/-! ### 6a. The nondegeneracy supplied by the neighbourhood

Nothing in section 6 needs the overlaps to be near uniform. The epsilon box is needed in exactly
three places: `0 < a`, `0 < b` and `(complexPart y.o02).im /= 0`.
The four algebraic identities here supply the nine real numbers to `nondegenerate_core`
(section 1). The triangle term is rewritten in a separate `have` so the norm-square
atoms remain in the form used by the goal. -/

theorem slot_nondegenerate (y : Albert) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : InComplexSector y)
    (h01 : y.o01 = octScalar a) (h12 : y.o12 = octScalar b)
    (hcub : newtonCubicNorm y = 0)
    (hc0 : |y.d0| < 1 / 25) (hc1 : |y.d1| < 1 / 25) (hc2 : |y.d2| < 1 / 25)
    (he0 : |(jordan y y).d0 - 2 / 3| < 1 / 25)
    (he1 : |(jordan y y).d1 - 2 / 3| < 1 / 25)
    (he2 : |(jordan y y).d2 - 2 / 3| < 1 / 25) :
    1 / 2 < a ∧ 1 / 2 < b ∧ (complexPart y.o02).im ≠ 0 := by
  have E0 := fe_complex_square_d0 y.d0 y.d1 y.d2
    (complexPart y.o01) (complexPart y.o02) (complexPart y.o12)
  have E1 := fe_complex_square_d1 y.d0 y.d1 y.d2
    (complexPart y.o01) (complexPart y.o02) (complexPart y.o12)
  have E2 := fe_complex_square_d2 y.d0 y.d1 y.d2
    (complexPart y.o01) (complexPart y.o02) (complexPart y.o12)
  have C := fe_complex_cubic y.d0 y.d1 y.d2
    (complexPart y.o01) (complexPart y.o02) (complexPart y.o12)
  rw [complexAlbert_eq y hc] at E0 E1 E2 C
  have hau : Complex.normSq (complexPart y.o01) = a ^ 2 := by
    rw [h01, normSq_complexPart_octScalar]
  have hbw : Complex.normSq (complexPart y.o12) = b ^ 2 := by
    rw [h12, normSq_complexPart_octScalar]
  -- the triangle real part, in its own `have`, so that the slot ENERGIES in `C` keep the atoms
  -- the goal names
  have htriangle : (complexPart y.o01 * complexPart y.o12 *
      star (complexPart y.o02)).re = a * b * (complexPart y.o02).re := by
    rw [h01, h12, complexPart_octScalar, complexPart_octScalar, real_real_conj_re]
  rw [hau] at E0
  rw [hau, hbw] at E1
  rw [hbw] at E2
  rw [hcub, hau, hbw, htriangle] at C
  have hsplit : Complex.normSq (complexPart y.o02) =
      (complexPart y.o02).re ^ 2 + (complexPart y.o02).im ^ 2 := by
    rw [Complex.normSq_apply]; ring
  exact nondegenerate_core a b y.d0 y.d1 y.d2
    (jordan y y).d0 (jordan y y).d1 (jordan y y).d2
    (Complex.normSq (complexPart y.o02)) (complexPart y.o02).re (complexPart y.o02).im
    ha hb hc0 hc1 hc2 he0 he1 he2 (Complex.normSq_nonneg _) E0 E1 E2 C hsplit

/-! ## 7. The pair, perturbed: pair normalization

Step 5 of the proof -- `flatQ_slots` (`FirstPairNormalization.lean`) and
`encoder_to_flatQ` (`:244`) -- is what breaks hardest: both name the target
`flatScale • flatY1`. Nearby there is no canonical target, so "normalise onto a fixed element"
becomes "two normal forms with the same P data are related". The sign branch is still resolved by
`exists_octAutomorphism_to_i (-octI)`, exactly as at `:283`, but that automorphism must now act
on a GENERAL complex slot `rho + sigma*octI`, not just on `sigma*octI`; that is the one place
where the whole of `DiagonalOctTriple` is needed. `octConj` is NOT used: octonion conjugation is
an anti-automorphism and can never be a sign corrector. -/

theorem relatedTriple_flatXN (t : OctRelatedTriple) :
    t.compactAutomorphism.equiv flatXN = flatXN := by
  change (⟨flatXN.d0, flatXN.d1, flatXN.d2,
    t.A flatXN.o01, t.C flatXN.o02, t.B flatXN.o12⟩ : Albert) = flatXN
  simp [flatXN, map_zero]

theorem relatedTriple_fixes_flatFrameP (t : OctRelatedTriple) (i : Fin 3) :
    t.compactAutomorphism.equiv (flatFrameP i) = flatFrameP i :=
  frame_eq_of_encoder_eq flatFrameP flatFrameP flatFrameP_frame flatFrameP_frame
    t.compactAutomorphism
    (by rw [flatFrameP_encoder]; exact relatedTriple_flatXN t) i

/-- The sign-flip automorphism conjugates the whole complex line, not merely its imaginary
axis. `DiagonalOctTriple` (`Theorems/OctonionAutomorphisms.lean`) says `B = A`, `C = A` and
`A (octScalar 1) = octScalar 1`; with `A octI = -octI` and real linearity that is all that is
needed. -/
theorem diagonalOctTriple_conj_slot (k : OctRelatedTriple) (hk : DiagonalOctTriple k)
    (hkI : k.A octI = -octI) (x : Octonion) (hx : OctInComplex x) :
    k.A x = octScalar (complexPart x).re - (complexPart x).im • octI := by
  have hd : x = octScalar (complexPart x).re + (complexPart x).im • octI :=
    octInComplex_decomp x hx
  calc k.A x
      = k.A (octScalar (complexPart x).re + (complexPart x).im • octI) := by rw [← hd]
    _ = k.A (octScalar (complexPart x).re) + (complexPart x).im • k.A octI := by
        rw [map_add, map_smul]
    _ = octScalar (complexPart x).re - (complexPart x).im • octI := by
        rw [diagonalOctTriple_scalar k hk, hkI, smul_neg, ← sub_eq_add_neg]

theorem octInComplex_conj_slot (k : OctRelatedTriple) (hk : DiagonalOctTriple k)
    (hkI : k.A octI = -octI) (x : Octonion) (hx : OctInComplex x) :
    OctInComplex (k.A x) ∧ complexPart (k.A x) = star (complexPart x) := by
  rw [diagonalOctTriple_conj_slot k hk hkI x hx]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · simp [octScalar, octI, quatI]
  · simp [octScalar, octI, quatI]
  · simp [octScalar, octI, quatI]
  · apply Complex.ext <;>
      simp [complexPart, octScalar, octI, quatI, Complex.star_def, Complex.conj_re,
        Complex.conj_im]

theorem neg_octI_re : octRe (-octI) = 0 := by
  have h : -octI = ((⟨0, -1, 0, 0⟩ : Quaternion ℝ), (0 : Quaternion ℝ)) := by
    apply Prod.ext <;> apply Quaternion.ext <;> simp [octI, quatI]
  rw [h]; rfl

theorem neg_octI_normSq : octNormSq (-octI) = 1 := by
  have h : -octI = ((⟨0, -1, 0, 0⟩ : Quaternion ℝ), (0 : Quaternion ℝ)) := by
    apply Prod.ext <;> apply Quaternion.ext <;> simp [octI, quatI]
  rw [h]; norm_num [octNormSq, Quaternion.normSq_def']

/-- The automorphism built from `exists_octAutomorphism_to_i (-octI)`: it fixes `flatFrameP`
pointwise, fixes every real slot and conjugates every complex slot. -/
theorem exists_slot_conjugator :
    ∃ m : CompactAutomorphism,
      (∀ i : Fin 3, m.equiv (flatFrameP i) = flatFrameP i) ∧
      (∀ y : Albert, InComplexSector y →
        (m.equiv y).d0 = y.d0 ∧ (m.equiv y).d1 = y.d1 ∧ (m.equiv y).d2 = y.d2 ∧
        complexPart (m.equiv y).o01 = star (complexPart y.o01) ∧
        complexPart (m.equiv y).o02 = star (complexPart y.o02) ∧
        complexPart (m.equiv y).o12 = star (complexPart y.o12) ∧
        InComplexSector (m.equiv y)) := by
  obtain ⟨k, hk, hkI⟩ := exists_octAutomorphism_to_i (-octI) neg_octI_re neg_octI_normSq
  have hkIneg : k.A octI = -octI := by
    have h : k.A ((-1 : ℝ) • octI) = octI := by rw [neg_one_smul]; exact hkI
    rw [LinearEquiv.map_smul, neg_one_smul] at h
    have h2 := congrArg (fun x : Octonion => -x) h
    simpa only [neg_neg] using h2
  refine ⟨k.compactAutomorphism, relatedTriple_fixes_flatFrameP k, ?_⟩
  intro y hy
  have hA01 := octInComplex_conj_slot k hk hkIneg y.o01 hy.1
  have hC02 := octInComplex_conj_slot k hk hkIneg y.o02 hy.2.1
  have hB12 := octInComplex_conj_slot k hk hkIneg y.o12 hy.2.2
  have hslot01 : (k.compactAutomorphism.equiv y).o01 = k.A y.o01 := rfl
  have hslot02 : (k.compactAutomorphism.equiv y).o02 = k.C y.o02 := rfl
  have hslot12 : (k.compactAutomorphism.equiv y).o12 = k.B y.o12 := rfl
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [hslot01]; exact hA01.2
  · rw [hslot02, hk.2.1]; exact hC02.2
  · rw [hslot12, hk.1]; exact hB12.2
  · refine ⟨?_, ?_, ?_⟩
    · rw [hslot01]; exact hA01.1
    · rw [hslot02, hk.2.1]; exact hC02.1
    · rw [hslot12, hk.1]; exact hB12.1

/-- Two Step-A normal forms with the same P data are equal, or are carried to one another by one
automorphism that fixes `flatFrameP` pointwise. This is the perturbed `encoder_to_flatQ`. -/
theorem pair_normal_form_rel (y y' : Albert) (a b a' b' : ℝ)
    (hc : InComplexSector y) (hc' : InComplexSector y')
    (h01 : y.o01 = octScalar a) (h12 : y.o12 = octScalar b)
    (h01' : y'.o01 = octScalar a') (h12' : y'.o12 = octScalar b')
    (hd0 : y.d0 = y'.d0) (hd1 : y.d1 = y'.d1) (hd2 : y.d2 = y'.d2)
    (haa : a = a') (hbb : b = b')
    (hre : (complexPart y.o02).re = (complexPart y'.o02).re)
    (himsq : (complexPart y.o02).im ^ 2 = (complexPart y'.o02).im ^ 2) :
    ∃ m : CompactAutomorphism,
      (∀ i : Fin 3, m.equiv (flatFrameP i) = flatFrameP i) ∧ m.equiv y = y' := by
  have hy01 : y.o01 = y'.o01 := by rw [h01, h01', haa]
  have hy12 : y.o12 = y'.o12 := by rw [h12, h12', hbb]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp himsq with him | him
  · refine ⟨CompactAutomorphism.refl, fun _ => rfl, ?_⟩
    show y = y'
    refine Albert.ext hd0 hd1 hd2 hy01 ?_ hy12
    exact octInComplex_ext y.o02 y'.o02 hc.2.1 hc'.2.1 (Complex.ext hre him)
  · obtain ⟨m, hmP, hmslots⟩ := exists_slot_conjugator
    obtain ⟨e0, e1, e2, c01, c02, c12, hsec⟩ := hmslots y hc
    refine ⟨m, hmP, ?_⟩
    refine Albert.ext ?_ ?_ ?_ ?_ ?_ ?_
    · rw [e0]; exact hd0
    · rw [e1]; exact hd1
    · rw [e2]; exact hd2
    · refine octInComplex_ext _ _ hsec.1 hc'.1 ?_
      rw [c01, h01, h01', complexPart_octScalar, complexPart_octScalar, haa]
      exact Complex.conj_ofReal a'
    · refine octInComplex_ext _ _ hsec.2.1 hc'.2.1 ?_
      rw [c02]
      apply Complex.ext
      · show (complexPart y.o02).re = (complexPart y'.o02).re
        exact hre
      · show -(complexPart y.o02).im = (complexPart y'.o02).im
        linarith [him]
    · refine octInComplex_ext _ _ hsec.2.2 hc'.2.2 ?_
      rw [c12, h12, h12', complexPart_octScalar, complexPart_octScalar, hbb]
      exact Complex.conj_ofReal b'

/-- **THE EXTENSION OF `native_flat_pair_normalization` (`FirstPairNormalization.lean`).**

Two genuine frame pairs whose nine overlaps AGREE, and are within `1/50` of uniform, are carried
onto ONE AND THE SAME normalised pair by two actual product automorphisms, and that common
normal form is exhibited with its two positive real slots and its nonvanishing imaginary slot.

At the exact value `1/3` this specialises to the theorem, with `flatFrameQ` as the
common target. Away from it, the common target is the P-block-determined normal form and is NOT
named -- which is why the proof's `flatQ_slots` and `encoder_to_flatQ` had to be
replaced rather than reused. -/
theorem nearby_pair_normalization
    (p q p' q' : Fin 3 → Albert)
    (hp : Frame p) (hq : Frame q) (hp' : Frame p') (hq' : Frame q')
    (hbox : ∀ i j : Fin 3, |inner (p i) (q j) - 1 / 3| < 1 / 50)
    (hEq : ∀ i j : Fin 3, inner (p i) (q j) = inner (p' i) (q' j)) :
    ∃ (g g' : CompactAutomorphism) (a b : ℝ),
      (∀ i : Fin 3, g.equiv (p i) = flatFrameP i) ∧
      (∀ i : Fin 3, g'.equiv (p' i) = flatFrameP i) ∧
      (∀ i : Fin 3, g.equiv (q i) = g'.equiv (q' i)) ∧
      InComplexSector (encoder fun i => g'.equiv (q' i)) ∧
      (encoder fun i => g'.equiv (q' i)).o01 = octScalar a ∧
      (encoder fun i => g'.equiv (q' i)).o12 = octScalar b ∧
      0 < a ∧ 0 < b ∧
      (complexPart (encoder fun i => g'.equiv (q' i)).o02).im ≠ 0 := by
  -- Step A on each pair.  No `1/3` enters here: `native_ordered_positive_pair`
  -- (`OrderedPositivePair.lean`) takes an ARBITRARY Albert element.
  obtain ⟨g, a, b, ha, hb, hgp, h01g, h12g, hsecg⟩ :=
    native_ordered_positive_pair p hp (encoder q)
  obtain ⟨g', a', b', ha', hb', hgp', h01g', h12g', hsecg'⟩ :=
    native_ordered_positive_pair p' hp' (encoder q')
  have hQframe : Frame (fun i => g.equiv (q i)) := g.map_frame q hq
  have hQframe' : Frame (fun i => g'.equiv (q' i)) := g'.map_frame q' hq'
  have hyg : (encoder fun i => g.equiv (q i)) = g.equiv (encoder q) := g.encoder_map q
  have hyg' : (encoder fun i => g'.equiv (q' i)) = g'.equiv (encoder q') := g'.encoder_map q'
  have hcy : InComplexSector (encoder fun i => g.equiv (q i)) := by rw [hyg]; exact hsecg
  have hcy' : InComplexSector (encoder fun i => g'.equiv (q' i)) := by rw [hyg']; exact hsecg'
  have hy01 : (encoder fun i => g.equiv (q i)).o01 = octScalar a := by rw [hyg]; exact h01g
  have hy12 : (encoder fun i => g.equiv (q i)).o12 = octScalar b := by rw [hyg]; exact h12g
  have hy01' : (encoder fun i => g'.equiv (q' i)).o01 = octScalar a' := by rw [hyg']; exact h01g'
  have hy12' : (encoder fun i => g'.equiv (q' i)).o12 = octScalar b' := by rw [hyg']; exact h12g'
  -- the normalised overlaps ARE the P block
  have hPQ : ∀ i j : Fin 3,
      inner (flatFrameP i) ((fun i => g.equiv (q i)) j) = inner (p i) (q j) := by
    intro i j
    rw [← hgp i]
    exact g.inner_map (p i) (q j)
  have hPQ' : ∀ i j : Fin 3,
      inner (flatFrameP i) ((fun i => g'.equiv (q' i)) j) = inner (p i) (q j) := by
    intro i j
    rw [← hgp' i, g'.inner_map (p' i) (q' j)]
    exact (hEq i j).symm
  obtain ⟨d0, d1, d2, e0, e1, e2⟩ :=
    normalised_diag_data (fun i => g.equiv (q i)) hQframe (fun i j => inner (p i) (q j)) hPQ
  obtain ⟨d0', d1', d2', e0', e1', e2'⟩ :=
    normalised_diag_data (fun i => g'.equiv (q' i)) hQframe' (fun i j => inner (p i) (q j)) hPQ'
  have hd0 : (encoder fun i => g.equiv (q i)).d0 =
      (encoder fun i => g'.equiv (q' i)).d0 := by rw [d0, d0']
  have hd1 : (encoder fun i => g.equiv (q i)).d1 =
      (encoder fun i => g'.equiv (q' i)).d1 := by rw [d1, d1']
  have hd2 : (encoder fun i => g.equiv (q i)).d2 =
      (encoder fun i => g'.equiv (q' i)).d2 := by rw [d2, d2']
  have hs0 : (jordan (encoder fun i => g.equiv (q i)) (encoder fun i => g.equiv (q i))).d0 =
      (jordan (encoder fun i => g'.equiv (q' i)) (encoder fun i => g'.equiv (q' i))).d0 := by
    rw [e0, e0']
  have hs1 : (jordan (encoder fun i => g.equiv (q i)) (encoder fun i => g.equiv (q i))).d1 =
      (jordan (encoder fun i => g'.equiv (q' i)) (encoder fun i => g'.equiv (q' i))).d1 := by
    rw [e1, e1']
  have hs2 : (jordan (encoder fun i => g.equiv (q i)) (encoder fun i => g.equiv (q i))).d2 =
      (jordan (encoder fun i => g'.equiv (q' i)) (encoder fun i => g'.equiv (q' i))).d2 := by
    rw [e2, e2']
  have hcub : newtonCubicNorm (encoder fun i => g.equiv (q i)) = 0 :=
    frame_encoder_cubicNorm _ hQframe
  have hcub' : newtonCubicNorm (encoder fun i => g'.equiv (q' i)) = 0 :=
    frame_encoder_cubicNorm _ hQframe'
  have hcubeq : newtonCubicNorm (encoder fun i => g.equiv (q i)) =
      newtonCubicNorm (encoder fun i => g'.equiv (q' i)) := by rw [hcub, hcub']
  -- the epsilon box, transported through the six numbers
  have habs : ∀ i j : Fin 3,
      -(1 / 50 : ℝ) < inner (p i) (q j) - 1 / 3 ∧ inner (p i) (q j) - 1 / 3 < 1 / 50 :=
    fun i j => abs_lt.mp (hbox i j)
  have hc0 : |(encoder fun i => g.equiv (q i)).d0| < 1 / 25 := by
    rw [d0, abs_lt]
    have h1 := habs 2 2
    have h2 := habs 2 0
    exact ⟨by linarith [h1.1, h1.2, h2.1, h2.2], by linarith [h1.1, h1.2, h2.1, h2.2]⟩
  have hc1 : |(encoder fun i => g.equiv (q i)).d1| < 1 / 25 := by
    rw [d1, abs_lt]
    have h1 := habs 1 2
    have h2 := habs 1 0
    exact ⟨by linarith [h1.1, h1.2, h2.1, h2.2], by linarith [h1.1, h1.2, h2.1, h2.2]⟩
  have hc2 : |(encoder fun i => g.equiv (q i)).d2| < 1 / 25 := by
    rw [d2, abs_lt]
    have h1 := habs 0 2
    have h2 := habs 0 0
    exact ⟨by linarith [h1.1, h1.2, h2.1, h2.2], by linarith [h1.1, h1.2, h2.1, h2.2]⟩
  have he0b : |(jordan (encoder fun i => g.equiv (q i))
      (encoder fun i => g.equiv (q i))).d0 - 2 / 3| < 1 / 25 := by
    rw [e0, abs_lt]
    have h1 := habs 2 2
    have h2 := habs 2 0
    exact ⟨by linarith [h1.1, h1.2, h2.1, h2.2], by linarith [h1.1, h1.2, h2.1, h2.2]⟩
  have he1b : |(jordan (encoder fun i => g.equiv (q i))
      (encoder fun i => g.equiv (q i))).d1 - 2 / 3| < 1 / 25 := by
    rw [e1, abs_lt]
    have h1 := habs 1 2
    have h2 := habs 1 0
    exact ⟨by linarith [h1.1, h1.2, h2.1, h2.2], by linarith [h1.1, h1.2, h2.1, h2.2]⟩
  have he2b : |(jordan (encoder fun i => g.equiv (q i))
      (encoder fun i => g.equiv (q i))).d2 - 2 / 3| < 1 / 25 := by
    rw [e2, abs_lt]
    have h1 := habs 0 2
    have h2 := habs 0 0
    exact ⟨by linarith [h1.1, h1.2, h2.1, h2.2], by linarith [h1.1, h1.2, h2.1, h2.2]⟩
  obtain ⟨hapos, hbpos, hsigma⟩ :=
    slot_nondegenerate (encoder fun i => g.equiv (q i)) a b ha hb hcy hy01 hy12 hcub
      hc0 hc1 hc2 he0b he1b he2b
  -- the slot data of the two normal forms agree
  obtain ⟨hn01, hn02, hn12, htri⟩ :=
    slot_data_eq_of_diag_eq _ _ hcy hcy' hd0 hd1 hd2 hs0 hs1 hs2 hcubeq
  have haa : a = a' := by
    rw [hy01, hy01', normSq_complexPart_octScalar, normSq_complexPart_octScalar] at hn01
    exact nonneg_sq_eq_of_sq_eq a a' ha ha' hn01
  have hbb : b = b' := by
    rw [hy12, hy12', normSq_complexPart_octScalar, normSq_complexPart_octScalar] at hn12
    exact nonneg_sq_eq_of_sq_eq b b' hb hb' hn12
  have hre : (complexPart (encoder fun i => g.equiv (q i)).o02).re =
      (complexPart (encoder fun i => g'.equiv (q' i)).o02).re := by
    rw [hy01, hy12, hy01', hy12', complexPart_octScalar, complexPart_octScalar,
      complexPart_octScalar, complexPart_octScalar, real_real_conj_re,
      real_real_conj_re, ← haa, ← hbb] at htri
    exact mul_left_cancel₀ (ne_of_gt (mul_pos (by linarith : (0 : ℝ) < a)
      (by linarith : (0 : ℝ) < b))) htri
  have himsq : (complexPart (encoder fun i => g.equiv (q i)).o02).im ^ 2 =
      (complexPart (encoder fun i => g'.equiv (q' i)).o02).im ^ 2 :=
    im_sq_eq_of_normSq_eq _ _ hn02 hre
  have hsigma' : (complexPart (encoder fun i => g'.equiv (q' i)).o02).im ≠ 0 :=
    ne_zero_of_sq_eq_of_ne_zero _ _ himsq hsigma
  -- compare the two normal forms and absorb the sign
  obtain ⟨m, hmP, hmy⟩ :=
    pair_normal_form_rel _ _ a b a' b' hcy hcy' hy01 hy12 hy01' hy12'
      hd0 hd1 hd2 haa hbb hre himsq
  refine ⟨m.comp g, g', a', b', ?_, hgp', ?_, hcy', hy01', hy12', ?_, ?_, hsigma'⟩
  · intro i
    rw [CompactAutomorphism.comp_apply, hgp i]
    exact hmP i
  · intro i
    refine frame_eq_of_encoder_eq q (fun i => g'.equiv (q' i)) hq hQframe' (m.comp g) ?_ i
    rw [CompactAutomorphism.comp_apply, ← hyg, hmy]
  · linarith [haa, hapos]
  · linarith [hbb, hbpos]

/-! ## 8. The ledger sees the third frame's sector data, slot by slot

This replaces `uniformLedger_complexProjection_encoder(_square)`
(`Theorems/ComplexSectorSpan.lean`), which recover the sector projection by declaring the
nine mixed products `jordan (p i) (q j)` a BASIS -- which needs
`uniform_pair_mixed_linearIndependent` and so the EXACT uniform P block. Linear independence is
an open condition, so a perturbation of that route would need an openness proof for a 9x9
determinant in a variable produced by an existential. The route below avoids spanning
altogether: it extracts the nine sector coordinates one at a time, at the cost of three 2x2
determinants, each of which is `a*b*sigma` up to sign and so nonzero by section 6a. -/

theorem inner_sector_complexProjection (v W : Albert) (hv : InComplexSector v) :
    inner v W = inner v (complexProjection W) := by
  conv_lhs => rw [← complex_hidden_decomposition W]
  rw [inner_add_right]
  have h : inner v (hiddenAlbert (hiddenMatrix W)) = 0 := by
    rw [← complexProjection_eq_self v hv]
    exact complex_hidden_orthogonal v (hiddenMatrix W)
  rw [h, add_zero]

/-- With a diagonal left factor and a diagonal-free right factor, the ledger probe is exactly
three slot pairings with rational coefficients. `jordan_o01/o02/o12` collapse because every slot
of the left factor is zero.

The four section-1a lemmas simplify the octonion zero terms. -/
theorem inner_diag_jordan_slots (x z E : Albert) (hxd : IsDiagonal x)
    (hE0 : E.d0 = 0) (hE1 : E.d1 = 0) (hE2 : E.d2 = 0) :
    inner (jordan x z) E =
      (x.d0 + x.d1) * octDot z.o01 E.o01 + (x.d0 + x.d2) * octDot z.o02 E.o02 +
        (x.d1 + x.d2) * octDot z.o12 E.o12 := by
  obtain ⟨hx01, hx02, hx12⟩ := hxd
  have s01 : (jordan x z).o01 = (1 / 2 : ℝ) • ((x.d0 + x.d1) • z.o01) := by
    rw [jordan_o01, hx01, hx02, hx12]
    simp [octConj_zero, octMul_zero_left, octMul_zero_right]
  have s02 : (jordan x z).o02 = (1 / 2 : ℝ) • ((x.d0 + x.d2) • z.o02) := by
    rw [jordan_o02, hx01, hx02, hx12]
    simp [octConj_zero, octMul_zero_left, octMul_zero_right]
  have s12 : (jordan x z).o12 = (1 / 2 : ℝ) • ((x.d1 + x.d2) • z.o12) := by
    rw [jordan_o12, hx01, hx02, hx12]
    simp [octConj_zero, octMul_zero_left, octMul_zero_right]
  rw [inner_coordinates, hE0, hE1, hE2, s01, s02, s12,
    octDot_smul_left, octDot_smul_left, octDot_smul_left,
    octDot_smul_left, octDot_smul_left, octDot_smul_left]
  ring

/-- The three slot pairings vanish. The `flatFrameP` probes give `A+B = 0`, `A+C = 0`,
`B+C = 0`, which `linarith` closes. The ledger's Q block is NOT needed. -/
theorem slot_pairings_zero (z E : Albert)
    (hE0 : E.d0 = 0) (hE1 : E.d1 = 0) (hE2 : E.d2 = 0)
    (h0 : inner (jordan (flatFrameP 0) z) E = 0)
    (h1 : inner (jordan (flatFrameP 1) z) E = 0)
    (h2 : inner (jordan (flatFrameP 2) z) E = 0) :
    octDot z.o01 E.o01 = 0 ∧ octDot z.o02 E.o02 = 0 ∧ octDot z.o12 E.o12 = 0 := by
  rw [inner_diag_jordan_slots _ z E (flatFrameP_isDiagonal 0) hE0 hE1 hE2,
    flatFrameP_zero_eq] at h0
  rw [inner_diag_jordan_slots _ z E (flatFrameP_isDiagonal 1) hE0 hE1 hE2,
    flatFrameP_one_eq] at h1
  rw [inner_diag_jordan_slots _ z E (flatFrameP_isDiagonal 2) hE0 hE1 hE2,
    flatFrameP_two_eq] at h2
  simp only [diagonalAlbert, zero_add, add_zero, zero_mul, one_mul] at h0 h1 h2
  exact ⟨by linarith, by linarith, by linarith⟩

/-- **Sector recovery.** A sector element with vanishing diagonal, orthogonal to the normalised
second encoder and to its square in every slot, is zero.

The proof computes the real and imaginary parts of the three square slots explicitly
(six one-line `simp only` plus `ring` from section 5's formulas), turns each slot into a
homogeneous 2x2 real system, and closes it with `two_by_two` (section 1), whose determinants are
`a*b*sigma` for slot 01, `-(sigma*(a*b))` for slot 02 and `a*b*sigma` for slot 12. Each
determinant is nonzero from `0 < a`, `0 < b`, `sigma /= 0` and nothing else. -/
theorem sector_slot_recovery (y E : Albert) (a b : ℝ)
    (hcy : InComplexSector y) (hcE : InComplexSector E)
    (h01 : y.o01 = octScalar a) (h12 : y.o12 = octScalar b)
    (hapos : 0 < a) (hbpos : 0 < b)
    (hsigma : (complexPart y.o02).im ≠ 0)
    (hE0 : E.d0 = 0) (hE1 : E.d1 = 0) (hE2 : E.d2 = 0)
    (p1 : octDot y.o01 E.o01 = 0) (p2 : octDot y.o02 E.o02 = 0)
    (p3 : octDot y.o12 E.o12 = 0)
    (q1 : octDot (jordan y y).o01 E.o01 = 0) (q2 : octDot (jordan y y).o02 E.o02 = 0)
    (q3 : octDot (jordan y y).o12 E.o12 = 0) :
    E = 0 := by
  have hcsq : InComplexSector (jordan y y) := complexSector_jordan y y hcy hcy
  have hua : complexPart y.o01 = (a : ℂ) := by rw [h01, complexPart_octScalar]
  have hwb : complexPart y.o12 = (b : ℂ) := by rw [h12, complexPart_octScalar]
  -- the three square slots, from section 5
  have S01 : complexPart (jordan y y).o01 =
      complexPart y.o01 * ((y.d0 : ℂ) + (y.d1 : ℂ)) +
        complexPart y.o02 * star (complexPart y.o12) := by
    have h := fe_complex_square_o01 y.d0 y.d1 y.d2
      (complexPart y.o01) (complexPart y.o02) (complexPart y.o12)
    rw [complexAlbert_eq y hcy] at h
    exact h
  have S02 : complexPart (jordan y y).o02 =
      complexPart y.o02 * ((y.d0 : ℂ) + (y.d2 : ℂ)) +
        complexPart y.o01 * complexPart y.o12 := by
    have h := fe_complex_square_o02 y.d0 y.d1 y.d2
      (complexPart y.o01) (complexPart y.o02) (complexPart y.o12)
    rw [complexAlbert_eq y hcy] at h
    exact h
  have S12 : complexPart (jordan y y).o12 =
      complexPart y.o12 * ((y.d1 : ℂ) + (y.d2 : ℂ)) +
        star (complexPart y.o01) * complexPart y.o02 := by
    have h := fe_complex_square_o12 y.d0 y.d1 y.d2
      (complexPart y.o01) (complexPart y.o02) (complexPart y.o12)
    rw [complexAlbert_eq y hcy] at h
    exact h
  -- the six real components of the three square slots
  have Z01re : (complexPart (jordan y y).o01).re =
      a * (y.d0 + y.d1) + b * (complexPart y.o02).re := by
    rw [S01, hua, hwb]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  have Z01im : (complexPart (jordan y y).o01).im = b * (complexPart y.o02).im := by
    rw [S01, hua, hwb]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  have Z02re : (complexPart (jordan y y).o02).re =
      (complexPart y.o02).re * (y.d0 + y.d2) + a * b := by
    rw [S02, hua, hwb]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have Z02im : (complexPart (jordan y y).o02).im =
      (complexPart y.o02).im * (y.d0 + y.d2) := by
    rw [S02, hua, hwb]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have Z12re : (complexPart (jordan y y).o12).re =
      b * (y.d1 + y.d2) + a * (complexPart y.o02).re := by
    rw [S12, hua, hwb]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  have Z12im : (complexPart (jordan y y).o12).im = a * (complexPart y.o02).im := by
    rw [S12, hua, hwb]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  -- slot 01
  rw [octDot_inComplex y.o01 E.o01 hcy.1 hcE.1, hua,
    Complex.ofReal_re, Complex.ofReal_im] at p1
  rw [octDot_inComplex (jordan y y).o01 E.o01 hcsq.1 hcE.1, Z01re, Z01im] at q1
  have hdet01 : a * (b * (complexPart y.o02).im) -
      0 * (a * (y.d0 + y.d1) + b * (complexPart y.o02).re) ≠ 0 := by
    simp only [zero_mul, sub_zero]
    exact mul_ne_zero (ne_of_gt hapos) (mul_ne_zero (ne_of_gt hbpos) hsigma)
  obtain ⟨r01, i01⟩ := two_by_two a 0
    (a * (y.d0 + y.d1) + b * (complexPart y.o02).re) (b * (complexPart y.o02).im)
    (complexPart E.o01).re (complexPart E.o01).im p1 q1 hdet01
  -- slot 02
  rw [octDot_inComplex y.o02 E.o02 hcy.2.1 hcE.2.1] at p2
  rw [octDot_inComplex (jordan y y).o02 E.o02 hcsq.2.1 hcE.2.1, Z02re, Z02im] at q2
  have hdet02 : (complexPart y.o02).re * ((complexPart y.o02).im * (y.d0 + y.d2)) -
      (complexPart y.o02).im *
        ((complexPart y.o02).re * (y.d0 + y.d2) + a * b) ≠ 0 := by
    have he : (complexPart y.o02).re * ((complexPart y.o02).im * (y.d0 + y.d2)) -
        (complexPart y.o02).im *
          ((complexPart y.o02).re * (y.d0 + y.d2) + a * b) =
        -((complexPart y.o02).im * (a * b)) := by ring
    rw [he]
    simp only [ne_eq, neg_eq_zero]
    exact mul_ne_zero hsigma (mul_ne_zero (ne_of_gt hapos) (ne_of_gt hbpos))
  obtain ⟨r02, i02⟩ := two_by_two (complexPart y.o02).re (complexPart y.o02).im
    ((complexPart y.o02).re * (y.d0 + y.d2) + a * b)
    ((complexPart y.o02).im * (y.d0 + y.d2))
    (complexPart E.o02).re (complexPart E.o02).im p2 q2 hdet02
  -- slot 12
  rw [octDot_inComplex y.o12 E.o12 hcy.2.2 hcE.2.2, hwb,
    Complex.ofReal_re, Complex.ofReal_im] at p3
  rw [octDot_inComplex (jordan y y).o12 E.o12 hcsq.2.2 hcE.2.2, Z12re, Z12im] at q3
  have hdet12 : b * (a * (complexPart y.o02).im) -
      0 * (b * (y.d1 + y.d2) + a * (complexPart y.o02).re) ≠ 0 := by
    simp only [zero_mul, sub_zero]
    exact mul_ne_zero (ne_of_gt hbpos) (mul_ne_zero (ne_of_gt hapos) hsigma)
  obtain ⟨r12, i12⟩ := two_by_two b 0
    (b * (y.d1 + y.d2) + a * (complexPart y.o02).re) (a * (complexPart y.o02).im)
    (complexPart E.o12).re (complexPart E.o12).im p3 q3 hdet12
  refine Albert.ext ?_ ?_ ?_ ?_ ?_ ?_
  · show E.d0 = (0 : Albert).d0
    rw [hE0]; rfl
  · show E.d1 = (0 : Albert).d1
    rw [hE1]; rfl
  · show E.d2 = (0 : Albert).d2
    rw [hE2]; rfl
  · exact octInComplex_eq_zero E.o01 hcE.1 r01 i01
  · exact octInComplex_eq_zero E.o02 hcE.2.1 r02 i02
  · exact octInComplex_eq_zero E.o12 hcE.2.2 r12 i12

/-! ## 9. The Gram matrix and the real part of the hidden determinant, from the sector data

This is `gram_phase_of_projections` (`FixedPairHidden.lean`) with the numerals removed and one
new ingredient: the exact-ledger version assumed `complexProjection (encoder r) = 0`, an exact-ledger
fact, so it had NO cross term. Nearby the sector part is small but nonzero and the cross term
must be handled -- abstractly, by trace associativity, never by a coordinate expansion. -/

/-- The sector/hidden cross term has no sector part. Three lines from
`complexProjection_zero_of_perp` (`SectorSubspace.lean`) and `inner_jordan_associative`
(`Native/AlgebraLaws.lean`).

`inner_jordan_associative` reads `inner (jordan x y) z = inner x (jordan y z)`;
the calculation uses its symmetric form. -/
theorem sector_hidden_cross_perp (x : Albert) (M : Matrix (Fin 3) (Fin 3) ℂ) :
    complexProjection (jordan (complexProjection x) (hiddenAlbert M)) = 0 := by
  apply complexProjection_zero_of_perp
  intro v hv
  have hvs : InComplexSector v := (complexSector_mem_iff v).mp hv
  have hxs : InComplexSector (complexProjection x) :=
    (complexSector_mem_iff _).mp (complexProjection_mem x)
  calc inner v (jordan (complexProjection x) (hiddenAlbert M))
      = inner (jordan v (complexProjection x)) (hiddenAlbert M) :=
        (inner_jordan_associative v (complexProjection x) (hiddenAlbert M)).symm
    _ = 0 := by
        rw [← complexProjection_eq_self _
          (complexSector_jordan v (complexProjection x) hvs hxs)]
        exact complex_hidden_orthogonal _ M

theorem complexProjection_hiddenAlbert (M : Matrix (Fin 3) (Fin 3) ℂ) :
    complexProjection (hiddenAlbert M) = 0 := by
  have h := complex_hidden_decomposition (hiddenAlbert M)
  rw [hiddenMatrix_hiddenAlbert] at h
  exact add_right_cancel (h.trans (zero_add (hiddenAlbert M)).symm)

theorem inner_sector_hiddenAlbert (v : Albert) (hv : InComplexSector v)
    (M : Matrix (Fin 3) (Fin 3) ℂ) : inner v (hiddenAlbert M) = 0 := by
  rw [← complexProjection_eq_self v hv]
  exact complex_hidden_orthogonal v M

/-- The pure-algebra half of the sector/hidden square expansion, stated on `S + H` so that no
`rw` ever has to touch the right-hand side.

The right-hand side is written in the EXACT associativity that the four rewrites produce, with
the cross term appearing twice rather than as `(2:ℝ) • jordan S H`, so that the proof is the four
rewrites and nothing else -- `rw` closes the goal by `rfl`. -/
theorem jordan_add_self_split (S H : Albert) :
    jordan (S + H) (S + H) =
      jordan S S + jordan S H + (jordan S H + jordan H H) := by
  rw [jordan_add_left, jordan_add_right, jordan_add_right, jordan_comm H S]

/-- The sector part of a square splits, with no cross term. -/
theorem complexProjection_square_split (z : Albert) :
    complexProjection (jordan z z) =
      jordan (complexProjection z) (complexProjection z) +
        complexProjection (jordan (hiddenAlbert (hiddenMatrix z))
          (hiddenAlbert (hiddenMatrix z))) := by
  have hsec : InComplexSector (complexProjection z) :=
    (complexSector_mem_iff _).mp (complexProjection_mem z)
  have hcross : complexProjection
      (jordan (hiddenAlbert (hiddenMatrix z)) (complexProjection z)) = 0 := by
    rw [jordan_comm]
    exact sector_hidden_cross_perp z (hiddenMatrix z)
  conv_lhs => rw [← complex_hidden_decomposition z]
  rw [jordan_add_left, jordan_add_right, jordan_add_right,
    complexProjection_add, complexProjection_add, complexProjection_add,
    complexProjection_eq_self _ (complexSector_jordan _ _ hsec hsec),
    sector_hidden_cross_perp z (hiddenMatrix z), hcross, add_zero, zero_add]

/-- Equal sector data force an equal hidden Gram matrix. `hidden_square_complexProjection`
(`Sector.lean`) reads `M^H M` off the sector part of the hidden square entry by entry,
and is fully general in `M`.

The off-diagonal extraction uses the three slot readers from section 5a:
`simpa only [complexPart_complexAlbert_o01]` produces `-G 0 1 = -G' 0 1`,
and `neg_inj` removes the negatives; the other slots use their corresponding readers.
The diagonal probes use `simp only [complexAlbert]` to unfold the constructor.

`Affine20.fin3_cases` (`Relabel.lean`) with `rcases ... with rfl | rfl | rfl`
keeps literal indices matching hypotheses stated at `0`, `1`, and `2`. -/
theorem gram_eq_of_sector_data (z z' : Albert)
    (hS : complexProjection z = complexProjection z')
    (hT : complexProjection (jordan z z) = complexProjection (jordan z' z')) :
    sectorColumnGram (hiddenMatrix z) = sectorColumnGram (hiddenMatrix z') := by
  have hcore : complexProjection (jordan (hiddenAlbert (hiddenMatrix z))
        (hiddenAlbert (hiddenMatrix z))) =
      complexProjection (jordan (hiddenAlbert (hiddenMatrix z'))
        (hiddenAlbert (hiddenMatrix z'))) := by
    have h := complexProjection_square_split z
    have h' := complexProjection_square_split z'
    rw [hS, hT] at h
    exact add_left_cancel (h.symm.trans h')
  rw [hidden_square_complexProjection, hidden_square_complexProjection] at hcore
  have hherm : (sectorColumnGram (hiddenMatrix z)).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_self (hiddenMatrix z)
  have hherm' : (sectorColumnGram (hiddenMatrix z')).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_self (hiddenMatrix z')
  have hS0 := congrArg Albert.d0 hcore
  have hS1 := congrArg Albert.d1 hcore
  have hS2 := congrArg Albert.d2 hcore
  have h01 := congrArg (fun x : Albert => complexPart x.o01) hcore
  have h02 := congrArg (fun x : Albert => complexPart x.o02) hcore
  have h12 := congrArg (fun x : Albert => complexPart x.o12) hcore
  simp only [complexAlbert] at hS0 hS1 hS2
  -- Read the three off-diagonal entries using the matching slot readers from section 5a.
  -- For example, `complexPart_complexAlbert_o01` reduces the `o01` complex part.
  -- Each intermediate equality retains the negation on both Gram-matrix entries.
  -- `neg_inj` then removes those negations.
  
  
  -- Each `simp only` uses one reader, so it cannot itself cancel the negation:
  -- `neg_inj` belongs to the default simp set, which is not in play.
  have hg01 : sectorColumnGram (hiddenMatrix z) 0 1 =
      sectorColumnGram (hiddenMatrix z') 0 1 := by
    have h : -sectorColumnGram (hiddenMatrix z) 0 1 =
        -sectorColumnGram (hiddenMatrix z') 0 1 := by
      simpa only [complexPart_complexAlbert_o01] using h01
    exact neg_inj.mp h
  have hg02 : sectorColumnGram (hiddenMatrix z) 0 2 =
      sectorColumnGram (hiddenMatrix z') 0 2 := by
    have h : -sectorColumnGram (hiddenMatrix z) 0 2 =
        -sectorColumnGram (hiddenMatrix z') 0 2 := by
      simpa only [complexPart_complexAlbert_o02] using h02
    exact neg_inj.mp h
  have hg12 : sectorColumnGram (hiddenMatrix z) 1 2 =
      sectorColumnGram (hiddenMatrix z') 1 2 := by
    have h : -sectorColumnGram (hiddenMatrix z) 1 2 =
        -sectorColumnGram (hiddenMatrix z') 1 2 := by
      simpa only [complexPart_complexAlbert_o12] using h12
    exact neg_inj.mp h
  -- the three diagonal entries, through the Frobenius trace
  have hFroDiag : ∀ M : Matrix (Fin 3) (Fin 3) ℂ,
      (sectorColumnGram M 0 0).re + (sectorColumnGram M 1 1).re +
        (sectorColumnGram M 2 2).re = sectorFrobeniusSq M := by
    intro M
    simp [sectorColumnGram, sectorFrobeniusSq, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_three, Complex.normSq_apply, Complex.mul_re, Complex.star_def,
      Complex.conj_re, Complex.conj_im]
    ring
  have hFro : sectorFrobeniusSq (hiddenMatrix z) = sectorFrobeniusSq (hiddenMatrix z') := by
    have t0 := hFroDiag (hiddenMatrix z)
    have t1 := hFroDiag (hiddenMatrix z')
    linarith [hS0, hS1, hS2, t0, t1]
  have hdiagIm : ∀ (M : Matrix (Fin 3) (Fin 3) ℂ),
      (sectorColumnGram M).IsHermitian → ∀ i : Fin 3, (sectorColumnGram M i i).im = 0 := by
    intro M hM i
    have h := congrArg Complex.im (hM.apply i i)
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  have hd0 : sectorColumnGram (hiddenMatrix z) 0 0 =
      sectorColumnGram (hiddenMatrix z') 0 0 := by
    apply Complex.ext
    · linarith [hS0, hFro]
    · rw [hdiagIm _ hherm 0, hdiagIm _ hherm' 0]
  have hd1 : sectorColumnGram (hiddenMatrix z) 1 1 =
      sectorColumnGram (hiddenMatrix z') 1 1 := by
    apply Complex.ext
    · linarith [hS1, hFro]
    · rw [hdiagIm _ hherm 1, hdiagIm _ hherm' 1]
  have hd2 : sectorColumnGram (hiddenMatrix z) 2 2 =
      sectorColumnGram (hiddenMatrix z') 2 2 := by
    apply Complex.ext
    · linarith [hS2, hFro]
    · rw [hdiagIm _ hherm 2, hdiagIm _ hherm' 2]
  have hg10 : sectorColumnGram (hiddenMatrix z) 1 0 =
      sectorColumnGram (hiddenMatrix z') 1 0 := by
    rw [← hherm.apply 1 0, ← hherm'.apply 1 0, hg01]
  have hg20 : sectorColumnGram (hiddenMatrix z) 2 0 =
      sectorColumnGram (hiddenMatrix z') 2 0 := by
    rw [← hherm.apply 2 0, ← hherm'.apply 2 0, hg02]
  have hg21 : sectorColumnGram (hiddenMatrix z) 2 1 =
      sectorColumnGram (hiddenMatrix z') 2 1 := by
    rw [← hherm.apply 2 1, ← hherm'.apply 2 1, hg12]
  ext i j
  rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases j with rfl | rfl | rfl
  · exact hd0
  · exact hg01
  · exact hg02
  · exact hg10
  · exact hd1
  · exact hg12
  · exact hg20
  · exact hg21
  · exact hd2

/-- Newton's cube term, split along a sector/hidden decomposition. Stated on `S + H` with the
three cross-term facts as hypotheses, so that the caller can fold `S + H` back to `z` with one
`rw [hdec]` and no rewrite ever reaches a right-hand side. -/
theorem cubic_trace_split (S H : Albert)
    (hc1 : inner S (jordan S H) = 0)
    (hc2 : inner H (jordan S S) = 0)
    (hc3 : inner H (jordan S H) = inner S (jordan H H)) :
    inner (S + H) (jordan (S + H) (S + H)) =
      inner S (jordan S S) + 3 * inner S (jordan H H) + inner H (jordan H H) := by
  rw [jordan_add_self_split]
  simp only [inner_add_left, inner_add_right, hc1, hc2, hc3]
  ring

/-- Equal sector data and equal cubic norms force equal `(det M).re`. `newtonCubicNorm` is
Newton's trace form (`Theorems/CubicNorm.lean`), so this is trace algebra over
`inner_jordan_associative`, `complex_hidden_orthogonal`, `hiddenAlbert_norm` and
`hiddenAlbert_cubicNorm` -- no 27-coordinate expansion anywhere.

The terms `ht1`, `hmix` and `hcubic` go forward on `S + H` and fold back with
`rw [hdec] at h`, whose pattern is `S + H` and therefore cannot reach
`complexProjection z` or `hiddenMatrix z`. -/
theorem newtonCubicNorm_sector_split (z : Albert) :
    newtonCubicNorm z =
      ((trace (complexProjection z)) ^ 3
        - 3 * trace (complexProjection z) * trace (complexProjection (jordan z z))
        + 2 * (3 * inner (complexProjection z) (complexProjection (jordan z z))
              - 2 * inner (complexProjection z)
                  (jordan (complexProjection z) (complexProjection z))
              + 6 * (hiddenMatrix z).det.re)) / 6 := by
  have hdec : complexProjection z + hiddenAlbert (hiddenMatrix z) = z :=
    complex_hidden_decomposition z
  have hsec : InComplexSector (complexProjection z) :=
    (complexSector_mem_iff _).mp (complexProjection_mem z)
  have hHtr : trace (hiddenAlbert (hiddenMatrix z)) = 0 := by simp [hiddenAlbert, trace]
  -- the three cross terms
  have hc1 : inner (complexProjection z)
      (jordan (complexProjection z) (hiddenAlbert (hiddenMatrix z))) = 0 := by
    rw [← inner_jordan_associative]
    exact inner_sector_hiddenAlbert _
      (complexSector_jordan _ _ hsec hsec) (hiddenMatrix z)
  have hc2 : inner (hiddenAlbert (hiddenMatrix z))
      (jordan (complexProjection z) (complexProjection z)) = 0 := by
    rw [inner_comm]
    exact inner_sector_hiddenAlbert _
      (complexSector_jordan _ _ hsec hsec) (hiddenMatrix z)
  have hc3 : inner (hiddenAlbert (hiddenMatrix z))
      (jordan (complexProjection z) (hiddenAlbert (hiddenMatrix z))) =
      inner (complexProjection z)
        (jordan (hiddenAlbert (hiddenMatrix z)) (hiddenAlbert (hiddenMatrix z))) := by
    rw [inner_comm (hiddenAlbert (hiddenMatrix z))
      (jordan (complexProjection z) (hiddenAlbert (hiddenMatrix z))),
      inner_jordan_associative]
  -- trace of z and of its square, both folded back from `S + H`
  have ht1 : trace z = trace (complexProjection z) := by
    have h : trace (complexProjection z + hiddenAlbert (hiddenMatrix z)) =
        trace (complexProjection z) + trace (hiddenAlbert (hiddenMatrix z)) := trace_add _ _
    rw [hdec, hHtr, add_zero] at h
    exact h
  have hHtr2 : trace (hiddenAlbert (hiddenMatrix (jordan z z))) = 0 := by
    simp [hiddenAlbert, trace]
  have ht2 : trace (jordan z z) = trace (complexProjection (jordan z z)) := by
    have h : trace (complexProjection (jordan z z) +
        hiddenAlbert (hiddenMatrix (jordan z z))) =
        trace (complexProjection (jordan z z)) +
          trace (hiddenAlbert (hiddenMatrix (jordan z z))) := trace_add _ _
    rw [complex_hidden_decomposition (jordan z z), hHtr2, add_zero] at h
    exact h
  -- the hidden cube
  have hcube : inner (hiddenAlbert (hiddenMatrix z))
      (jordan (hiddenAlbert (hiddenMatrix z)) (hiddenAlbert (hiddenMatrix z))) =
      6 * (hiddenMatrix z).det.re := by
    have h := hiddenAlbert_cubicNorm (hiddenMatrix z)
    rw [newtonCubicNorm, hHtr] at h
    have hi : trace (jordan (hiddenAlbert (hiddenMatrix z))
        (jordan (hiddenAlbert (hiddenMatrix z)) (hiddenAlbert (hiddenMatrix z)))) =
        inner (hiddenAlbert (hiddenMatrix z))
          (jordan (hiddenAlbert (hiddenMatrix z)) (hiddenAlbert (hiddenMatrix z))) := rfl
    rw [hi] at h
    linarith [h]
  -- the mixed term, as sector data
  have hmix : inner (complexProjection z)
      (jordan (hiddenAlbert (hiddenMatrix z)) (hiddenAlbert (hiddenMatrix z))) =
      inner (complexProjection z) (complexProjection (jordan z z)) -
        inner (complexProjection z) (jordan (complexProjection z) (complexProjection z)) := by
    have hSX : inner (complexProjection z) (jordan z z) =
        inner (complexProjection z) (complexProjection (jordan z z)) :=
      inner_sector_complexProjection _ _ hsec
    have hexp : inner (complexProjection z)
        (jordan (complexProjection z + hiddenAlbert (hiddenMatrix z))
          (complexProjection z + hiddenAlbert (hiddenMatrix z))) =
        inner (complexProjection z) (jordan (complexProjection z) (complexProjection z)) +
          inner (complexProjection z)
            (jordan (hiddenAlbert (hiddenMatrix z)) (hiddenAlbert (hiddenMatrix z))) := by
      rw [jordan_add_self_split]
      simp only [inner_add_right, hc1]
      ring
    rw [hdec] at hexp
    linarith [hSX, hexp]
  -- Newton's cube term, folded back from `S + H`
  have hcubic : trace (jordan z (jordan z z)) =
      inner (complexProjection z) (jordan (complexProjection z) (complexProjection z)) +
        3 * inner (complexProjection z)
          (jordan (hiddenAlbert (hiddenMatrix z)) (hiddenAlbert (hiddenMatrix z))) +
        6 * (hiddenMatrix z).det.re := by
    have h := cubic_trace_split (complexProjection z) (hiddenAlbert (hiddenMatrix z))
      hc1 hc2 hc3
    rw [hdec, hcube] at h
    exact h
  rw [newtonCubicNorm, ht1, ht2, hcubic, hmix]
  ring

theorem det_re_eq_of_sector_data (z z' : Albert)
    (hS : complexProjection z = complexProjection z')
    (hT : complexProjection (jordan z z) = complexProjection (jordan z' z'))
    (hcub : newtonCubicNorm z = newtonCubicNorm z') :
    (hiddenMatrix z).det.re = (hiddenMatrix z').det.re := by
  rw [newtonCubicNorm_sector_split z, newtonCubicNorm_sector_split z', hS, hT] at hcub
  linarith [hcub]

/-! ## 10. The colour SU(3) transport, with the exact Gram removed

`scaled_transport` (`FixedPairNormalization.lean`) builds the explicit left inverse
`A := 3 * M^H` out of `M^H M = diag(1/3)`. The argument needs only SOME left inverse, so
`A := G^{-1} M^H` with `G := M^H M` invertible does the same work and names no value. It is
`private` there, so it has to be re-proved in any case. -/

theorem su3_transport_general (M N : Matrix (Fin 3) (Fin 3) ℂ)
    (hG : sectorColumnGram M = sectorColumnGram N)
    (hUnit : IsUnit (sectorColumnGram M).det)
    (hdet : N.det = M.det) :
    ∃ s : SectorUnitary, (s : SectorMatrix).det = 1 ∧ (s : SectorMatrix) * M = N := by
  have hGdef : sectorColumnGram M = M.conjTranspose * M := rfl
  have hGdef' : sectorColumnGram N = N.conjTranspose * N := rfl
  have hAM : ((sectorColumnGram M)⁻¹ * M.conjTranspose) * M = 1 := by
    rw [Matrix.mul_assoc, ← hGdef, Matrix.nonsing_inv_mul _ hUnit]
  have hMA : M * ((sectorColumnGram M)⁻¹ * M.conjTranspose) = 1 := mul_eq_one_comm.mp hAM
  have hUnitary :
      (N * ((sectorColumnGram M)⁻¹ * M.conjTranspose)).conjTranspose *
        (N * ((sectorColumnGram M)⁻¹ * M.conjTranspose)) = 1 := by
    have hstep :
        ((sectorColumnGram M)⁻¹ * M.conjTranspose).conjTranspose * (N.conjTranspose * N) *
            ((sectorColumnGram M)⁻¹ * M.conjTranspose) =
          (M * ((sectorColumnGram M)⁻¹ * M.conjTranspose)).conjTranspose *
            (M * ((sectorColumnGram M)⁻¹ * M.conjTranspose)) := by
      rw [← hGdef', ← hG, hGdef]
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc N.conjTranspose N ((sectorColumnGram M)⁻¹ * M.conjTranspose),
      ← Matrix.mul_assoc, hstep, hMA, Matrix.conjTranspose_one, Matrix.one_mul]
  refine ⟨⟨N * ((sectorColumnGram M)⁻¹ * M.conjTranspose),
    Matrix.mem_unitaryGroup_iff'.mpr hUnitary⟩, ?_, ?_⟩
  · change (N * ((sectorColumnGram M)⁻¹ * M.conjTranspose)).det = 1
    rw [Matrix.det_mul, hdet, ← Matrix.det_mul, hMA, Matrix.det_one]
  · change N * ((sectorColumnGram M)⁻¹ * M.conjTranspose) * M = N
    rw [Matrix.mul_assoc, hAM, Matrix.mul_one]

/-- The colour SU(3) automorphism fixes the sector pointwise and multiplies the hidden matrix on
the left. `sectorLeftSU3_fixes_complex` (`SectorLeftAction.lean`) fixes EVERY sector element,
not just the flat pair, so no analogue of that file's `fixes_original_pair` is needed -- which is
precisely what makes the perturbed pair harmless here. -/
theorem su3_maps_hiddenAlbert (s : SectorUnitary) (hs : (s : SectorMatrix).det = 1)
    (M : Matrix (Fin 3) (Fin 3) ℂ) :
    (sectorLeftSU3Automorphism s hs).equiv (hiddenAlbert M) =
      hiddenAlbert ((s : SectorMatrix) * M) := by
  have hc : complexProjection
      ((sectorLeftSU3Automorphism s hs).equiv (hiddenAlbert M)) = 0 := by
    apply complexProjection_zero_of_perp
    intro v hv
    have hvs : InComplexSector v := (complexSector_mem_iff v).mp hv
    have hfix : (sectorLeftSU3Automorphism s hs).equiv v = v :=
      sectorLeftSU3_fixes_complex s hs v hvs
    calc inner v ((sectorLeftSU3Automorphism s hs).equiv (hiddenAlbert M))
        = inner ((sectorLeftSU3Automorphism s hs).equiv v)
            ((sectorLeftSU3Automorphism s hs).equiv (hiddenAlbert M)) := by rw [hfix]
      _ = inner v (hiddenAlbert M) :=
          (sectorLeftSU3Automorphism s hs).inner_map v (hiddenAlbert M)
      _ = 0 := inner_sector_hiddenAlbert v hvs M
  have hm : hiddenMatrix ((sectorLeftSU3Automorphism s hs).equiv (hiddenAlbert M)) =
      (s : SectorMatrix) * M := by
    rw [sectorLeftSU3_hidden s hs, hiddenMatrix_hiddenAlbert]
  have hd := complex_hidden_decomposition
    ((sectorLeftSU3Automorphism s hs).equiv (hiddenAlbert M))
  rw [hc, hm, zero_add] at hd
  exact hd.symm

theorem su3_maps_sector_hidden (s : SectorUnitary) (hs : (s : SectorMatrix).det = 1)
    (z : Albert) :
    (sectorLeftSU3Automorphism s hs).equiv z =
      complexProjection z + hiddenAlbert ((s : SectorMatrix) * hiddenMatrix z) := by
  have hdec : complexProjection z + hiddenAlbert (hiddenMatrix z) = z :=
    complex_hidden_decomposition z
  have hfix : (sectorLeftSU3Automorphism s hs).equiv (complexProjection z) =
      complexProjection z :=
    sectorLeftSU3_fixes_complex s hs _ ((complexSector_mem_iff _).mp (complexProjection_mem z))
  conv_lhs => rw [← hdec]
  rw [map_add, hfix, su3_maps_hiddenAlbert s hs (hiddenMatrix z)]

/-! ## 11. The separator: Phi is a nonzero multiple of the hidden determinant's imaginary part

`phi_of_diagonal_complex` (`UnitShifts.lean`) holds for an
ARBITRARY third argument, with hypotheses `IsDiagonal x` and `InComplexSector y` -- exactly what
`native_ordered_positive_pair` delivers. At `x = flatXN = diag(1,0,-1)` the pair factor is
`2 * 1 * 1 * (-2) * (a*b*star v).im = 4*a*b*v.im`. Only `a*b*v.im /= 0` and "the same for both
candidates" are used downstream, so an overall sign error here would be harmless; it is spelled
out anyway. -/

theorem phi_normalized (y z : Albert) (a b : ℝ)
    (hcy : InComplexSector y) (h01 : y.o01 = octScalar a) (h12 : y.o12 = octScalar b) :
    phi flatXN y z =
      4 * a * b * (complexPart y.o02).im * (hiddenMatrix z).det.im := by
  have hdiag : IsDiagonal flatXN := by simp [IsDiagonal, flatXN]
  rw [phi_of_diagonal_complex flatXN y z hdiag hcy]
  have hd0 : flatXN.d0 = (1 : ℝ) := rfl
  have hd1 : flatXN.d1 = (0 : ℝ) := rfl
  have hd2 : flatXN.d2 = (-1 : ℝ) := rfl
  rw [hd0, hd1, hd2, h01, h12, complexPart_octScalar, complexPart_octScalar,
    real_real_conj_im]
  ring

/-! ## 12. Assembly

The open set is an epsilon box on the P block intersected with one half-space of Phi. It is open
by `FrameTopology.continuous_ledger54` and `Sections.continuous_phiOf` and by nothing else; in
particular no relabelling gate is used, and the two sign sheets are never merged. -/

def PBox : Set Triple :=
  {T : Triple | ∀ i j : Fin 3, |(ledger54 T).2.1 i j - 1 / 3| < 1 / 50}

theorem isOpen_PBox : IsOpen PBox := by
  have hcont : ∀ i j : Fin 3, Continuous fun T : Triple => (ledger54 T).2.1 i j := by
    intro i j
    have h2 : Continuous fun L : Ledger54 => L.2.1 i j :=
      (continuous_apply j).comp ((continuous_apply i).comp (continuous_fst.comp continuous_snd))
    simpa only [Function.comp_def] using h2.comp continuous_ledger54
  have hset : PBox =
      ⋂ r : Fin 3 × Fin 3,
        {T : Triple | |(ledger54 T).2.1 r.1 r.2 - 1 / 3| < 1 / 50} := by
    ext T
    simp only [PBox, Set.mem_setOf_eq, Set.mem_iInter, Prod.forall]
  rw [hset]
  refine isOpen_iInter_of_finite ?_
  intro r
  exact isOpen_lt (((hcont r.1 r.2).sub continuous_const).abs) continuous_const

/-- **The core.** Two nearby frame triples with the same ledger have Phi equal up to sign, and
are automorphism related as soon as the signs agree. No premise; the only shrink is the box. -/
theorem nearby_core (T S : Triple)
    (hT : ∀ a : Fin 3, Frame (T a)) (hS : ∀ a : Fin 3, Frame (S a))
    (hbox : T ∈ PBox) (hL : ledger54 T = ledger54 S) (hTne : phiOf T ≠ 0) :
    phiOf T ^ 2 = phiOf S ^ 2 ∧
      (phiOf T = phiOf S → ∃ k : CompactAutomorphism, mapAtoms k S = T) := by
  -- the two P blocks agree, and T's is in the box
  have hPeq : ∀ i j : Fin 3, inner (T 0 i) (T 1 j) = inner (S 0 i) (S 1 j) := fun i j =>
    congrArg (fun L : Ledger54 => L.2.1 i j) hL
  have hboxT : ∀ i j : Fin 3, |inner (T 0 i) (T 1 j) - 1 / 3| < 1 / 50 := hbox
  -- normalise both pairs onto a common normal form
  obtain ⟨g, g', a, b, hgp, hgp', hqq, hcy, h01, h12, hapos, hbpos, hsig⟩ :=
    nearby_pair_normalization (T 0) (T 1) (S 0) (S 1) (hT 0) (hT 1) (hS 0) (hS 1) hboxT hPeq
  have hQsame : (fun i => g.equiv (T 1 i)) = fun i => g'.equiv (S 1 i) := funext hqq
  have hQframe : Frame (fun i => g'.equiv (S 1 i)) := g'.map_frame (S 1) (hS 1)
  have hrTframe : Frame (fun k => g.equiv (T 2 k)) := g.map_frame (T 2) (hT 2)
  have hrSframe : Frame (fun k => g'.equiv (S 2 k)) := g'.map_frame (S 2) (hS 2)
  -- every atom of the common normalised second frame lies in the sector, because its encoder
  -- does (`frame_in_complexSector`, `Theorems/ComplexSectorSpan.lean`)
  have hQsec : ∀ j : Fin 3, InComplexSector ((fun i => g'.equiv (S 1 i)) j) := fun j =>
    (complexSector_mem_iff _).mp (frame_in_complexSector _ hQframe hcy j)
  -- STEP C: the ledger pins the sector data of the third frame, atom by atom
  have hatom : ∀ k : Fin 3,
      complexProjection (g.equiv (T 2 k)) = complexProjection (g'.equiv (S 2 k)) := by
    intro k
    have hEsec : InComplexSector
        (complexProjection (g.equiv (T 2 k) - g'.equiv (S 2 k))) :=
      (complexSector_mem_iff _).mp (complexProjection_mem _)
    -- R block gives the three diagonal entries
    have hR : ∀ i : Fin 3,
        inner (flatFrameP i) (g.equiv (T 2 k) - g'.equiv (S 2 k)) = 0 := by
      intro i
      have e1 : inner (flatFrameP i) (g.equiv (T 2 k)) = inner (T 0 i) (T 2 k) := by
        rw [← hgp i]
        exact g.inner_map (T 0 i) (T 2 k)
      have e2 : inner (flatFrameP i) (g'.equiv (S 2 k)) = inner (S 0 i) (S 2 k) := by
        rw [← hgp' i]
        exact g'.inner_map (S 0 i) (S 2 k)
      have hRL : inner (T 2 k) (T 0 i) = inner (S 2 k) (S 0 i) :=
        congrArg (fun L : Ledger54 => L.2.2.2 k i) hL
      rw [inner_sub_right, e1, e2, inner_comm (T 0 i) (T 2 k), inner_comm (S 0 i) (S 2 k), hRL]
      ring
    have hE0 : (complexProjection (g.equiv (T 2 k) - g'.equiv (S 2 k))).d0 = 0 := by
      have h := hR 2
      rw [inner_sector_complexProjection _ _ (flatFrameP_inComplexSector 2),
        inner_flatFrameP_two] at h
      exact h
    have hE1 : (complexProjection (g.equiv (T 2 k) - g'.equiv (S 2 k))).d1 = 0 := by
      have h := hR 1
      rw [inner_sector_complexProjection _ _ (flatFrameP_inComplexSector 1),
        inner_flatFrameP_one] at h
      exact h
    have hE2 : (complexProjection (g.equiv (T 2 k) - g'.equiv (S 2 k))).d2 = 0 := by
      have h := hR 0
      rw [inner_sector_complexProjection _ _ (flatFrameP_inComplexSector 0),
        inner_flatFrameP_zero] at h
      exact h
    -- C block gives the nine mixed probes
    have hC : ∀ i j : Fin 3,
        inner (jordan (flatFrameP i) ((fun i => g'.equiv (S 1 i)) j))
          (g.equiv (T 2 k) - g'.equiv (S 2 k)) = 0 := by
      intro i j
      have hCL : ledger (T 0) (T 1) (T 2) i j k = ledger (S 0) (S 1) (S 2) i j k :=
        congrArg (fun L : Ledger54 => L.1 i j k) hL
      have e1 : inner (jordan (flatFrameP i) ((fun i => g'.equiv (S 1 i)) j))
          (g.equiv (T 2 k)) = ledger (T 0) (T 1) (T 2) i j k := by
        rw [← hQsame, ← hgp i]
        show inner (jordan (g.equiv (T 0 i)) (g.equiv (T 1 j))) (g.equiv (T 2 k)) = _
        rw [← g.map_jordan (T 0 i) (T 1 j), g.inner_map]
        rfl
      have e2 : inner (jordan (flatFrameP i) ((fun i => g'.equiv (S 1 i)) j))
          (g'.equiv (S 2 k)) = ledger (S 0) (S 1) (S 2) i j k := by
        rw [← hgp' i]
        show inner (jordan (g'.equiv (S 0 i)) (g'.equiv (S 1 j))) (g'.equiv (S 2 k)) = _
        rw [← g'.map_jordan (S 0 i) (S 1 j), g'.inner_map]
        rfl
      rw [inner_sub_right, e1, e2, hCL]
      ring
    -- push onto the sector projection, then take the two j-combinations
    have hCE : ∀ i j : Fin 3,
        inner (jordan (flatFrameP i) ((fun i => g'.equiv (S 1 i)) j))
          (complexProjection (g.equiv (T 2 k) - g'.equiv (S 2 k))) = 0 := by
      intro i j
      rw [← inner_sector_complexProjection _ _
        (complexSector_jordan _ _ (flatFrameP_inComplexSector i) (hQsec j))]
      exact hC i j
    have hyc : ∀ i : Fin 3,
        inner (jordan (flatFrameP i) (encoder fun i => g'.equiv (S 1 i)))
          (complexProjection (g.equiv (T 2 k) - g'.equiv (S 2 k))) = 0 := by
      intro i
      have hdiff : (encoder fun i => g'.equiv (S 1 i)) =
          (fun i => g'.equiv (S 1 i)) 2 - (fun i => g'.equiv (S 1 i)) 0 := rfl
      rw [hdiff, jordan_sub_right, inner_sub_left, hCE i 2, hCE i 0]
      ring
    have hsqc : ∀ i : Fin 3,
        inner (jordan (flatFrameP i)
            (jordan (encoder fun i => g'.equiv (S 1 i))
              (encoder fun i => g'.equiv (S 1 i))))
          (complexProjection (g.equiv (T 2 k) - g'.equiv (S 2 k))) = 0 := by
      intro i
      rw [frame_encoder_square _ hQframe, jordan_add_right, inner_add_left, hCE i 2, hCE i 0]
      ring
    obtain ⟨p1, p2, p3⟩ :=
      slot_pairings_zero (encoder fun i => g'.equiv (S 1 i)) _ hE0 hE1 hE2
        (hyc 0) (hyc 1) (hyc 2)
    obtain ⟨q1, q2, q3⟩ :=
      slot_pairings_zero (jordan (encoder fun i => g'.equiv (S 1 i))
        (encoder fun i => g'.equiv (S 1 i))) _ hE0 hE1 hE2 (hsqc 0) (hsqc 1) (hsqc 2)
    have hzero : complexProjection (g.equiv (T 2 k) - g'.equiv (S 2 k)) = 0 :=
      sector_slot_recovery (encoder fun i => g'.equiv (S 1 i)) _ a b hcy hEsec h01 h12
        hapos hbpos hsig hE0 hE1 hE2 p1 p2 p3 q1 q2 q3
    rw [complexProjection_sub] at hzero
    exact sub_eq_zero.mp hzero
  -- the encoder-level sector data
  have hSigma : complexProjection (encoder fun k => g.equiv (T 2 k)) =
      complexProjection (encoder fun k => g'.equiv (S 2 k)) := by
    have hdT : (encoder fun k => g.equiv (T 2 k)) =
        g.equiv (T 2 2) - g.equiv (T 2 0) := rfl
    have hdS : (encoder fun k => g'.equiv (S 2 k)) =
        g'.equiv (S 2 2) - g'.equiv (S 2 0) := rfl
    rw [hdT, hdS, complexProjection_sub, complexProjection_sub, hatom 2, hatom 0]
  have hTheta : complexProjection (jordan (encoder fun k => g.equiv (T 2 k))
        (encoder fun k => g.equiv (T 2 k))) =
      complexProjection (jordan (encoder fun k => g'.equiv (S 2 k))
        (encoder fun k => g'.equiv (S 2 k))) := by
    rw [frame_encoder_square _ hrTframe, frame_encoder_square _ hrSframe,
      complexProjection_add, complexProjection_add, hatom 2, hatom 0]
  -- STEP D: Gram and the real part of the determinant agree
  have hGram : sectorColumnGram (hiddenMatrix (encoder fun k => g.equiv (T 2 k))) =
      sectorColumnGram (hiddenMatrix (encoder fun k => g'.equiv (S 2 k))) :=
    gram_eq_of_sector_data _ _ hSigma hTheta
  have hdetre : (hiddenMatrix (encoder fun k => g.equiv (T 2 k))).det.re =
      (hiddenMatrix (encoder fun k => g'.equiv (S 2 k))).det.re :=
    det_re_eq_of_sector_data _ _ hSigma hTheta
      (by rw [frame_encoder_cubicNorm _ hrTframe, frame_encoder_cubicNorm _ hrSframe])
  have hnorm : Complex.normSq (hiddenMatrix (encoder fun k => g.equiv (T 2 k))).det =
      Complex.normSq (hiddenMatrix (encoder fun k => g'.equiv (S 2 k))).det := by
    rw [normSq_det_eq_gram_det_re, normSq_det_eq_gram_det_re]
    have hc : ∀ M : Matrix (Fin 3) (Fin 3) ℂ,
        M.conjTranspose * M = sectorColumnGram M := fun _ => rfl
    rw [hc, hc, hGram]
  have hdetim : (hiddenMatrix (encoder fun k => g.equiv (T 2 k))).det.im ^ 2 =
      (hiddenMatrix (encoder fun k => g'.equiv (S 2 k))).det.im ^ 2 :=
    im_sq_eq_of_normSq_eq _ _ hnorm hdetre
  -- Phi at normalised position
  have hcoef : 4 * a * b * (complexPart (encoder fun i => g'.equiv (S 1 i)).o02).im ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨⟨⟨by norm_num, ne_of_gt hapos⟩, ne_of_gt hbpos⟩, hsig⟩
  have hphiT : phiOf T = 4 * a * b *
      (complexPart (encoder fun i => g'.equiv (S 1 i)).o02).im *
      (hiddenMatrix (encoder fun k => g.equiv (T 2 k))).det.im := by
    have hinv : phiOf T =
        phi flatXN (encoder fun i => g'.equiv (S 1 i)) (encoder fun k => g.equiv (T 2 k)) := by
      rw [phiOf_apply]
      calc phi (encoder (T 0)) (encoder (T 1)) (encoder (T 2))
          = phi (g.equiv (encoder (T 0))) (g.equiv (encoder (T 1)))
              (g.equiv (encoder (T 2))) := (g.phi_map _ _ _).symm
        _ = phi flatXN (encoder fun i => g'.equiv (S 1 i))
              (encoder fun k => g.equiv (T 2 k)) := by
            rw [← g.encoder_map (T 0), ← g.encoder_map (T 1), ← g.encoder_map (T 2),
              congrArg encoder (funext hgp), flatFrameP_encoder, hQsame]
    rw [hinv, phi_normalized _ _ a b hcy h01 h12]
  have hphiS : phiOf S = 4 * a * b *
      (complexPart (encoder fun i => g'.equiv (S 1 i)).o02).im *
      (hiddenMatrix (encoder fun k => g'.equiv (S 2 k))).det.im := by
    have hinv : phiOf S =
        phi flatXN (encoder fun i => g'.equiv (S 1 i)) (encoder fun k => g'.equiv (S 2 k)) := by
      rw [phiOf_apply]
      calc phi (encoder (S 0)) (encoder (S 1)) (encoder (S 2))
          = phi (g'.equiv (encoder (S 0))) (g'.equiv (encoder (S 1)))
              (g'.equiv (encoder (S 2))) := (g'.phi_map _ _ _).symm
        _ = phi flatXN (encoder fun i => g'.equiv (S 1 i))
              (encoder fun k => g'.equiv (S 2 k)) := by
            rw [← g'.encoder_map (S 0), ← g'.encoder_map (S 1), ← g'.encoder_map (S 2),
              congrArg encoder (funext hgp'), flatFrameP_encoder]
    rw [hinv, phi_normalized _ _ a b hcy h01 h12]
  refine ⟨?_, ?_⟩
  · rw [hphiT, hphiS]
    exact mul_sq_eq_of_sq_eq _ _ _ hdetim
  · intro hsame
    rw [hphiT, hphiS] at hsame
    have him : (hiddenMatrix (encoder fun k => g.equiv (T 2 k))).det.im =
        (hiddenMatrix (encoder fun k => g'.equiv (S 2 k))).det.im :=
      mul_left_cancel₀ hcoef hsame
    have hdeteq : (hiddenMatrix (encoder fun k => g.equiv (T 2 k))).det =
        (hiddenMatrix (encoder fun k => g'.equiv (S 2 k))).det := Complex.ext hdetre him
    -- nonvanishing determinant, from Phi alone
    have hdetne : (hiddenMatrix (encoder fun k => g.equiv (T 2 k))).det ≠ 0 := by
      intro h
      have himz : (hiddenMatrix (encoder fun k => g.equiv (T 2 k))).det.im = 0 := by
        rw [h]; rfl
      rw [hphiT, himz, mul_zero] at hTne
      exact hTne rfl
    have hUnit : IsUnit (sectorColumnGram
        (hiddenMatrix (encoder fun k => g.equiv (T 2 k)))).det := by
      refine isUnit_iff_ne_zero.mpr ?_
      -- `rw` closes with `with_reducible rfl`, which will NOT unfold the plain `def`
      -- `sectorColumnGram`; so the unfolding is supplied as an explicit term-mode `rfl`
      -- equation and rewritten in, leaving the two sides syntactically identical.
      have hgdef : ∀ M : Matrix (Fin 3) (Fin 3) ℂ,
          sectorColumnGram M = M.conjTranspose * M := fun _ => rfl
      have hreal : (sectorColumnGram
          (hiddenMatrix (encoder fun k => g.equiv (T 2 k)))).det.re =
          Complex.normSq (hiddenMatrix (encoder fun k => g.equiv (T 2 k))).det := by
        rw [hgdef, normSq_det_eq_gram_det_re]
      intro hz
      rw [hz] at hreal
      have hzz : Complex.normSq
          (hiddenMatrix (encoder fun k => g.equiv (T 2 k))).det = 0 := by
        rw [← hreal]; rfl
      exact hdetne (Complex.normSq_eq_zero.mp hzz)
    obtain ⟨s, hs, hsM⟩ :=
      su3_transport_general (hiddenMatrix (encoder fun k => g.equiv (T 2 k)))
        (hiddenMatrix (encoder fun k => g'.equiv (S 2 k))) hGram hUnit hdeteq.symm
    -- transport the third encoder, then the three atoms
    have hmap : (sectorLeftSU3Automorphism s hs).equiv
        (encoder fun k => g.equiv (T 2 k)) = encoder fun k => g'.equiv (S 2 k) := by
      rw [su3_maps_sector_hidden s hs, hsM, hSigma]
      exact complex_hidden_decomposition _
    have hatoms : ∀ k : Fin 3,
        (sectorLeftSU3Automorphism s hs).equiv (g.equiv (T 2 k)) = g'.equiv (S 2 k) :=
      frame_eq_of_encoder_eq _ _ hrTframe hrSframe (sectorLeftSU3Automorphism s hs) hmap
    -- the full triple, slot by slot
    have hT0 : ∀ i : Fin 3,
        ((sectorLeftSU3Automorphism s hs).comp g).equiv (T 0 i) = g'.equiv (S 0 i) := by
      intro i
      rw [CompactAutomorphism.comp_apply, hgp i, hgp' i]
      exact sectorLeftSU3_fixes_complex s hs _ (flatFrameP_inComplexSector i)
    have hT1 : ∀ i : Fin 3,
        ((sectorLeftSU3Automorphism s hs).comp g).equiv (T 1 i) = g'.equiv (S 1 i) := by
      intro i
      rw [CompactAutomorphism.comp_apply, hqq i]
      exact sectorLeftSU3_fixes_complex s hs _ (hQsec i)
    have hT2 : ∀ i : Fin 3,
        ((sectorLeftSU3Automorphism s hs).comp g).equiv (T 2 i) = g'.equiv (S 2 i) := by
      intro i
      rw [CompactAutomorphism.comp_apply]
      exact hatoms i
    have hKT : ∀ c i : Fin 3,
        (g'.symm.comp ((sectorLeftSU3Automorphism s hs).comp g)).equiv (T c i) = S c i := by
      intro c i
      rw [CompactAutomorphism.comp_apply]
      rcases fin3_cases c with rfl | rfl | rfl
      · rw [hT0 i]; exact g'.equiv.symm_apply_apply (S 0 i)
      · rw [hT1 i]; exact g'.equiv.symm_apply_apply (S 1 i)
      · rw [hT2 i]; exact g'.equiv.symm_apply_apply (S 2 i)
    refine ⟨(g'.symm.comp ((sectorLeftSU3Automorphism s hs).comp g)).symm, ?_⟩
    funext c i
    show (g'.symm.comp ((sectorLeftSU3Automorphism s hs).comp g)).equiv.symm (S c i) = T c i
    rw [← hKT c i]
    exact (g'.symm.comp ((sectorLeftSU3Automorphism s hs).comp g)).equiv.symm_apply_apply (T c i)

/-! ### The two endpoints -/

theorem flat_pair_overlap (i j : Fin 3) : inner (flatFrameP i) (flatFrameQ j) = 1 / 3 :=
  uniformLedger_pair_overlap flatFrameP flatFrameQ flatFrameR flatFrameR_frame flat_uniform i j

theorem flatBaseTriple_mem_PBox : flatBaseTriple ∈ PBox := by
  intro i j
  have h : (ledger54 flatBaseTriple).2.1 i j = 1 / 3 := flat_pair_overlap i j
  rw [h]; norm_num

theorem flatBaseRev3_mem_PBox : flatBaseRev3 ∈ PBox := by
  intro i j
  have h : (ledger54 flatBaseRev3).2.1 i j = 1 / 3 := flat_pair_overlap i j
  rw [h]; norm_num

/-- **`LocalOrbitCompleteness` at the original flat ordered triple, with no premise.** -/
theorem localOrbitCompleteness_flatBaseTriple :
    LocalOrbitCompleteness flatBaseTriple := by
  refine ⟨PBox ∩ {T : Triple | phiOf T < 0},
    isOpen_PBox.inter (isOpen_lt continuous_phiOf continuous_const),
    ⟨flatBaseTriple_mem_PBox, phiOf_flatBaseTriple_neg⟩, ?_⟩
  intro T S hT hS hTU hSU hL
  obtain ⟨hsq, himp⟩ := nearby_core T S hT hS hTU.1 hL (ne_of_lt hTU.2)
  refine himp ?_
  have h1 : phiOf T < 0 := hTU.2
  have h2 : phiOf S < 0 := hSU.2
  have hprod : (phiOf T - phiOf S) * (phiOf T + phiOf S) = 0 := by linarith [hsq]
  rcases mul_eq_zero.mp hprod with h | h
  · linarith
  · linarith

/-- **`LocalOrbitCompleteness` at the third-frame reversal, with no premise.** -/
theorem localOrbitCompleteness_flatBaseRev3 :
    LocalOrbitCompleteness flatBaseRev3 := by
  refine ⟨PBox ∩ {T : Triple | 0 < phiOf T},
    isOpen_PBox.inter (isOpen_lt continuous_const continuous_phiOf),
    ⟨flatBaseRev3_mem_PBox, phiOf_flatBaseRev3_pos⟩, ?_⟩
  intro T S hT hS hTU hSU hL
  obtain ⟨hsq, himp⟩ := nearby_core T S hT hS hTU.1 hL (ne_of_gt hTU.2)
  refine himp ?_
  have h1 : 0 < phiOf T := hTU.2
  have h2 : 0 < phiOf S := hSU.2
  have hprod : (phiOf T - phiOf S) * (phiOf T + phiOf S) = 0 := by linarith [hsq]
  rcases mul_eq_zero.mp hprod with h | h
  · linarith
  · linarith

/-- Both hypotheses of `NearbyOrbits.nearby_fibres_two_orbits`, discharged together. -/
theorem both_localOrbitCompleteness :
    LocalOrbitCompleteness flatBaseTriple ∧ LocalOrbitCompleteness flatBaseRev3 :=
  ⟨localOrbitCompleteness_flatBaseTriple, localOrbitCompleteness_flatBaseRev3⟩

end
end Glennie.Compact.PairNormNearby
