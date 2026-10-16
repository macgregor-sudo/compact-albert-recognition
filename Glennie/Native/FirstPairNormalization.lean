module

public import Glennie.Native.OrderedPositivePair
public import Glennie.Native.FixedPairNormalization

/- Arbitrary genuine first-pair normalization and the ordered base fibre.

Route. `native_ordered_positive_pair` puts the first frame onto the ORIGINAL ordered
flat frame `flatFrameP` and makes the second element's encoder slots 01 and 12
NONNEGATIVE reals with slot 02 in the actual complex sector. The nine p-q pair
overlaps then force every complex slot norm to 1/3, so the two nonnegative reals are
exactly `flatScale`, and the vanishing cubic norm forces the real part of slot 02 to
zero, leaving slot 02 at `±flatScale*i`. One constructed scalar-fixing octonion
automorphism flips `+i` to `-i` when needed, landing on the ORIGINAL `flatY1`
convention `(1, -i, 1)`. A frame equals its own projector frame, so the encoder
equality gives all three same-index atom equalities with no reversal disjunction:
nonnegativity of the two real slots is what pins the encoder's overall sign, since a
negated encoder would give slot 01 the value `-flatScale < 0`. Composing the fixed-pair third-frame normalizer then classifies the third frame as the original R or
its ordered reversal. -/

@[expose] public section
namespace Glennie.NativeFirstPairNormalization
open Glennie Glennie.Compact.FlatBase Glennie.Compact.Affine20
open Glennie.NativeOrderedPositivePair Glennie.NativeFixedPairNormalization
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Frames are their own projector frames -/

private theorem frame_as_projector (p : Fin 3 → Albert) (hp : Frame p) :
    p = projectorFrame (encoder p) := by
  funext i
  fin_cases i
  · exact (frame_projector_first p hp).symm
  · exact (frame_projector_middle p hp).symm
  · exact (frame_projector_last p hp).symm

/-- Matching encoders force all three same-index atom equalities. -/
private theorem frame_eq_of_encoder_eq (q s : Fin 3 → Albert) (hq : Frame q) (hs : Frame s)
    (m : CompactAutomorphism) (hEnc : m.equiv (encoder q) = encoder s) (i : Fin 3) :
    m.equiv (q i) = s i := by
  calc
    m.equiv (q i) = m.equiv (projectorFrame (encoder q) i) :=
        congrArg (fun x : Albert => m.equiv x) (congrFun (frame_as_projector q hq) i)
    _ = projectorFrame (m.equiv (encoder q)) i :=
        compactAutomorphism_projectorFrame m (encoder q) i
    _ = projectorFrame (encoder s) i := by rw [hEnc]
    _ = s i := congrFun (frame_as_projector s hs).symm i

/-! ## Scalar slots -/

private theorem complexPart_octScalar (a : ℝ) : complexPart (octScalar a) = (a : ℂ) := rfl

private theorem normSq_complexPart_octScalar (a : ℝ) :
    Complex.normSq (complexPart (octScalar a)) = a ^ 2 := by
  rw [complexPart_octScalar, Complex.normSq_ofReal]
  ring

private theorem real_real_conj_re (a b : ℝ) (v : ℂ) :
    ((a : ℂ) * (b : ℂ) * star v).re = a * b * v.re := by
  have hs : (star v).re = v.re := rfl
  have hi : (star v).im = -v.im := rfl
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hs, hi]
  ring

private theorem flatScale_pos : 0 < flatScale := by
  change 0 < 1 / Real.sqrt 3
  exact one_div_pos.mpr (Real.sqrt_pos.mpr (by norm_num))

/-- A nonnegative real with square 1/3 is exactly `flatScale`. No square-root API is
used: only `flatScale_sq` and positivity. -/
private theorem nonneg_sq_flatScale (a : ℝ) (ha : 0 ≤ a) (h : a ^ 2 = 1 / 3) :
    a = flatScale := by
  have hp : 0 < flatScale := flatScale_pos
  have hprod : (a - flatScale) * (a + flatScale) = 0 := by
    linear_combination h - flatScale_sq
  rcases mul_eq_zero.mp hprod with h1 | h2
  · linarith
  · linarith

/-! ## Saturation of the complex slots -/

/-- The three complex slot norms and the vanishing triangle real part, from the
diagonal and square data of a complex-sector element of cubic norm zero. -/
private theorem complex_slot_data_of_square (y : Albert) (hc : InComplexSector y)
    (h0 : y.d0 = 0) (h1 : y.d1 = 0) (h2 : y.d2 = 0)
    (hs0 : (jordan y y).d0 = 2/3) (hs1 : (jordan y y).d1 = 2/3)
    (hs2 : (jordan y y).d2 = 2/3) (hcub : newtonCubicNorm y = 0) :
    Complex.normSq (complexPart y.o01) = 1/3 ∧
      Complex.normSq (complexPart y.o02) = 1/3 ∧
      Complex.normSq (complexPart y.o12) = 1/3 ∧
      (complexPart y.o01 * complexPart y.o12 *
        star (complexPart y.o02)).re = 0 := by
  have hy : complexAlbert y.d0 y.d1 y.d2 (complexPart y.o01) (complexPart y.o02)
      (complexPart y.o12) = y := complexProjection_eq_self y hc
  have hsum0 := fe_complex_square_d0 y.d0 y.d1 y.d2 (complexPart y.o01)
    (complexPart y.o02) (complexPart y.o12)
  have hsum1 := fe_complex_square_d1 y.d0 y.d1 y.d2 (complexPart y.o01)
    (complexPart y.o02) (complexPart y.o12)
  have hsum2 := fe_complex_square_d2 y.d0 y.d1 y.d2 (complexPart y.o01)
    (complexPart y.o02) (complexPart y.o12)
  rw [hy, hs0, h0] at hsum0
  rw [hy, hs1, h1] at hsum1
  rw [hy, hs2, h2] at hsum2
  have hu01 : Complex.normSq (complexPart y.o01) = 1/3 := by linarith
  have hu02 : Complex.normSq (complexPart y.o02) = 1/3 := by linarith
  have hu12 : Complex.normSq (complexPart y.o12) = 1/3 := by linarith
  refine ⟨hu01, hu02, hu12, ?_⟩
  rw [← hy, fe_complex_cubic, h0, h1, h2] at hcub
  linarith

/-- The nine-entry P block of a genuine frame pair, with the first frame diagonal and
the second encoder in the complex sector, saturates every complex slot at 1/3 and kills
the real part of the triangle. Same hypotheses as `fe_uniform_complex_triangle` minus
the third frame, stronger conclusion. -/
theorem uniform_complex_slot_data (p q : Fin 3 → Albert)
    (hp : Frame p) (hq : Frame q) (hpd : ∀ i, IsDiagonal (p i))
    (hPQ : ∀ i j : Fin 3, inner (p i) (q j) = 1/3)
    (hqc : InComplexSector (encoder q)) :
    (encoder q).d0 = 0 ∧ (encoder q).d1 = 0 ∧ (encoder q).d2 = 0 ∧
      Complex.normSq (complexPart (encoder q).o01) = 1/3 ∧
      Complex.normSq (complexPart (encoder q).o02) = 1/3 ∧
      Complex.normSq (complexPart (encoder q).o12) = 1/3 ∧
      (complexPart (encoder q).o01 * complexPart (encoder q).o12 *
        star (complexPart (encoder q).o02)).re = 0 := by
  have hqd : ∀ j : Fin 3, (q j).d0 = 1/3 ∧ (q j).d1 = 1/3 ∧ (q j).d2 = 1/3 := fun j =>
    diagonal_frame_uniform_coordinates p hp hpd (q j) (fun i => hPQ i j)
  have h0 : (encoder q).d0 = 0 := by
    show (q 2).d0 - (q 0).d0 = 0
    rw [(hqd 2).1, (hqd 0).1]
    norm_num
  have h1 : (encoder q).d1 = 0 := by
    show (q 2).d1 - (q 0).d1 = 0
    rw [(hqd 2).2.1, (hqd 0).2.1]
    norm_num
  have h2 : (encoder q).d2 = 0 := by
    show (q 2).d2 - (q 0).d2 = 0
    rw [(hqd 2).2.2, (hqd 0).2.2]
    norm_num
  have hs0 : (jordan (encoder q) (encoder q)).d0 = 2/3 := by
    rw [frame_encoder_square q hq]
    show (q 2).d0 + (q 0).d0 = 2/3
    rw [(hqd 2).1, (hqd 0).1]
    norm_num
  have hs1 : (jordan (encoder q) (encoder q)).d1 = 2/3 := by
    rw [frame_encoder_square q hq]
    show (q 2).d1 + (q 0).d1 = 2/3
    rw [(hqd 2).2.1, (hqd 0).2.1]
    norm_num
  have hs2 : (jordan (encoder q) (encoder q)).d2 = 2/3 := by
    rw [frame_encoder_square q hq]
    show (q 2).d2 + (q 0).d2 = 2/3
    rw [(hqd 2).2.2, (hqd 0).2.2]
    norm_num
  obtain ⟨hn01, hn02, hn12, htri⟩ := complex_slot_data_of_square (encoder q) hqc
    h0 h1 h2 hs0 hs1 hs2 (frame_encoder_cubicNorm q hq)
  exact ⟨h0, h1, h2, hn01, hn02, hn12, htri⟩

/-! ## The original second-frame encoder, slot by slot -/

private theorem smul_octI_slots (c : ℝ) :
    (c • octI).1.re = 0 ∧ (c • octI).1.imI = c ∧ (c • octI).1.imJ = 0 ∧
      (c • octI).1.imK = 0 ∧ (c • octI).2 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [octI, quatI]

/-- A complex-sector octonion slot with vanishing real part is a real multiple of the
standard imaginary unit. -/
private theorem octInComplex_slot_eq (x : Octonion) (hx : OctInComplex x) (c : ℝ)
    (hre : (complexPart x).re = 0) (him : (complexPart x).im = c) :
    x = c • octI := by
  obtain ⟨hj, hk, hz⟩ := hx
  obtain ⟨s0, s1, s2, s3, s4⟩ := smul_octI_slots c
  apply Prod.ext
  · apply Quaternion.ext
    · rw [s0]; exact hre
    · rw [s1]; exact him
    · rw [s2]; exact hj
    · rw [s3]; exact hk
  · rw [s4]; exact hz

/-- The ORIGINAL convention: `flatY1` upper slots are `(1, -i, 1)`. -/
private theorem flatQ_slots :
    (flatScale • flatY1).d0 = 0 ∧ (flatScale • flatY1).d1 = 0 ∧
      (flatScale • flatY1).d2 = 0 ∧
      (flatScale • flatY1).o01 = octScalar flatScale ∧
      (flatScale • flatY1).o02 = (-flatScale) • octI ∧
      (flatScale • flatY1).o12 = octScalar flatScale := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show flatScale * 0 = 0
    ring
  · show flatScale * 0 = 0
    ring
  · show flatScale * 0 = 0
    ring
  · show flatScale • octScalar 1 = octScalar flatScale
    rw [octScalar_smul, mul_one]
  · show flatScale • (-octI) = (-flatScale) • octI
    rw [smul_neg, neg_smul]
  · show flatScale • octScalar 1 = octScalar flatScale
    rw [octScalar_smul, mul_one]

/-! ## The imaginary sign correction

`octConj` is NOT used: octonion conjugation is an anti-automorphism. The sign flip is
produced by the genuine scalar-fixing octonion automorphism of
`exists_octAutomorphism_to_i` applied to `-octI`. -/

private theorem neg_octI_eq :
    -octI = ((⟨0, -1, 0, 0⟩ : Quaternion ℝ), (0 : Quaternion ℝ)) := by
  apply Prod.ext <;> apply Quaternion.ext <;> simp [octI, quatI]

private theorem neg_octI_re : octRe (-octI) = 0 := by
  rw [neg_octI_eq]
  rfl

private theorem neg_octI_normSq : octNormSq (-octI) = 1 := by
  rw [neg_octI_eq]
  norm_num [octNormSq, Quaternion.normSq_def']

private theorem relatedTriple_flatXN (t : OctRelatedTriple) :
    t.compactAutomorphism.equiv flatXN = flatXN := by
  change (⟨flatXN.d0, flatXN.d1, flatXN.d2,
    t.A flatXN.o01, t.C flatXN.o02, t.B flatXN.o12⟩ : Albert) = flatXN
  simp [flatXN, map_zero]

private theorem relatedTriple_fixes_flatFrameP (t : OctRelatedTriple) (i : Fin 3) :
    t.compactAutomorphism.equiv (flatFrameP i) = flatFrameP i :=
  frame_eq_of_encoder_eq flatFrameP flatFrameP flatFrameP_frame flatFrameP_frame
    t.compactAutomorphism
    (by rw [flatFrameP_encoder]; exact relatedTriple_flatXN t) i

private theorem flatFrameP_diagonal (i : Fin 3) : IsDiagonal (flatFrameP i) :=
  frame_projectors_diagonal flatFrameP flatFrameP_frame
    (by rw [flatFrameP_encoder]; simp [IsDiagonal, flatXN]) i

/-! ## Landing exactly on the original second-frame encoder -/

/-- With the saturated slot data and the two nonnegative real slots, one constructed
automorphism fixing the original first frame carries the element to the ORIGINAL
`encoder flatFrameQ = flatScale • flatY1`. Nonnegativity of `a` is what rules out the
negated encoder, since `a = flatScale > 0`. -/
private theorem encoder_to_flatQ (y : Albert) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h01 : y.o01 = octScalar a) (h12 : y.o12 = octScalar b)
    (hc : InComplexSector y)
    (hd0 : y.d0 = 0) (hd1 : y.d1 = 0) (hd2 : y.d2 = 0)
    (hn01 : Complex.normSq (complexPart y.o01) = 1/3)
    (hn02 : Complex.normSq (complexPart y.o02) = 1/3)
    (hn12 : Complex.normSq (complexPart y.o12) = 1/3)
    (htri : (complexPart y.o01 * complexPart y.o12 *
      star (complexPart y.o02)).re = 0) :
    ∃ m : CompactAutomorphism,
      (∀ i : Fin 3, m.equiv (flatFrameP i) = flatFrameP i) ∧
      m.equiv y = flatScale • flatY1 := by
  obtain ⟨hQ0, hQ1, hQ2, hQ01, hQ02, hQ12⟩ := flatQ_slots
  have hasq : a ^ 2 = 1 / 3 := by
    rw [h01, normSq_complexPart_octScalar] at hn01
    exact hn01
  have hbsq : b ^ 2 = 1 / 3 := by
    rw [h12, normSq_complexPart_octScalar] at hn12
    exact hn12
  have ha' : a = flatScale := nonneg_sq_flatScale a ha hasq
  have hb' : b = flatScale := nonneg_sq_flatScale b hb hbsq
  have hy01 : y.o01 = octScalar flatScale := by rw [h01, ha']
  have hy12 : y.o12 = octScalar flatScale := by rw [h12, hb']
  have hab : 0 < a * b := by
    rw [ha', hb']
    exact mul_pos flatScale_pos flatScale_pos
  have htri' : a * b * (complexPart y.o02).re = 0 := by
    rw [h01, h12, complexPart_octScalar, complexPart_octScalar,
      real_real_conj_re] at htri
    exact htri
  have hvre : (complexPart y.o02).re = 0 :=
    (mul_eq_zero.mp htri').resolve_left hab.ne'
  have hvimsq : (complexPart y.o02).im ^ 2 = 1 / 3 := by
    rw [Complex.normSq_apply, hvre] at hn02
    linarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hvimsq.trans flatScale_sq.symm) with him | him
  · -- slot 02 carries `+flatScale*i`; the constructed automorphism flips the sign
    have hy02 : y.o02 = flatScale • octI :=
      octInComplex_slot_eq y.o02 hc.2.1 flatScale hvre him
    obtain ⟨k, hk, hkI⟩ := exists_octAutomorphism_to_i (-octI) neg_octI_re neg_octI_normSq
    have hkIneg : k.A octI = -octI := by
      have h : k.A ((-1 : ℝ) • octI) = octI := by
        rw [neg_one_smul]
        exact hkI
      rw [LinearEquiv.map_smul, neg_one_smul] at h
      have h2 := congrArg (fun x : Octonion => -x) h
      simpa only [neg_neg] using h2
    refine ⟨k.compactAutomorphism, relatedTriple_fixes_flatFrameP k, ?_⟩
    refine Albert.ext ?_ ?_ ?_ ?_ ?_ ?_
    · show y.d0 = (flatScale • flatY1).d0
      exact hd0.trans hQ0.symm
    · show y.d1 = (flatScale • flatY1).d1
      exact hd1.trans hQ1.symm
    · show y.d2 = (flatScale • flatY1).d2
      exact hd2.trans hQ2.symm
    · show k.A y.o01 = (flatScale • flatY1).o01
      rw [hy01, hQ01, diagonalOctTriple_scalar k hk]
    · show k.C y.o02 = (flatScale • flatY1).o02
      rw [hk.2.1, hy02, hQ02, LinearEquiv.map_smul, hkIneg, smul_neg, neg_smul]
    · show k.B y.o12 = (flatScale • flatY1).o12
      rw [hk.1, hy12, hQ12, diagonalOctTriple_scalar k hk]
  · -- slot 02 already carries `-flatScale*i`: the original `flatY1` convention
    have hy02 : y.o02 = (-flatScale) • octI :=
      octInComplex_slot_eq y.o02 hc.2.1 (-flatScale) hvre him
    refine ⟨CompactAutomorphism.refl, fun _ => rfl, ?_⟩
    show y = flatScale • flatY1
    exact Albert.ext (hd0.trans hQ0.symm) (hd1.trans hQ1.symm) (hd2.trans hQ2.symm)
      (hy01.trans hQ01.symm) (hy02.trans hQ02.symm) (hy12.trans hQ12.symm)

/-! ## The public endpoints -/

/-- The nine-entry P block alone normalizes an arbitrary genuine frame pair to the
ORIGINAL ordered flat pair. No third frame and no triple traces are involved. The
conclusion is same-index equality with no reversal disjunction. -/
theorem native_flat_pair_normalization (p q : Fin 3 → Albert)
    (hp : Frame p) (hq : Frame q) (hPQ : ∀ i j : Fin 3, inner (p i) (q j) = 1/3) :
    ∃ g : CompactAutomorphism,
      (∀ i : Fin 3, g.equiv (p i) = flatFrameP i) ∧
      (∀ i : Fin 3, g.equiv (q i) = flatFrameQ i) := by
  obtain ⟨g, a, b, ha, hb, hgp, h01, h12, hsec⟩ :=
    native_ordered_positive_pair p hp (encoder q)
  have hq' : Frame (fun i => g.equiv (q i)) := g.map_frame q hq
  have hqe : encoder (fun i => g.equiv (q i)) = g.equiv (encoder q) := g.encoder_map q
  have hPQ' : ∀ i j : Fin 3, inner (flatFrameP i) (g.equiv (q j)) = 1/3 := by
    intro i j
    rw [← hgp i, g.inner_map]
    exact hPQ i j
  have hqc : InComplexSector (encoder (fun i => g.equiv (q i))) := by
    rw [hqe]
    exact hsec
  obtain ⟨hd0, hd1, hd2, hn01, hn02, hn12, htri⟩ :=
    uniform_complex_slot_data flatFrameP (fun i => g.equiv (q i))
      flatFrameP_frame hq' flatFrameP_diagonal hPQ' hqc
  rw [hqe] at hd0 hd1 hd2 hn01 hn02 hn12 htri
  obtain ⟨m, hmP, hmy⟩ := encoder_to_flatQ (g.equiv (encoder q)) a b ha hb h01 h12
    hsec hd0 hd1 hd2 hn01 hn02 hn12 htri
  have hEnc : (m.comp g).equiv (encoder q) = encoder flatFrameQ := by
    rw [CompactAutomorphism.comp_apply, hmy, flatFrameQ_encoder]
  refine ⟨m.comp g, ?_, ?_⟩
  · intro i
    rw [CompactAutomorphism.comp_apply, hgp i]
    exact hmP i
  · exact fun i =>
      frame_eq_of_encoder_eq q flatFrameQ hq flatFrameQ_frame (m.comp g) hEnc i

/-- Arbitrary genuine frame pair over the original flat ledger is carried to the
ORIGINAL ordered first pair by one constructed product automorphism, and the third
frame is carried into the original fixed-pair flat ledger. -/
theorem native_flat_first_pair_normalization
    (p q r : Fin 3 → Albert) (hp : Frame p) (hq : Frame q) (hr : Frame r)
    (hu : UniformLedger p q r) :
    ∃ g : CompactAutomorphism,
      (∀ i : Fin 3, g.equiv (p i) = flatFrameP i) ∧
      (∀ i : Fin 3, g.equiv (q i) = flatFrameQ i) ∧
      UniformLedger flatFrameP flatFrameQ (fun i => g.equiv (r i)) := by
  obtain ⟨g, hgp, hgq⟩ := native_flat_pair_normalization p q hp hq
    (fun i j => uniformLedger_pair_overlap p q r hr hu i j)
  refine ⟨g, hgp, hgq, ?_⟩
  have hpf : (fun a => g.equiv (p a)) = flatFrameP := by
    funext a
    exact hgp a
  have hqf : (fun a => g.equiv (q a)) = flatFrameQ := by
    funext a
    exact hgq a
  intro i j k
  have h := g.ledger_map p q r i j k
  rw [hpf, hqf] at h
  rw [h]
  exact hu i j k

private theorem uniform_of_full54 (p q r : Fin 3 → Albert)
    (hL : ledger54 ![p, q, r] = ledger54 ![flatFrameP, flatFrameQ, flatFrameR]) :
    UniformLedger p q r := by
  intro i j k
  have h := congrArg (fun L : Ledger54 => L.1 i j k) hL
  change ledger p q r i j k =
    ledger flatFrameP flatFrameQ flatFrameR i j k at h
  exact h.trans (flat_uniform i j k)

/-- The complete original 54-entry fibre premise. -/
theorem native_flat_full54_first_pair_normalization
    (p q r : Fin 3 → Albert) (hp : Frame p) (hq : Frame q) (hr : Frame r)
    (hL : ledger54 ![p, q, r] = ledger54 ![flatFrameP, flatFrameQ, flatFrameR]) :
    ∃ g : CompactAutomorphism,
      (∀ i : Fin 3, g.equiv (p i) = flatFrameP i) ∧
      (∀ i : Fin 3, g.equiv (q i) = flatFrameQ i) ∧
      ledger54 ![flatFrameP, flatFrameQ, (fun i => g.equiv (r i))] =
        ledger54 ![flatFrameP, flatFrameQ, flatFrameR] := by
  obtain ⟨g, hgp, hgq, _⟩ := native_flat_first_pair_normalization p q r hp hq hr
    (uniform_of_full54 p q r hL)
  refine ⟨g, hgp, hgq, ?_⟩
  have hmap : mapAtoms g ![p, q, r] =
      ![flatFrameP, flatFrameQ, (fun i => g.equiv (r i))] := by
    funext s i
    rcases fin3_cases s with rfl | rfl | rfl
    · exact hgp i
    · exact hgq i
    · rfl
  calc
    ledger54 ![flatFrameP, flatFrameQ, (fun i => g.equiv (r i))] =
        ledger54 (mapAtoms g ![p, q, r]) := by rw [hmap]
    _ = ledger54 ![p, q, r] := ledger54_map g ![p, q, r]
    _ = ledger54 ![flatFrameP, flatFrameQ, flatFrameR] := hL

/-- ORDERED BASE FIBRE, uniform-ledger form: every genuine frame triple with the
original flat ledger is carried by ONE actual product automorphism to the original
ordered flat triple or to its ordered third-frame reversal. -/
theorem native_flat_ordered_base_fibre
    (p q r : Fin 3 → Albert) (hp : Frame p) (hq : Frame q) (hr : Frame r)
    (hu : UniformLedger p q r) :
    ∃ g : CompactAutomorphism,
      (∀ i : Fin 3, g.equiv (p i) = flatFrameP i) ∧
      (∀ i : Fin 3, g.equiv (q i) = flatFrameQ i) ∧
      ((∀ i : Fin 3, g.equiv (r i) = flatFrameR i) ∨
        (∀ i : Fin 3, g.equiv (r i) = reverseFrame flatFrameR i)) := by
  obtain ⟨g, hgp, hgq, hgu⟩ := native_flat_first_pair_normalization p q r hp hq hr hu
  obtain ⟨h, hhp, hhq, hcase⟩ :=
    native_fixed_pair_third_frame_normalization (fun i => g.equiv (r i))
      (g.map_frame r hr) hgu
  refine ⟨h.comp g, ?_, ?_, ?_⟩
  · intro i
    rw [CompactAutomorphism.comp_apply, hgp i]
    exact hhp i
  · intro i
    rw [CompactAutomorphism.comp_apply, hgq i]
    exact hhq i
  · rcases hcase with hc | hc
    · exact Or.inl fun i =>
        (CompactAutomorphism.comp_apply h g (r i)).trans (hc i)
    · exact Or.inr fun i =>
        (CompactAutomorphism.comp_apply h g (r i)).trans (hc i)

/-- ORDERED BASE FIBRE: every genuine frame triple with the original complete
54-entry flat ledger is carried by ONE actual product automorphism to the original
ordered flat triple or to its ordered third-frame reversal. -/
theorem native_flat_full54_ordered_base_fibre
    (p q r : Fin 3 → Albert) (hp : Frame p) (hq : Frame q) (hr : Frame r)
    (hL : ledger54 ![p, q, r] = ledger54 ![flatFrameP, flatFrameQ, flatFrameR]) :
    ∃ g : CompactAutomorphism,
      (∀ i : Fin 3, g.equiv (p i) = flatFrameP i) ∧
      (∀ i : Fin 3, g.equiv (q i) = flatFrameQ i) ∧
      ((∀ i : Fin 3, g.equiv (r i) = flatFrameR i) ∨
        (∀ i : Fin 3, g.equiv (r i) = reverseFrame flatFrameR i)) :=
  native_flat_ordered_base_fibre p q r hp hq hr (uniform_of_full54 p q r hL)

end
end Glennie.NativeFirstPairNormalization
