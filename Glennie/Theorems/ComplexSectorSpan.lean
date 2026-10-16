module

public import Glennie.SectorSubspace
public import Glennie.Theorems.FrameMixedGram

/- Native frame adapters into the actual nine-dimensional complex sector.
The coordinate submodule and its dimension are proved in SectorSubspace. -/

public section
namespace Glennie
noncomputable section

/-- This transports the declared octMul, never the alias's inherited product. -/
theorem complexOct_mul_native (u v : ℂ) :
    octMul (complexOct u) (complexOct v) = complexOct (u*v) := by
  ext <;> simp [complexOct,octMul,Complex.mul_re,Complex.mul_im,
    Quaternion.re_mul,Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul]
  all_goals ring

theorem complexProjection_sub (x y : Albert) :
    complexProjection (x-y) = complexProjection x-complexProjection y := by
  ext <;> simp [complexProjection,complexOct,complexPart]

theorem complexProjection_add (x y : Albert) :
    complexProjection (x+y) = complexProjection x+complexProjection y := by
  ext <;> simp [complexProjection,complexOct,complexPart]

theorem complexProjection_smul (a : ℝ) (x : Albert) :
    complexProjection (a • x) = a • complexProjection x := by
  ext <;> simp [complexProjection,complexOct,complexPart,smul_eq_mul]

theorem complexProjection_unit : complexProjection (1 : Albert) = 1 := by
  ext <;> simp [complexProjection,complexOct,complexPart,unit,octScalar]

/-- Polynomial projector recovery places the entire frame in the encoder's sector. -/
theorem frame_in_complexSector (p : Fin 3 → Albert) (hp : Frame p)
    (he : InComplexSector (encoder p)) (i : Fin 3) : p i ∈ complexSector := by
  have he' : encoder p ∈ complexSector := (complexSector_mem_iff _).mpr he
  have hs : jordan (encoder p) (encoder p) ∈ complexSector :=
    (complexSector_mem_iff _).mpr (complexSector_jordan _ _ he he)
  have hu : (1 : Albert) ∈ complexSector := by
    rw [complexSector_mem_iff]
    simp [InComplexSector,OctInComplex,unit,octScalar]
  have h0 : p 0 ∈ complexSector := by
    rw [← frame_projector_first p hp]
    exact complexSector.smul_mem _ (complexSector.sub_mem hs he')
  have h1 : p 1 ∈ complexSector := by
    rw [← frame_projector_middle p hp]
    exact complexSector.sub_mem hu hs
  have h2 : p 2 ∈ complexSector := by
    rw [← frame_projector_last p hp]
    exact complexSector.smul_mem _ (complexSector.add_mem hs he')
  fin_cases i <;> assumption

/-- Every uniform native pair contained in the complex sector spans the whole sector. -/
theorem uniform_pair_span_complexSector (p q : Fin 3 → Albert)
    (hp : Frame p) (hq : Frame q) (hu : ∀ i j, inner (p i) (q j) = 1/3)
    (hpc : ∀ i, InComplexSector (p i)) (hqc : ∀ j, InComplexSector (q j)) :
    Submodule.span ℝ (Set.range (fun u : Fin 3 × Fin 3 => jordan (p u.1) (q u.2))) =
      complexSector :=
  nine_independent_span_complexSector _
    (fun u => complexSector_jordan _ _ (hpc u.1) (hqc u.2))
    (uniform_pair_mixed_linearIndependent p q hp hq hu)

/-- Uniform native ledgers force the third encoder into the actual hidden sector. -/
theorem uniformLedger_complexProjection_encoder (p q r : Fin 3 → Albert)
    (hp : Frame p) (hq : Frame q) (hr : Frame r) (hu : UniformLedger p q r)
    (hpc : ∀ i, InComplexSector (p i)) (hqc : ∀ j, InComplexSector (q j)) :
    complexProjection (encoder r) = 0 :=
  complexProjection_zero_of_nine_perp _
    (fun u => complexSector_jordan _ _ (hpc u.1) (hqc u.2))
    (uniform_pair_mixed_linearIndependent p q hp hq
      (uniformLedger_pair_overlap p q r hr hu)) (encoder r)
    (fun u => uniformLedger_mixed_encoder_perp p q r hu u.1 u.2)

/-- The entire projected square is fixed, not just its three diagonal entries. -/
theorem uniformLedger_complexProjection_encoder_square (p q r : Fin 3 → Albert)
    (hp : Frame p) (hq : Frame q) (hr : Frame r) (hu : UniformLedger p q r)
    (hpc : ∀ i, InComplexSector (p i)) (hqc : ∀ j, InComplexSector (q j)) :
    complexProjection (jordan (encoder r) (encoder r)) = (2/3 : ℝ) • (1 : Albert) := by
  have h := complexProjection_zero_of_nine_perp _
    (fun u => complexSector_jordan _ _ (hpc u.1) (hqc u.2))
    (uniform_pair_mixed_linearIndependent p q hp hq
      (uniformLedger_pair_overlap p q r hr hu))
    (jordan (encoder r) (encoder r)-(2/3 : ℝ) • (1 : Albert))
    (fun u => uniformLedger_mixed_encoder_square_perp p q r hr hu u.1 u.2)
  rw [complexProjection_sub,complexProjection_smul,complexProjection_unit] at h
  exact sub_eq_zero.mp h

theorem frame_projector_complexProjections (r : Fin 3 → Albert) (hr : Frame r)
    (he : complexProjection (encoder r) = 0)
    (hs : complexProjection (jordan (encoder r) (encoder r)) =
      (2/3 : ℝ) • (1 : Albert)) (k : Fin 3) :
    complexProjection (r k) = (1/3 : ℝ) • (1 : Albert) := by
  have h0 : complexProjection (r 0) = (1/3 : ℝ) • (1 : Albert) := by
    rw [← frame_projector_first r hr,complexProjection_smul,complexProjection_sub,hs,he]
    module
  have h1 : complexProjection (r 1) = (1/3 : ℝ) • (1 : Albert) := by
    rw [← frame_projector_middle r hr,complexProjection_sub,complexProjection_unit,hs]
    module
  have h2 : complexProjection (r 2) = (1/3 : ℝ) • (1 : Albert) := by
    rw [← frame_projector_last r hr,complexProjection_smul,complexProjection_add,hs,he]
    module
  fin_cases k <;> assumption

/-- Constant projector projections and uniform overlaps recover every ledger entry. -/
theorem complex_pair_uniformLedger_of_projections (p q r : Fin 3 → Albert)
    (hpc : ∀ i, InComplexSector (p i)) (hqc : ∀ j, InComplexSector (q j))
    (hu : ∀ i j, inner (p i) (q j) = 1/3)
    (hr : ∀ k, complexProjection (r k) = (1/3 : ℝ) • (1 : Albert)) :
    UniformLedger p q r := by
  intro i j k
  have hm : complexProjection (jordan (p i) (q j)) = jordan (p i) (q j) :=
    complexProjection_eq_self _ (complexSector_jordan _ _ (hpc i) (hqc j))
  change inner (jordan (p i) (q j)) (r k) = 1/9
  calc
    _ = inner (jordan (p i) (q j))
        (complexProjection (r k)+hiddenAlbert (hiddenMatrix (r k))) :=
      congrArg (inner (jordan (p i) (q j))) (complex_hidden_decomposition (r k)).symm
    _ = inner (jordan (p i) (q j)) (complexProjection (r k)) := by
      rw [inner_add_right]
      have ho : inner (jordan (p i) (q j)) (hiddenAlbert (hiddenMatrix (r k))) = 0 := by
        rw [← hm]
        exact complex_hidden_orthogonal _ _
      rw [ho,add_zero]
    _ = 1/9 := by
      rw [hr,inner_smul_right,inner,jordan_unit_right]
      change (1/3 : ℝ)*inner (p i) (q j) = 1/9
      rw [hu]
      norm_num

end
end Glennie
