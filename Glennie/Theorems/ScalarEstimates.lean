module

public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Basic.Complex.Basic

/-!
Exact scalar ingredients of the compact Glennie estimate. The native Albert
adapter is a separate obligation: these results make no spectral or pair
reduction assumption and do not state the universal Glennie endpoint.
-/

public section

namespace Glennie.ScalarEstimates

/-- The trace-zero cubic discriminant, with the actual unscaled trace metric. -/
theorem discriminant_identity (a b c : ℝ) (htrace : a + b + c = 0) :
    ((a - b) * (a - c) * (b - c)) ^ 2 =
      (a ^ 2 + b ^ 2 + c ^ 2) ^ 3 / 2 - 27 * (a * b * c) ^ 2 := by
  have hc : c = -a - b := by linarith
  rw [hc]
  ring

theorem discriminant_le (a b c : ℝ) (htrace : a + b + c = 0) :
    ((a - b) * (a - c) * (b - c)) ^ 2 ≤
      (a ^ 2 + b ^ 2 + c ^ 2) ^ 3 / 2 := by
  rw [discriminant_identity a b c htrace]
  nlinarith [sq_nonneg (a * b * c)]

theorem discriminant_eq_iff (a b c : ℝ) (htrace : a + b + c = 0) :
    ((a - b) * (a - c) * (b - c)) ^ 2 =
      (a ^ 2 + b ^ 2 + c ^ 2) ^ 3 / 2 ↔ a * b * c = 0 := by
  rw [discriminant_identity a b c htrace]
  constructor
  · intro h
    have hs : (a * b * c) ^ 2 = 0 := by linarith
    exact (sq_eq_zero_iff).mp hs
  · intro h
    simp [h]

private theorem amgm_min (a b c : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hac : a ≤ c) :
    27 * (a * b * c) ≤ (a + b + c) ^ 3 := by
  have hu : 0 ≤ b - a := by linarith
  have hv : 0 ≤ c - a := by linarith
  have hq : 0 ≤ (b - a) ^ 2 - (b - a) * (c - a) + (c - a) ^ 2 := by
    nlinarith [sq_nonneg ((b - a) - (c - a)), sq_nonneg (b - a), sq_nonneg (c - a)]
  have hm := mul_nonneg ha hq
  have hp := pow_nonneg (add_nonneg hu hv) 3
  have hid : (a + b + c) ^ 3 - 27 * (a * b * c) =
      ((b - a) + (c - a)) ^ 3 +
        9 * a * ((b - a) ^ 2 - (b - a) * (c - a) + (c - a) ^ 2) := by ring
  linarith

/-- AM–GM in a polynomial form, including zero arguments. -/
theorem amgm_three (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    27 * (a * b * c) ≤ (a + b + c) ^ 3 := by
  rcases le_total a b with hab | hba
  · rcases le_total a c with hac | hca
    · exact amgm_min a b c ha hab hac
    · have h := amgm_min c a b hc hca (hca.trans hab)
      nlinarith
  · rcases le_total b c with hbc | hcb
    · have h := amgm_min b a c hb hba hbc
      nlinarith
    · have h := amgm_min c a b hc (hcb.trans hba) hcb
      nlinarith

private theorem amgm_min_eq (a b c : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hac : a ≤ c)
    (heq : 27 * (a * b * c) = (a + b + c) ^ 3) : a = b ∧ b = c := by
  have hu : 0 ≤ b - a := by linarith
  have hv : 0 ≤ c - a := by linarith
  have hq : 0 ≤ (b - a) ^ 2 - (b - a) * (c - a) + (c - a) ^ 2 := by
    nlinarith [sq_nonneg ((b - a) - (c - a)), sq_nonneg (b - a), sq_nonneg (c - a)]
  have hm := mul_nonneg ha hq
  have hid : (a + b + c) ^ 3 - 27 * (a * b * c) =
      ((b - a) + (c - a)) ^ 3 +
        9 * a * ((b - a) ^ 2 - (b - a) * (c - a) + (c - a) ^ 2) := by ring
  have hle : ((b - a) + (c - a)) ^ 3 ≤ 0 := by linarith
  have hs : (b - a) + (c - a) ≤ 0 := by
    by_contra h
    have hp := pow_pos (lt_of_not_ge h) 3
    linarith
  constructor <;> linarith

theorem amgm_three_eq_iff (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    27 * (a * b * c) = (a + b + c) ^ 3 ↔ a = b ∧ b = c := by
  constructor
  · intro heq
    rcases le_total a b with hab | hba
    · rcases le_total a c with hac | hca
      · exact amgm_min_eq a b c ha hab hac heq
      · have h' : 27 * (c * a * b) = (c + a + b) ^ 3 := by nlinarith
        obtain ⟨h1, h2⟩ := amgm_min_eq c a b hc hca (hca.trans hab) h'
        constructor <;> linarith
    · rcases le_total b c with hbc | hcb
      · have h' : 27 * (b * a * c) = (b + a + c) ^ 3 := by nlinarith
        obtain ⟨h1, h2⟩ := amgm_min_eq b a c hb hba hbc h'
        constructor <;> linarith
      · have h' : 27 * (c * a * b) = (c + a + b) ^ 3 := by nlinarith
        obtain ⟨h1, h2⟩ := amgm_min_eq c a b hc (hcb.trans hba) hcb h'
        constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    ring

/-- The squared product budget for three squared off-diagonal moduli. -/
theorem product_le_one_over_216 (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : a + b + c ≤ 1 / 2) :
    a * b * c ≤ 1 / 216 := by
  have ham := amgm_three a b c ha hb hc
  have hs0 : 0 ≤ a + b + c := by linarith
  have hcube : (a + b + c) ^ 3 ≤ (1 / 2 : ℝ) ^ 3 := by
    exact pow_le_pow_left₀ hs0 hs 3
  norm_num at hcube
  linarith

/-- The three estimates combine to the precise squared constant 23328. -/
theorem sector_sharp_estimate (v t d : ℝ)
    (hv : v ^ 2 ≤ 1 / 2) (ht : t ^ 2 ≤ 1 / 216) (hd : d ^ 2 ≤ 1 / 216) :
    23328 * (2 * v * t * d) ^ 2 ≤ 1 := by
  have hvt : v ^ 2 * t ^ 2 ≤ (1 / 2 : ℝ) * (1 / 216) :=
    mul_le_mul hv ht (sq_nonneg t) (by norm_num)
  have hvtd : v ^ 2 * t ^ 2 * d ^ 2 ≤
      ((1 / 2 : ℝ) * (1 / 216)) * (1 / 216) :=
    mul_le_mul hvt hd (sq_nonneg d) (by norm_num)
  calc
    23328 * (2 * v * t * d) ^ 2 = 93312 * (v ^ 2 * t ^ 2 * d ^ 2) := by ring
    _ ≤ 93312 * (((1 / 2 : ℝ) * (1 / 216)) * (1 / 216)) :=
      mul_le_mul_of_nonneg_left hvtd (by norm_num)
    _ = 1 := by norm_num

private theorem unit_product_eq_iff (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ha1 : a ≤ 1) (hb1 : b ≤ 1) (hc1 : c ≤ 1) :
    a * b * c = 1 ↔ a = 1 ∧ b = 1 ∧ c = 1 := by
  constructor
  · intro hprod
    have hbc : b * c ≤ 1 := by
      have h := mul_le_mul hb1 hc1 hc (by norm_num)
      simpa using h
    have habc : a * b * c ≤ a := by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hbc ha
    have haeq : a = 1 := by linarith
    rw [haeq, one_mul] at hprod
    have hbc_b : b * c ≤ b := by
      simpa using mul_le_mul_of_nonneg_left hc1 hb
    have hbeq : b = 1 := by linarith
    have hceq : c = 1 := by simpa [hbeq] using hprod
    exact ⟨haeq, hbeq, hceq⟩
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num

/-- Equality in the sharp scalar product forces equality in every ingredient. -/
theorem sector_sharp_equality_iff (v t d : ℝ)
    (hv : v ^ 2 ≤ 1 / 2) (ht : t ^ 2 ≤ 1 / 216) (hd : d ^ 2 ≤ 1 / 216) :
    23328 * (2 * v * t * d) ^ 2 = 1 ↔
      v ^ 2 = 1 / 2 ∧ t ^ 2 = 1 / 216 ∧ d ^ 2 = 1 / 216 := by
  have hunit := unit_product_eq_iff (2 * v ^ 2) (216 * t ^ 2) (216 * d ^ 2)
    (by nlinarith [sq_nonneg v]) (by nlinarith [sq_nonneg t])
    (by nlinarith [sq_nonneg d]) (by linarith) (by linarith) (by linarith)
  have hid : 23328 * (2 * v * t * d) ^ 2 =
      (2 * v ^ 2) * (216 * t ^ 2) * (216 * d ^ 2) := by ring
  rw [hid, hunit]
  constructor
  · rintro ⟨hv', ht', hd'⟩
    constructor
    · linarith
    constructor <;> linarith
  · rintro ⟨hv', ht', hd'⟩
    simp [hv', ht', hd']

/-- Hadamard's bound for a Gram matrix with all three diagonal entries two. -/
theorem gram_det_le_eight (a b c : ℝ) (ha0 : -2 ≤ a) (ha1 : a ≤ 2) :
    8 - 2 * (a ^ 2 + b ^ 2 + c ^ 2) + 2 * a * b * c ≤ 8 := by
  have habc : a * b * c ≤ b ^ 2 + c ^ 2 := by
    rcases le_total 0 (b * c) with hbc | hbc
    · have h := mul_le_mul_of_nonneg_right ha1 hbc
      nlinarith [sq_nonneg (b - c)]
    · have h := mul_le_mul_of_nonpos_right ha0 hbc
      nlinarith [sq_nonneg (b + c)]
  nlinarith [sq_nonneg a]

theorem gram_det_eq_eight_iff (a b c : ℝ) (ha0 : -2 ≤ a) (ha1 : a ≤ 2) :
    8 - 2 * (a ^ 2 + b ^ 2 + c ^ 2) + 2 * a * b * c = 8 ↔
      a = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro hdet
    have habc : a * b * c ≤ b ^ 2 + c ^ 2 := by
      rcases le_total 0 (b * c) with hbc | hbc
      · have h := mul_le_mul_of_nonneg_right ha1 hbc
        nlinarith [sq_nonneg (b - c)]
      · have h := mul_le_mul_of_nonpos_right ha0 hbc
        nlinarith [sq_nonneg (b + c)]
    have ha : a = 0 := by nlinarith [sq_nonneg a]
    rw [ha] at hdet
    have hb : b = 0 := by nlinarith [sq_nonneg b, sq_nonneg c]
    have hc : c = 0 := by nlinarith [sq_nonneg b, sq_nonneg c]
    exact ⟨ha, hb, hc⟩
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num

/-- Equal-modulus orthogonal rows have a fixed real quartet coefficient. -/
theorem equal_norm_zero_sum_real_product (z₀ z₁ z₂ : ℂ) (r : ℝ)
    (hzero : z₀ + z₁ + z₂ = 0)
    (h₀ : Complex.normSq z₀ = r) (h₁ : Complex.normSq z₁ = r)
    (h₂ : Complex.normSq z₂ = r) :
    (z₀ * star z₁).re = -r / 2 := by
  have hz : z₀ + z₁ = -z₂ := eq_neg_iff_add_eq_zero.mpr hzero
  have he : Complex.normSq (z₀ + z₁) = r := by rw [hz]; simpa using h₂
  rw [Complex.normSq_add, h₀, h₁] at he
  simp only [Complex.star_def]
  linarith

end Glennie.ScalarEstimates
