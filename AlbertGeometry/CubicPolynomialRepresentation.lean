/- Every formal homogeneous degree-three polynomial on the actual real27
Euclidean coordinate space receives a constructed continuous symmetric
trilinear diagonal representation. No existence of a representation is assumed.
-/
module

public import AlbertGeometry.CubicDerivatives
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Multiset.ZeroCons
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

@[expose] public section
namespace AlbertGeometry.CubicPolynomialRepresentation
noncomputable section
open scoped BigOperators
open AlbertGeometry.Cubic

abbrev Coordinates := EuclideanSpace ℝ (Fin 27)
abbrev Exponent := Fin 27 →₀ ℕ

/-- Actual total exponent weight, including repeated coordinates. -/
def exponentWeight (a : Exponent) : ℕ := a.sum (fun _ n => n)

/-- Weight3 means three actual coordinate indices, repetitions permitted.
The proof uses the actual multiset of exponents, not a coefficient dictionary
or factorization supplied as an assumption. -/
theorem exponent_factorization (a : Exponent) (ha : exponentWeight a = 3) :
    ∃ f : Fin 3 → Fin 27,
      a = Finsupp.single (f 0) 1 + Finsupp.single (f 1) 1 +
        Finsupp.single (f 2) 1 := by
  have hc : a.toMultiset.card = 3 := by
    simpa only [Finsupp.card_toMultiset, exponentWeight, Function.id_def] using ha
  obtain ⟨i,j,k,hm⟩ := Multiset.card_eq_three.mp hc
  refine ⟨![i,j,k], ?_⟩
  show a = Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single k 1
  -- invert the multiset equivalence instead of a count case split
  -- Normalize count_singleton and the summand order explicitly.
  rw [Finsupp.toMultiset_eq_iff.mp hm, Multiset.insert_eq_cons, Multiset.insert_eq_cons,
    ← Multiset.singleton_add, ← Multiset.singleton_add, Multiset.toFinsupp_add,
    Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, Multiset.toFinsupp_singleton,
    Multiset.toFinsupp_singleton, add_assoc]

/-- A selected factorization, justified by the previous finite theorem. -/
def monomialIndices (a : Exponent) (ha : exponentWeight a = 3) : Fin 3 → Fin 27 :=
  Classical.choose (exponent_factorization a ha)

theorem monomialIndices_spec (a : Exponent) (ha : exponentWeight a = 3) :
    a = Finsupp.single (monomialIndices a ha 0) 1 +
      Finsupp.single (monomialIndices a ha 1) 1 +
      Finsupp.single (monomialIndices a ha 2) 1 :=
  Classical.choose_spec (exponent_factorization a ha)

/-- Evaluate a factorized monomial at arbitrary real coordinates. -/
theorem eval_monomial_factorized (a : Exponent) (f : Fin 3 → Fin 27)
    (ha : a = Finsupp.single (f 0) 1 + Finsupp.single (f 1) 1 +
      Finsupp.single (f 2) 1) (c : ℝ) (v : Fin 27 → ℝ) :
    MvPolynomial.eval v (MvPolynomial.monomial a c) =
      c * v (f 0) * v (f 1) * v (f 2) := by
  rw [ha, MvPolynomial.monomial_add_single, MvPolynomial.monomial_add_single,
    ← MvPolynomial.C_mul_X_eq_monomial]
  simp only [pow_one, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X]

/-- A genuine continuous coordinate product in three separately linear inputs. -/
def coordinateProduct (i j k : Fin 27) : TrilinearForm Coordinates :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 3) ℝ).compContinuousLinearMap
    ![EuclideanSpace.proj i, EuclideanSpace.proj j, EuclideanSpace.proj k]

theorem coordinateProduct_apply (i j k : Fin 27) (m : Fin 3 → Coordinates) :
    coordinateProduct i j k m = m 0 i * m 1 j * m 2 k := by
  simp [coordinateProduct, Fin.prod_univ_three, mul_assoc]

/-- The six slot permutations are averaged with literal coefficient1/6.
Repeated coordinate indices remain six terms; no orbit-size division is used. -/
def symmetricCoordinateForm (i j k : Fin 27) : TrilinearForm Coordinates :=
  (1 / 6 : ℝ) • (coordinateProduct i j k + coordinateProduct i k j +
    coordinateProduct j i k + coordinateProduct j k i +
    coordinateProduct k i j + coordinateProduct k j i)

theorem symmetricCoordinateForm_apply (i j k : Fin 27) (x y z : Coordinates) :
    symmetricCoordinateForm i j k ![x,y,z] = (1 / 6 : ℝ) *
      (x i * y j * z k + x i * y k * z j +
       x j * y i * z k + x j * y k * z i +
       x k * y i * z j + x k * y j * z i) := by
  simp [symmetricCoordinateForm, coordinateProduct_apply, smul_eq_mul]
  ring

theorem symmetricCoordinateForm_swap12 (i j k : Fin 27) (x y z : Coordinates) :
    symmetricCoordinateForm i j k ![x,y,z] =
      symmetricCoordinateForm i j k ![y,x,z] := by
  rw [symmetricCoordinateForm_apply, symmetricCoordinateForm_apply]
  ring

theorem symmetricCoordinateForm_swap23 (i j k : Fin 27) (x y z : Coordinates) :
    symmetricCoordinateForm i j k ![x,y,z] =
      symmetricCoordinateForm i j k ![x,z,y] := by
  rw [symmetricCoordinateForm_apply, symmetricCoordinateForm_apply]
  ring

theorem symmetricCoordinateForm_diagonal (i j k : Fin 27) (x : Coordinates) :
    symmetricCoordinateForm i j k (fun _ : Fin 3 => x) = x i * x j * x k := by
  have hv : (fun _ : Fin 3 => x) = ![x,x,x] := by
    ext t
    fin_cases t <;> rfl
  rw [hv, symmetricCoordinateForm_apply]
  ring

/-- The degree-three part of a monomial, constructed without hypotheses on p.
The final endpoint proves that every supported monomial of a homogeneous cubic
uses the first branch, so this is not a silent truncation of the endpoint. -/
def monomialForm (a : Exponent) : TrilinearForm Coordinates :=
  if ha : exponentWeight a = 3 then
    symmetricCoordinateForm (monomialIndices a ha 0)
      (monomialIndices a ha 1) (monomialIndices a ha 2)
  else 0

theorem monomialForm_swap12 (a : Exponent) (x y z : Coordinates) :
    monomialForm a ![x,y,z] = monomialForm a ![y,x,z] := by
  by_cases ha : exponentWeight a = 3
  · simp only [monomialForm, dif_pos ha]
    exact symmetricCoordinateForm_swap12 _ _ _ x y z
  · simp [monomialForm, ha]

theorem monomialForm_swap23 (a : Exponent) (x y z : Coordinates) :
    monomialForm a ![x,y,z] = monomialForm a ![x,z,y] := by
  by_cases ha : exponentWeight a = 3
  · simp only [monomialForm, dif_pos ha]
    exact symmetricCoordinateForm_swap23 _ _ _ x y z
  · simp [monomialForm, ha]

theorem monomialForm_diagonal (a : Exponent) (ha : exponentWeight a = 3)
    (x : Coordinates) :
    monomialForm a (fun _ : Fin 3 => x) =
      MvPolynomial.eval (fun i => x i) (MvPolynomial.monomial a (1 : ℝ)) := by
  rw [monomialForm, dif_pos ha, symmetricCoordinateForm_diagonal]
  simpa only [one_mul] using
    (eval_monomial_factorized a (monomialIndices a ha)
      (monomialIndices_spec a ha) 1 (fun i => x i)).symm

/-- Finite coefficient support gives an actual continuous trilinear map. -/
def polynomialForm (p : MvPolynomial (Fin 27) ℝ) : TrilinearForm Coordinates :=
  ∑ a ∈ p.support, p.coeff a • monomialForm a

theorem polynomialForm_apply (p : MvPolynomial (Fin 27) ℝ)
    (m : Fin 3 → Coordinates) :
    polynomialForm p m = ∑ a ∈ p.support, p.coeff a * monomialForm a m := by
  -- generic simp lemmas sum_apply/smul_apply.
  simp [polynomialForm, smul_eq_mul]

theorem polynomialForm_swap12 (p : MvPolynomial (Fin 27) ℝ) (x y z : Coordinates) :
    polynomialForm p ![x,y,z] = polynomialForm p ![y,x,z] := by
  rw [polynomialForm_apply, polynomialForm_apply]
  apply Finset.sum_congr rfl
  intro a ha
  rw [monomialForm_swap12]

theorem polynomialForm_swap23 (p : MvPolynomial (Fin 27) ℝ) (x y z : Coordinates) :
    polynomialForm p ![x,y,z] = polynomialForm p ![x,z,y] := by
  rw [polynomialForm_apply, polynomialForm_apply]
  apply Finset.sum_congr rfl
  intro a ha
  rw [monomialForm_swap23]

/-- Every supported exponent of an arbitrary formal homogeneous cubic has
actual total exponent weight3. The polynomial hypothesis is not just p.totalDegree=3. -/
theorem supported_exponent_weight (p : MvPolynomial (Fin 27) ℝ)
    (hp : p.IsHomogeneous 3) (a : Exponent) (ha : a ∈ p.support) :
    exponentWeight a = 3 := by
  simpa only [exponentWeight, Finsupp.sum] using
    (hp.degree_eq_sum_deg_support ha).symm

/-- Diagonal equality for EVERY homogeneous degree-three polynomial.
All coefficients and repeated-variable monomials are retained. -/
theorem polynomialForm_diagonal (p : MvPolynomial (Fin 27) ℝ)
    (hp : p.IsHomogeneous 3) (x : Coordinates) :
    polynomialForm p (fun _ : Fin 3 => x) = MvPolynomial.eval (fun i => x i) p := by
  rw [polynomialForm_apply]
  conv_rhs => rw [p.as_sum]
  rw [MvPolynomial.eval_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [monomialForm_diagonal a (supported_exponent_weight p hp a ha) x]
  simp only [MvPolynomial.eval_monomial, one_mul]

/-- The constructed form has proved adjacent-swap symmetry, not symmetry fields
supplied as an input to the polynomial endpoint. -/
def polynomialRepresentation (p : MvPolynomial (Fin 27) ℝ) :
    SymmetricTrilinearForm Coordinates where
  form := polynomialForm p
  swap12 := polynomialForm_swap12 p
  swap23 := polynomialForm_swap23 p

theorem polynomialRepresentation_diagonal (p : MvPolynomial (Fin 27) ℝ)
    (hp : p.IsHomogeneous 3) (x : Coordinates) :
    diagonalCubic (polynomialRepresentation p).form x =
      MvPolynomial.eval (fun i => x i) p :=
  polynomialForm_diagonal p hp x

/-- Representation existence is a conclusion constructed from polynomial data. -/
theorem exists_continuous_symmetric_representation (p : MvPolynomial (Fin 27) ℝ)
    (hp : p.IsHomogeneous 3) :
    ∃ P : SymmetricTrilinearForm Coordinates,
      ∀ x : Coordinates, diagonalCubic P.form x = MvPolynomial.eval (fun i => x i) p :=
  ⟨polynomialRepresentation p, polynomialRepresentation_diagonal p hp⟩

end
end AlbertGeometry.CubicPolynomialRepresentation
