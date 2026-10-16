/-
The reverse polynomial producer uses every
ordered triple of actual Euclidean coordinate basis vectors. Homogeneity and
evaluation equality are proved from finite sums and actual linearity. No
coefficient/evaluation conclusion or representation roundtrip is assumed.
-/
module

public import AlbertGeometry.CubicPolynomialRepresentation
public import AlbertGeometry.CubicPolarizationUniqueness

@[expose] public section

namespace AlbertGeometry.CubicPolynomialReconstruction
noncomputable section
open scoped BigOperators
open AlbertGeometry.Cubic AlbertGeometry.CubicPolynomialRepresentation

/-- The existing actual Euclidean coordinate basis vector. -/
def coordinateVector (i : Fin 27) : Coordinates := EuclideanSpace.basisFun (Fin 27) ℝ i

theorem coordinate_sum (x : Coordinates) :
    ∑ i : Fin 27, x i • coordinateVector i = x := by
  simpa only [coordinateVector, EuclideanSpace.basisFun_repr] using
    (EuclideanSpace.basisFun (Fin 27) ℝ).sum_repr x

/-- Three ordered factors, including repeated indices, recorded as an actual exponent. -/
def orderedExponent (i j k : Fin 27) : Fin 27 →₀ ℕ :=
  Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single k 1

theorem orderedExponent_degree (i j k : Fin 27) :
    (orderedExponent i j k).degree = 3 := by
  -- simp only keeps the default simprocs, which can close 1 + 1 + 1 = 3
  -- and leave norm_num with no goal; one terminal simp call avoids both outcomes.
  simp [orderedExponent]

/-- An actual monomial; coincident indices accumulate in its Finsupp exponent. -/
def orderedMonomial (i j k : Fin 27) (c : ℝ) : MvPolynomial (Fin 27) ℝ :=
  MvPolynomial.monomial (orderedExponent i j k) c

theorem orderedMonomial_homogeneous (i j k : Fin 27) (c : ℝ) :
    (orderedMonomial i j k c).IsHomogeneous 3 :=
  MvPolynomial.isHomogeneous_monomial c (orderedExponent_degree i j k)

theorem orderedMonomial_eval (i j k : Fin 27) (c : ℝ) (x : Coordinates) :
    MvPolynomial.eval (fun l => x l) (orderedMonomial i j k c) =
      c * x i * x j * x k := by
  exact eval_monomial_factorized (orderedExponent i j k) ![i, j, k] rfl c
    (fun l => x l)

/-- All ordered coefficients contribute, with no compressed multiplicity cases. -/
def reconstruction (P : SymmetricTrilinearForm Coordinates) : MvPolynomial (Fin 27) ℝ :=
  ∑ i : Fin 27, ∑ j : Fin 27, ∑ k : Fin 27,
    orderedMonomial i j k (P.form ![coordinateVector i, coordinateVector j, coordinateVector k])

theorem reconstruction_homogeneous (P : SymmetricTrilinearForm Coordinates) :
    (reconstruction P).IsHomogeneous 3 := by
  unfold reconstruction
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  apply MvPolynomial.IsHomogeneous.sum
  intro j hj
  apply MvPolynomial.IsHomogeneous.sum
  intro k hk
  exact orderedMonomial_homogeneous i j k _

/-- Successive finite sums are expanded through the genuine fully curried CLMs. -/
theorem fullyCurried_coordinate_expansion (P : SymmetricTrilinearForm Coordinates)
    (x y z : Coordinates) :
    fullyCurried P x y z = ∑ i : Fin 27, ∑ j : Fin 27, ∑ k : Fin 27,
      (x i * y j * z k) * fullyCurried P (coordinateVector i) (coordinateVector j)
        (coordinateVector k) := by
  calc
    fullyCurried P x y z =
        fullyCurried P (∑ i : Fin 27, x i • coordinateVector i)
          (∑ j : Fin 27, y j • coordinateVector j)
          (∑ k : Fin 27, z k • coordinateVector k) := by
      rw [coordinate_sum, coordinate_sum, coordinate_sum]
    _ = _ := by
      -- the simp call below leaves the three sums in reversed order,
      -- so reverse them explicitly and close each summand by ring.
      have hrev : ∀ f : Fin 27 → Fin 27 → Fin 27 → ℝ,
          ∑ a : Fin 27, ∑ b : Fin 27, ∑ c : Fin 27, f a b c =
            ∑ c : Fin 27, ∑ b : Fin 27, ∑ a : Fin 27, f a b c := by
        intro f
        calc
          ∑ a : Fin 27, ∑ b : Fin 27, ∑ c : Fin 27, f a b c =
              ∑ a : Fin 27, ∑ c : Fin 27, ∑ b : Fin 27, f a b c :=
            Finset.sum_congr rfl fun a _ => Finset.sum_comm
          _ = ∑ c : Fin 27, ∑ a : Fin 27, ∑ b : Fin 27, f a b c := Finset.sum_comm
          _ = ∑ c : Fin 27, ∑ b : Fin 27, ∑ a : Fin 27, f a b c :=
            Finset.sum_congr rfl fun c _ => Finset.sum_comm
      simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
      rw [hrev]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      ring

theorem form_coordinate_expansion (P : SymmetricTrilinearForm Coordinates)
    (x y z : Coordinates) :
    P.form ![x, y, z] = ∑ i : Fin 27, ∑ j : Fin 27, ∑ k : Fin 27,
      (x i * y j * z k) *
        P.form ![coordinateVector i, coordinateVector j, coordinateVector k] := by
  rw [← fullyCurried_apply P x y z, fullyCurried_coordinate_expansion]
  simp_rw [fullyCurried_apply]

/-- Genuine evaluation equality, derived by expanding all three coordinate sums. -/
theorem reconstruction_eval (P : SymmetricTrilinearForm Coordinates) (x : Coordinates) :
    MvPolynomial.eval (fun i => x i) (reconstruction P) = diagonalCubic P.form x := by
  calc
    MvPolynomial.eval (fun i => x i) (reconstruction P) =
        ∑ i : Fin 27, ∑ j : Fin 27, ∑ k : Fin 27,
          P.form ![coordinateVector i, coordinateVector j, coordinateVector k] *
            x i * x j * x k := by
      simp only [reconstruction, MvPolynomial.eval_sum, orderedMonomial_eval]
    _ = ∑ i : Fin 27, ∑ j : Fin 27, ∑ k : Fin 27,
        (x i * x j * x k) *
          P.form ![coordinateVector i, coordinateVector j, coordinateVector k] := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = diagonalCubic P.form x := by
      have hx : (fun _ : Fin 3 => x) = ![x, x, x] := by
        ext i
        fin_cases i <;> rfl
      change _ = P.form (fun _ : Fin 3 => x)
      rw [hx]
      exact (form_coordinate_expansion P x x x).symm

/-- Reconstructing the actual form, including its symmetry certificates, is a
proved conclusion. Equality of polynomial evaluations need not be assumed. -/
theorem polynomialRepresentation_reconstruction (P : SymmetricTrilinearForm Coordinates) :
    polynomialRepresentation (reconstruction P) = P := by
  -- explicit arguments fix the carrier, instead of applying the
  -- strict-implicit Injective lemma.
  refine symmetricTrilinearForm_ext (polynomialRepresentation (reconstruction P)) P
    (form_eq_of_diagonal_eq (polynomialRepresentation (reconstruction P)) P ?_)
  funext x
  calc
    diagonalCubic (polynomialRepresentation (reconstruction P)).form x =
        MvPolynomial.eval (fun i => x i) (reconstruction P) :=
      polynomialRepresentation_diagonal (reconstruction P) (reconstruction_homogeneous P) x
    _ = diagonalCubic P.form x := reconstruction_eval P x

end
end AlbertGeometry.CubicPolynomialReconstruction
