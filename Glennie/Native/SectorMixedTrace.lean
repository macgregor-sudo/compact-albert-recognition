/- Complete small real mixed-trace cancellation.
No coordinate polynomial expansion, missing cancellation premise, inverse,
spectral or norm reconstruction.
All native Hermitian premises are supplied by explicit proved source APIs. -/
module
public import Glennie.Native.SectorAssemblyBridges

@[expose] public section
namespace Glennie.SectorMixedTrace
noncomputable section

abbrev Mat := Matrix (Fin 3) (Fin 3) ℂ

/-- Anti-Hermitian times Hermitian has purely imaginary trace, using cyclicity. -/
theorem antiHermitian_trace_re_zero (S G : Mat)
    (hS : S.conjTranspose = -S) (hG : G.IsHermitian) :
    (S*G).trace.re = 0 := by
  have hs : star (S*G).trace = -(S*G).trace := by
    calc
      _ = (S*G).conjTranspose.trace := (Matrix.trace_conjTranspose (S*G)).symm
      _ = -(G*S).trace := by
        simp only [Matrix.conjTranspose_mul, hG.eq, hS,
          Matrix.mul_neg, Matrix.trace_neg]
      _ = _ := by rw [Matrix.trace_mul_comm G S]
  have hr : (S*G).trace.re = -(S*G).trace.re := by
    simpa using congrArg Complex.re hs
  linarith

/-- Conjugation reverses every factor; the two-factor cyclic rotation retains
precisely the S*B*K order on the right, including its minus sign. -/
theorem star_trace_four (S G K B : Mat)
    (hS : S.conjTranspose = -S) (hG : G.IsHermitian)
    (hK : K.IsHermitian) (hB : B.IsHermitian) :
    star (S*G*K*B).trace = -(G*S*B*K).trace := by
  calc
    _ = (S*G*K*B).conjTranspose.trace :=
      (Matrix.trace_conjTranspose (S*G*K*B)).symm
    _ = -(B*K*G*S).trace := by
      simp only [Matrix.conjTranspose_mul, hB.eq, hK.eq, hG.eq, hS,
        Matrix.mul_neg, Matrix.trace_neg, Matrix.mul_assoc]
    _ = _ := by
      simpa only [Matrix.mul_assoc] using
        congrArg (fun t : ℂ => -t) (Matrix.trace_mul_comm (B*K) (G*S))

theorem trace_four_re_reverse (S G K B : Mat)
    (hS : S.conjTranspose = -S) (hG : G.IsHermitian)
    (hK : K.IsHermitian) (hB : B.IsHermitian) :
    (S*G*K*B).trace.re = -(G*S*B*K).trace.re := by
  simpa using congrArg Complex.re (star_trace_four S G K B hS hG hK hB)

/-- Expand the actual hidden contraction over the full complex field first.
G=M†M is literal, and no determinant/inverse condition is used. -/
theorem hidden_trace_expansion (M S K B : Mat)
    (hS : S.conjTranspose = -S) :
    ((M*S).conjTranspose *
      (M*((K*B).trace • (1:Mat)-K*B))).trace =
      -((K*B).trace * (S*(M.conjTranspose*M)).trace) +
        (S*(M.conjTranspose*M)*K*B).trace := by
  simp only [Matrix.conjTranspose_mul, hS, Matrix.mul_sub,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_sub, Matrix.trace_neg, Matrix.trace_smul, smul_eq_mul,
    Matrix.mul_assoc]
  ring

/-- The scalar t=tr(KB) is real by the explicit Hermitian trace bridge. Its
product with the purely imaginary tr(SG) contributes zero real part. -/
theorem hidden_real_trace (M S K B : Mat)
    (hS : S.conjTranspose = -S) (hK : K.IsHermitian) (hB : B.IsHermitian) :
    ((M*S).conjTranspose *
      (M*((K*B).trace • (1:Mat)-K*B))).trace.re =
        (S*(M.conjTranspose*M)*K*B).trace.re := by
  have hG : (M.conjTranspose*M).IsHermitian :=
    SectorAssemblyBridges.hidden_gram_isHermitian M
  have hsg := antiHermitian_trace_re_zero S (M.conjTranspose*M) hS hG
  have ht := SectorAssemblyBridges.trace_mul_im_zero K B hK hB
  rw [hidden_trace_expansion M S K B hS]
  simp [Complex.mul_re, hsg, ht]

/-- Exact real mixed cancellation. All singular M are covered. No missing
mixed matrix identity or scalar cancellation is supplied as a premise. -/
theorem mixed_trace_cancel (M S K B : Mat)
    (hS : S.conjTranspose = -S) (hK : K.IsHermitian) (hB : B.IsHermitian) :
    ((M.conjTranspose*M)*(S*B*K-K*B*S)).trace.re +
      2*((M*S).conjTranspose *
        (M*((K*B).trace • (1:Mat)-K*B))).trace.re = 0 := by
  let G : Mat := M.conjTranspose*M
  have hG : G.IsHermitian := SectorAssemblyBridges.hidden_gram_isHermitian M
  have hcyc : (G*K*B*S).trace = (S*G*K*B).trace := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle (G*K) B S
  have hc : (G*(S*B*K-K*B*S)).trace =
      (G*S*B*K).trace - (S*G*K*B).trace := by
    calc
      _ = (G*S*B*K).trace - (G*K*B*S).trace := by
        simp only [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_assoc]
      _ = _ := by rw [hcyc]
  have hcr : (G*(S*B*K-K*B*S)).trace.re =
      (G*S*B*K).trace.re - (S*G*K*B).trace.re := by
    simpa only [Complex.sub_re] using congrArg Complex.re hc
  have hr : (S*G*K*B).trace.re = -(G*S*B*K).trace.re :=
    trace_four_re_reverse S G K B hS hG hK hB
  have hh : ((M*S).conjTranspose *
      (M*((K*B).trace • (1:Mat)-K*B))).trace.re = (S*G*K*B).trace.re :=
    hidden_real_trace M S K B hS hK hB
  change (G*(S*B*K-K*B*S)).trace.re +
    2*((M*S).conjTranspose*(M*((K*B).trace • (1:Mat)-K*B))).trace.re = 0
  rw [hcr, hh]
  linarith

/-- Native facts for any x,y,z instantiate the generic cancellation: K and B
are actual sector matrices, while S is their native adjugate commutator.
This wrapper does not assert the commutator action unless x,y are pure complex. -/
theorem native_mixed_trace_cancel (x y z : Albert) :
    let D := sectorComplexMatrix x
    let H := sectorComplexMatrix y
    let K := sectorComplexMatrix z
    let M := hiddenMatrix z
    let B := sectorComplexMatrix (jordan x y)
    let S := H.adjugate*D.adjugate-D.adjugate*H.adjugate
    ((M.conjTranspose*M)*(S*B*K-K*B*S)).trace.re +
      2*((M*S).conjTranspose *
        (M*((K*B).trace • (1:Mat)-K*B))).trace.re = 0 := by
  dsimp only
  exact mixed_trace_cancel _ _ _ _
    (SectorAssemblyBridges.native_adjugate_commutator_antiHermitian x y)
    (sectorComplexMatrix_isHermitian z)
    (sectorComplexMatrix_isHermitian (jordan x y))

end
end Glennie.SectorMixedTrace
