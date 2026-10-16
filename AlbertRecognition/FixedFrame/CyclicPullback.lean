/- Actual native cyclic frame transport for an unrestricted symmetric cubic.
Unknown-cubic invariance is neither a field nor a premise: B is pulled back.
-/
module

public import AlbertRecognition.CubicOperators
public import Glennie.Automorphism
public import Glennie.Native.RealConjugation

@[expose] public section
namespace AlbertRecognition
noncomputable section
open Glennie

/-- Restrict an actual native trace-preserving automorphism to the real trace kernel. -/
def automorphismV (g : CompactAutomorphism) : V ≃ₗ[ℝ] V where
  toFun x := ⟨g.equiv (x : Albert), by
    change trace (g.equiv (x : Albert)) = 0
    rw [g.map_trace]
    exact trace_V x⟩
  invFun x := ⟨g.symm.equiv (x : Albert), by
    change trace (g.symm.equiv (x : Albert)) = 0
    rw [g.symm.map_trace]
    exact trace_V x⟩
  left_inv x := by
    apply Subtype.ext
    exact g.equiv.symm_apply_apply (x : Albert)
  right_inv x := by
    apply Subtype.ext
    exact g.equiv.apply_symm_apply (x : Albert)
  map_add' x y := by apply Subtype.ext; exact map_add g.equiv _ _
  map_smul' r x := by
    apply Subtype.ext
    change g.equiv (r • (x : Albert)) = r • g.equiv (x : Albert)
    simpa only [RingHom.id_apply] using map_smul g.equiv r (x : Albert)

@[simp] theorem automorphismV_coe (g : CompactAutomorphism) (x : V) :
    (automorphismV g x : Albert) = g.equiv (x : Albert) := rfl

@[simp] theorem automorphismV_comp_apply (g f : CompactAutomorphism) (x : V) :
    automorphismV (g.comp f) x = automorphismV g (automorphismV f x) := by
  apply Subtype.ext
  rfl

/-- The specified metric scale remains trace/3 under the actual automorphism. -/
theorem automorphismV_gA (g : CompactAutomorphism) (x y : V) :
    gA (automorphismV g x) (automorphismV g y) = gA x y := by
  exact congrArg (fun r : ℝ => r / 3) (g.inner_map (x : Albert) (y : Albert))

theorem automorphismV_project (g : CompactAutomorphism) (x : Albert) :
    automorphismV g (project x) = project (g.equiv x) := by
  apply Subtype.ext
  exact g.map_traceless x

/-- Native projected Jordan multiplication is transported, never postulated. -/
theorem automorphismV_KA (g : CompactAutomorphism) (x y : V) :
    automorphismV g (KA x y) = KA (automorphismV g x) (automorphismV g y) := by
  apply Subtype.ext
  change g.equiv (traceless (jordan (x : Albert) (y : Albert))) =
    traceless (jordan (g.equiv (x : Albert)) (g.equiv (y : Albert)))
  rw [g.map_traceless, g.map_jordan]

/-- Pullback of an arbitrary genuine symmetric trilinear form by a real equivalence. -/
def pullbackCubic (T : V ≃ₗ[ℝ] V) (B : SymmetricCubic) : SymmetricCubic where
  form :=
    { toFun := fun x =>
        { toFun := fun y => (B.form (T x) (T y)).comp T.toLinearMap
          map_add' y z := by
            apply LinearMap.ext
            intro v
            change B.form (T x) (T (y + z)) (T v) =
              B.form (T x) (T y) (T v) + B.form (T x) (T z) (T v)
            rw [map_add, map_add, LinearMap.add_apply]
          map_smul' r y := by
            simp only [RingHom.id_apply]
            apply LinearMap.ext
            intro v
            change B.form (T x) (T (r • y)) (T v) =
              r * B.form (T x) (T y) (T v)
            rw [map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul] }
      map_add' x y := by
        apply LinearMap.ext
        intro z
        apply LinearMap.ext
        intro v
        change B.form (T (x + y)) (T z) (T v) =
          B.form (T x) (T z) (T v) + B.form (T y) (T z) (T v)
        rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply]
      map_smul' r x := by
        simp only [RingHom.id_apply]
        apply LinearMap.ext
        intro y
        apply LinearMap.ext
        intro z
        change B.form (T (r • x)) (T y) (T z) =
          r * B.form (T x) (T y) (T z)
        rw [map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply,
          smul_eq_mul] }
  swap12 x y z := B.swap12 (T x) (T y) (T z)
  swap23 x y z := B.swap23 (T x) (T y) (T z)

@[simp] theorem pullbackCubic_form (T : V ≃ₗ[ℝ] V) (B : SymmetricCubic)
    (x y z : V) : (pullbackCubic T B).form x y z = B.form (T x) (T y) (T z) := rfl

/-- Raising an index commutes with pullback because the actual metric is preserved.
The transformed unknown is B(Tx,Ty,Tz); B itself is unrestricted. -/
theorem automorphismV_KB_pullback (g : CompactAutomorphism) (B : SymmetricCubic)
    (x y : V) :
    automorphismV g (KB (pullbackCubic (automorphismV g) B) x y) =
      KB B (automorphismV g x) (automorphismV g y) := by
  apply metricDual.injective
  apply LinearMap.ext
  intro z
  obtain ⟨w, rfl⟩ := (automorphismV g).surjective z
  change gA (automorphismV g (KB (pullbackCubic (automorphismV g) B) x y))
      (automorphismV g w) =
    gA (KB B (automorphismV g x) (automorphismV g y)) (automorphismV g w)
  rw [automorphismV_gA, KB_pairing, KB_pairing, pullbackCubic_form]

/-- Transfer one proved scalar action of the pullback to the original unknown. -/
theorem scalar_action_of_pullback (g : CompactAutomorphism) (B : SymmetricCubic)
    (x y : V) (r : ℝ)
    (hxy : KB (pullbackCubic (automorphismV g) B) x y = r • y) :
    KB B (automorphismV g x) (automorphismV g y) =
      r • automorphismV g y := by
  rw [← automorphismV_KB_pullback, hxy, map_smul]

/-- Reference cubic invariance is derived from KA and the scaled metric. -/
theorem automorphismV_referenceCubic (g : CompactAutomorphism) (x y z : V) :
    referenceCubic.form (automorphismV g x) (automorphismV g y)
      (automorphismV g z) = referenceCubic.form x y z := by
  change gA (KA (automorphismV g x) (automorphismV g y)) (automorphismV g z) =
    gA (KA x y) z
  rw [← automorphismV_KA, automorphismV_gA]

private theorem intertwines_operatorComm (T : V ≃ₗ[ℝ] V)
    (P Q R S : V →ₗ[ℝ] V)
    (hP : ∀ v, T (P v) = R (T v)) (hQ : ∀ v, T (Q v) = S (T v))
    (v : V) : T (operatorComm P Q v) = operatorComm R S (T v) := by
  change T (P (Q v) - Q (P v)) = R (S (T v)) - S (R (T v))
  simp only [map_sub, hP, hQ]

/-- The actual reference-q tensor transports with the native automorphism. -/
theorem automorphismV_q_reference (g : CompactAutomorphism) (x y v : V) :
    automorphismV g (q referenceCubic x y v) =
      q referenceCubic (automorphismV g x) (automorphismV g y)
        (automorphismV g v) := by
  simp only [q, KB_referenceCubic]
  exact intertwines_operatorComm (automorphismV g)
    (KA x) (KA y) (KA (automorphismV g x)) (KA (automorphismV g y))
    (automorphismV_KA g x) (automorphismV_KA g y) v

/-- Literal A(q) covariance for the pulled-back arbitrary cubic, pointwise. -/
theorem automorphismV_A_q_pullback (g : CompactAutomorphism) (B : SymmetricCubic)
    (x y z v : V) :
    automorphismV g (A (q referenceCubic) (pullbackCubic (automorphismV g) B)
      x y z v) =
      A (q referenceCubic) B (automorphismV g x) (automorphismV g y)
        (automorphismV g z) (automorphismV g v) := by
  have hterm (u w s : V) :
      automorphismV g
        (operatorComm (KB (pullbackCubic (automorphismV g) B) u)
          (q referenceCubic w s) v) =
        operatorComm (KB B (automorphismV g u))
          (q referenceCubic (automorphismV g w) (automorphismV g s))
          (automorphismV g v) :=
    intertwines_operatorComm (automorphismV g)
      (KB (pullbackCubic (automorphismV g) B) u) (q referenceCubic w s)
      (KB B (automorphismV g u))
      (q referenceCubic (automorphismV g w) (automorphismV g s))
      (automorphismV_KB_pullback g B u) (automorphismV_q_reference g w s) v
  change automorphismV g
      (operatorComm (KB (pullbackCubic (automorphismV g) B) x)
          (q referenceCubic y z) v +
        operatorComm (KB (pullbackCubic (automorphismV g) B) y)
          (q referenceCubic z x) v +
        operatorComm (KB (pullbackCubic (automorphismV g) B) z)
          (q referenceCubic x y) v) =
      operatorComm (KB B (automorphismV g x))
          (q referenceCubic (automorphismV g y) (automorphismV g z))
          (automorphismV g v) +
        operatorComm (KB B (automorphismV g y))
          (q referenceCubic (automorphismV g z) (automorphismV g x))
          (automorphismV g v) +
        operatorComm (KB B (automorphismV g z))
          (q referenceCubic (automorphismV g x) (automorphismV g y))
          (automorphismV g v)
  rw [map_add, map_add]
  exact congrArg₂ (fun a b : V => a + b)
    (congrArg₂ (fun a b : V => a + b) (hterm x y z) (hterm y z x))
    (hterm z x y)

/-- The sole original Jacobi-kernel hypothesis is stable under actual pullback. -/
theorem A_q_pullback_zero (g : CompactAutomorphism) (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) :
    A (q referenceCubic) (pullbackCubic (automorphismV g) B) = 0 := by
  funext x y z
  apply LinearMap.ext
  intro v
  apply (automorphismV g).injective
  change automorphismV g
    (A (q referenceCubic) (pullbackCubic (automorphismV g) B) x y z v) =
      automorphismV g 0
  rw [automorphismV_A_q_pullback, hB]
  simp only [Pi.zero_apply, LinearMap.zero_apply, map_zero]

namespace FixedFrame

/-- Concrete native cyclic permutation: first swap01, then swap02. -/
def cyclicAutomorphism : CompactAutomorphism :=
  realSwap02Automorphism.comp realSwap01Automorphism

def cyclicV : V ≃ₗ[ℝ] V := automorphismV cyclicAutomorphism

theorem cyclicAutomorphism_coordinates (x : Albert) :
    cyclicAutomorphism.equiv x =
      ⟨x.d2,x.d0,x.d1,octConj x.o02,octConj x.o12,x.o01⟩ := by
  change realConjugateAlbert realSwap02 (realConjugateAlbert realSwap01 x) = _
  rw [realSwap01_coordinates, realSwap02_coordinates, octConj_conj]

theorem cyclicV_coordinates (x : V) :
    (cyclicV x : Albert) =
      ⟨(x : Albert).d2,(x : Albert).d0,(x : Albert).d1,
        octConj (x : Albert).o02,octConj (x : Albert).o12,(x : Albert).o01⟩ :=
  cyclicAutomorphism_coordinates (x : Albert)

@[simp] theorem cyclicV_h0 : cyclicV (h 0) = h 1 := by
  apply Subtype.ext
  rw [cyclicV_coordinates]
  apply Albert.ext <;> norm_num [h, e, unit, octConj]

@[simp] theorem cyclicV_h1 : cyclicV (h 1) = h 2 := by
  apply Subtype.ext
  rw [cyclicV_coordinates]
  apply Albert.ext <;> norm_num [h, e, unit, octConj]

@[simp] theorem cyclicV_h2 : cyclicV (h 2) = h 0 := by
  apply Subtype.ext
  rw [cyclicV_coordinates]
  apply Albert.ext <;> norm_num [h, e, unit, octConj]

@[simp] theorem cyclicV_X01 (u : Octonion) : cyclicV (X01 u) = X12 u := by
  apply Subtype.ext
  rw [cyclicV_coordinates]
  apply Albert.ext <;> simp [X01, X12, octConj]

@[simp] theorem cyclicV_X02 (u : Octonion) :
    cyclicV (X02 u) = X01 (octConj u) := by
  apply Subtype.ext
  rw [cyclicV_coordinates]
  apply Albert.ext <;> simp [X01, X02, octConj]

@[simp] theorem cyclicV_X12 (u : Octonion) :
    cyclicV (X12 u) = X02 (octConj u) := by
  apply Subtype.ext
  rw [cyclicV_coordinates]
  apply Albert.ext <;> simp [X02, X12, octConj]

/-- Concrete order3 identity on all actual tracefree vectors. -/
theorem cyclicV_cube (v : V) : cyclicV (cyclicV (cyclicV v)) = v := by
  apply Subtype.ext
  simp only [cyclicV_coordinates, octConj_conj]

end FixedFrame
end
end AlbertRecognition
