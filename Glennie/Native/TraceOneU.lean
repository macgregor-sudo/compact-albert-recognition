/- Classical proof guidance: Garibaldi–Petersson–Racine, January 19 2026 draft,
37.1 / Proposition 37.2(b), PDF 380–381 / printed 362–363, and 37.4,
PDF 382–383 / printed 364–365. No book text or proof code is copied.
This native cubic-residual proof does not assume elementary p#=0 or book U.
Book circle is twice native jordan; all operations below remain native.
The imported general CubicJordan port retains its upstream Apache-2.0 license
and provenance in THIRD-PARTY-NOTICES.md and licenses/albert-lean-CubicJordan-LICENSE. -/
module
public import Glennie.Native.CubicIdentity
public import Glennie.BasicLaws

@[expose] public section
namespace Glennie
noncomputable section

set_option maxHeartbeats 2000000

/-- A trace-one idempotent has a rank-one quadratic representation. -/
theorem traceOne_idempotent_U (p q : Albert)
    (hp : jordan p p = p) (ht : trace p = 1) : U p q = inner p q • p := by
  have hc : ∀ a b, jordanLinear a b = jordanLinear b a := fun a b => by
    simpa only [jordanLinear_apply] using jordan_comm a b
  have ha : ∀ a b c, traceLinear (jordanLinear (jordanLinear a b) c) =
      traceLinear (jordanLinear a (jordanLinear b c)) := fun a b c => by
    simp only [jordanLinear_apply, traceLinear_apply]
    exact inner_jordan_associative a b c
  have hlin := CubicJordan.linearResidual_eq_zero jordanLinear traceLinear 1
    hc ha cubicResidual_eq_zero p q
  simp only [CubicJordan.linearResidual, jordanLinear_apply, traceLinear_apply] at hlin
  simp only [hp, ht] at hlin
  change (4 : ℝ) • jordan p (jordan p q) + (2 : ℝ) • jordan p q -
    (2 * trace q) • p - (4 * 1 : ℝ) • jordan p q +
    (2 * 1 * trace q - 2 * inner p q) • p +
    ((1 : ℝ) ^ 2 - 1) • q -
    (((1 : ℝ) ^ 2 - 1) * trace q - 2 * 1 * inner p q +
      2 * inner p q) • (1 : Albert) = 0 at hlin
  have heq : (2 : ℝ) • (U p q - inner p q • p) = 0 := by
    calc
      _ = (4 : ℝ) • jordan p (jordan p q) + (2 : ℝ) • jordan p q -
        (2 * trace q) • p - (4 * 1 : ℝ) • jordan p q +
        (2 * 1 * trace q - 2 * inner p q) • p +
        ((1 : ℝ) ^ 2 - 1) • q -
        (((1 : ℝ) ^ 2 - 1) * trace q - 2 * 1 * inner p q +
          2 * inner p q) • (1 : Albert) := by unfold U; rw [hp]; module
      _ = 0 := hlin
  have hhalf := congrArg (fun z : Albert => (1 / 2 : ℝ) • z) heq
  simpa only [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num,
    one_smul, smul_zero, sub_eq_zero] using hhalf


end
end Glennie
