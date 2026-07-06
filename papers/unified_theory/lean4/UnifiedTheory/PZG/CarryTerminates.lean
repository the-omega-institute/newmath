import UnifiedTheory.PZG.Carry
import UnifiedTheory.Foundation.Rewriting

namespace UnifiedTheory

open Rewriting

/--
Zeckendorf 进位重写终止:lex(长度, 指标和)在合并/加倍两规则下严格降。
This is the termination half of theorem 5.7 algorithmic normalization.
-/
theorem CarryStep.terminates : Terminates CarryStep := by
  let μ : List ℕ → ℕ × ℕ := fun l => (l.length, l.sum)
  have hstep :
      ∀ l l', CarryStep l l' →
        Prod.Lex (· < ·) (· < ·) (μ l') (μ l) := by
    intro l l' h
    cases h with
    | merge p q i =>
        apply Prod.Lex.left
        simp
    | double p q i =>
        dsimp [μ]
        simp
        omega
  have hwf :
      WellFounded (fun l' l : List ℕ =>
        Prod.Lex (· < ·) (· < ·) (μ l') (μ l)) :=
    InvImage.wf μ (WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf)
  exact Subrelation.wf (fun {a b} h => hstep b a h) hwf

end UnifiedTheory
