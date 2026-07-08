import UnifiedTheory.PZG.CarryMultiset
import UnifiedTheory.Foundation.Rewriting

namespace UnifiedTheory

open Rewriting

/--
多重集进位重写终止:lex(card, sum) 在合并/加倍下严格降。
merge 严格降低 card; double 保持 card 并严格降低 sum。
-/
theorem CarryStepM.terminates : Terminates CarryStepM := by
  let μ : Multiset ℕ → ℕ × ℕ := fun m => (Multiset.card m, m.sum)
  have hstep :
      ∀ m m', CarryStepM m m' →
        Prod.Lex (· < ·) (· < ·) (μ m') (μ m) := by
    intro m m' h
    cases h with
    | merge rest i =>
        dsimp [μ]
        apply Prod.Lex.left
        simp [Multiset.card_cons]
    | double rest i =>
        dsimp [μ]
        simp only [Multiset.card_cons]
        apply Prod.Lex.right
        simp [Multiset.sum_cons]
        omega
  have hwf :
      WellFounded (fun m' m : Multiset ℕ =>
        Prod.Lex (· < ·) (· < ·) (μ m') (μ m)) :=
    InvImage.wf μ (WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf)
  exact Subrelation.wf (fun {a b} h => hstep b a h) hwf

end UnifiedTheory
