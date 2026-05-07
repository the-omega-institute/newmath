import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem SheafConsumerAccessTrace_append_exhaustion {root : BHist} {left right : List BHist} :
    SheafConsumerAccessTrace root (left ++ right) ->
      UnaryHistory root ∧ SheafConsumerAccessTrace root left ∧
        SheafConsumerAccessTrace root right := by
  intro trace
  induction left with
  | nil =>
      exact And.intro trace.left
        (And.intro
          (And.intro trace.left
            (by
              intro row rowMem
              cases rowMem))
          trace)
  | cons head tail ih =>
      have headUnary : UnaryHistory head :=
        trace.right head (List.Mem.head (tail ++ right))
      have tailTrace : SheafConsumerAccessTrace root (tail ++ right) :=
        And.intro trace.left
          (by
            intro row rowMem
            exact trace.right row (List.Mem.tail head rowMem))
      have splitTail := ih tailTrace
      exact And.intro trace.left
        (And.intro
          (And.intro trace.left
            (by
              intro row rowMem
              cases rowMem with
              | head =>
                  exact headUnary
              | tail _ tailMem =>
                  exact splitTail.right.left.right row tailMem))
          splitTail.right.right)

theorem SheafConsumerAccessTrace_append_membership_coverage
    {root row : BHist} {left right : List BHist} :
    SheafConsumerAccessTrace root left -> SheafConsumerAccessTrace root right ->
      List.Mem row (left ++ right) ->
        (List.Mem row left ∨ List.Mem row right) ∧ UnaryHistory row := by
  intro leftTrace rightTrace rowMem
  induction left with
  | nil =>
      exact And.intro (Or.inr rowMem) (rightTrace.right row rowMem)
  | cons head tail ih =>
      cases rowMem with
      | head =>
          exact And.intro (Or.inl (List.Mem.head tail))
            (leftTrace.right row (List.Mem.head tail))
      | tail _ tailMem =>
          have tailTrace : SheafConsumerAccessTrace root tail :=
            And.intro leftTrace.left
              (by
                intro tailRow tailRowMem
                exact leftTrace.right tailRow (List.Mem.tail head tailRowMem))
          have tailCoverage := ih tailTrace tailMem
          cases tailCoverage.left with
          | inl tailLeft =>
              exact And.intro (Or.inl (List.Mem.tail head tailLeft)) tailCoverage.right
          | inr rightMem =>
              exact And.intro (Or.inr rightMem) tailCoverage.right

end BEDC.Derived.SheafUp
