import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
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

theorem SheafConsumerAccessTrace_no_feedback
    {root feedback tail : BHist} {trace : List BHist} :
    SheafConsumerAccessTrace root trace -> List.Mem feedback trace ->
      Cont feedback (BHist.e0 tail) root -> False := by
  intro trace _feedbackMem feedbackRow
  have rootUnary : UnaryHistory root := trace.left
  have rootZero : hsame root (BHist.e0 (append feedback tail)) := feedbackRow
  exact unary_no_zero_extension (unary_transport rootUnary rootZero)

theorem SheafConsumerAccessTrace_root_access_factorization
    {root row endpoint : BHist} {trace : List BHist}
    {landing : SheafRootFaceLanding} :
    SheafConsumerAccessTrace root (row :: trace) ->
      SheafRootFaceRead row endpoint landing ->
        UnaryHistory root ∧ UnaryHistory row ∧ SheafConsumerAccessTrace root trace ∧
          (landing = SheafRootFaceLanding.coverMembership ∨
            landing = SheafRootFaceLanding.restrictionRoute ∨
              landing = SheafRootFaceLanding.localityGluingRefinement) := by
  intro consumerTrace rootRead
  have rowUnary : UnaryHistory row :=
    consumerTrace.right row (List.Mem.head trace)
  have tailTrace : SheafConsumerAccessTrace root trace :=
    And.intro consumerTrace.left
      (by
        intro tailRow tailMem
        exact consumerTrace.right tailRow (List.Mem.tail row tailMem))
  exact And.intro consumerTrace.left
    (And.intro rowUnary
      (And.intro tailTrace (SheafRootFaceRead_coverage rootRead)))

end BEDC.Derived.SheafUp
