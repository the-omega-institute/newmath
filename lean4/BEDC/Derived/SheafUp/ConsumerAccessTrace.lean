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

end BEDC.Derived.SheafUp
