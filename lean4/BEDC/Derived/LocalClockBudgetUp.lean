import BEDC.FKernel.Cont

namespace BEDC.Derived.LocalClockBudgetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

inductive LocalClockBudgetUp : Type where
  | mk : (H T W B L Q P N : BHist) → LocalClockBudgetUp

def localClockBudgetFields : LocalClockBudgetUp → List BHist
  -- BEDC touchpoint anchor: BHist hsame Cont
  | LocalClockBudgetUp.mk H T W B L Q P N => [H, T, W, B, L, Q, P, N]

def LocalClockBudgetCarrier (H T W B L Q P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist hsame Cont
  hsame H H ∧ hsame T T ∧ hsame W W ∧ hsame B B ∧ hsame L L ∧ hsame Q Q ∧
    hsame P P ∧ hsame N N ∧
      localClockBudgetFields (LocalClockBudgetUp.mk H T W B L Q P N) =
        [H, T, W, B, L, Q, P, N]

def LocalClockBudgetWindowSurface (H T W B Q : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist hsame Cont
  Cont BHist.Empty T H ∧ Cont T W Q ∧ hsame B B

theorem LocalClockBudgetWindow_totality {H T W B L Q P N : BHist} :
    LocalClockBudgetCarrier H T W B L Q P N →
      Cont BHist.Empty T H →
        Cont T W Q →
          LocalClockBudgetWindowSurface H T W B Q ∧
            localClockBudgetFields (LocalClockBudgetUp.mk H T W B L Q P N) =
              [H, T, W, B, L, Q, P, N] := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  intro carrier streamRoute windowRoute
  constructor
  · constructor
    · exact streamRoute
    · constructor
      · exact windowRoute
      · rfl
  · exact carrier.right.right.right.right.right.right.right.right

end BEDC.Derived.LocalClockBudgetUp
