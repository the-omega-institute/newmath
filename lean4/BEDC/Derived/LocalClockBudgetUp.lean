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

theorem LocalClockBudget_route_determinacy
    {H T W B L Q P N H' T' W' B' L' Q' P' N' : BHist} :
    LocalClockBudgetCarrier H T W B L Q P N →
      LocalClockBudgetCarrier H' T' W' B' L' Q' P' N' →
        [H, T, W, B, L, Q, P, N] = [H', T', W', B', L', Q', P', N'] →
          hsame H H' ∧ hsame T T' ∧ hsame W W' ∧ hsame B B' ∧ hsame L L' ∧
            hsame Q Q' ∧ hsame P P' ∧ hsame N N' := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  intro _ _ rows
  injection rows with hH restT
  injection restT with hT restW
  injection restW with hW restB
  injection restB with hB restL
  injection restL with hL restQ
  injection restQ with hQ restP
  injection restP with hP restN
  injection restN with hN _
  cases hH
  cases hT
  cases hW
  cases hB
  cases hL
  cases hQ
  cases hP
  cases hN
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · constructor
          · rfl
          · constructor
            · rfl
            · constructor
              · rfl
              · rfl

end BEDC.Derived.LocalClockBudgetUp
