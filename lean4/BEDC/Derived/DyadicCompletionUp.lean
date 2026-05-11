import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DyadicCompletionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def DyadicCompletionFiniteWindowSource (row : BHist) : Prop :=
  exists left right midpoint refinement endpoint : BHist,
    Cont left right midpoint ∧
      Cont midpoint refinement endpoint ∧ hsame row endpoint

def DyadicCompletionFiniteWindowPattern (row : BHist) : Prop :=
  exists left right midpoint endpoint : BHist,
    Cont left right midpoint ∧ hsame row endpoint

def DyadicCompletionFiniteWindowLedger (row : BHist) : Prop :=
  exists midpoint refinement endpoint : BHist,
    Cont midpoint refinement endpoint ∧ hsame row endpoint

theorem DyadicCompletionPacket_namecert_obligation_surface :
    SemanticNameCert DyadicCompletionFiniteWindowSource DyadicCompletionFiniteWindowPattern
      DyadicCompletionFiniteWindowLedger hsame := by
  have source : DyadicCompletionFiniteWindowSource BHist.Empty := by
    exact Exists.intro BHist.Empty
      (Exists.intro BHist.Empty
        (Exists.intro BHist.Empty
          (Exists.intro BHist.Empty
            (Exists.intro BHist.Empty
              (And.intro (cont_left_unit BHist.Empty)
                (And.intro (cont_left_unit BHist.Empty) (hsame_refl BHist.Empty)))))))
  constructor
  · constructor
    · exact Exists.intro BHist.Empty source
    · intro row _source
      exact hsame_refl row
    · intro left right sameRows
      exact hsame_symm sameRows
    · intro left middle right sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro left right sameRows sourceLeft
      cases sourceLeft with
      | intro leftWindow leftData =>
          cases leftData with
          | intro rightWindow rightData =>
              cases rightData with
              | intro midpoint midpointData =>
                  cases midpointData with
                  | intro refinement refinementData =>
                      cases refinementData with
                      | intro endpoint packet =>
                          exact Exists.intro leftWindow
                            (Exists.intro rightWindow
                              (Exists.intro midpoint
                                (Exists.intro refinement
                                  (Exists.intro endpoint
                                    (And.intro packet.left
                                      (And.intro packet.right.left
                                        (hsame_trans (hsame_symm sameRows)
                                          packet.right.right)))))))
  · intro row sourceRow
    cases sourceRow with
    | intro left leftData =>
        cases leftData with
        | intro right rightData =>
            cases rightData with
            | intro midpoint midpointData =>
                cases midpointData with
                | intro refinement refinementData =>
                    cases refinementData with
                    | intro endpoint packet =>
                        exact Exists.intro left
                          (Exists.intro right
                            (Exists.intro midpoint
                              (Exists.intro endpoint
                                (And.intro packet.left packet.right.right))))
  · intro row sourceRow
    cases sourceRow with
    | intro left leftData =>
        cases leftData with
        | intro right rightData =>
            cases rightData with
            | intro midpoint midpointData =>
                cases midpointData with
                | intro refinement refinementData =>
                    cases refinementData with
                    | intro endpoint packet =>
                        exact Exists.intro midpoint
                          (Exists.intro refinement
                            (Exists.intro endpoint
                              (And.intro packet.right.left packet.right.right)))

end BEDC.Derived.DyadicCompletionUp
