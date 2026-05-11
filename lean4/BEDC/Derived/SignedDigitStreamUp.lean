import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.SignedDigitStreamUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def SignedDigitStreamFiniteWindowSource (row : BHist) : Prop :=
  exists schedule normalized carry hiddenTail boundary : BHist,
    Cont schedule normalized carry ∧
      Cont carry hiddenTail boundary ∧ hsame row (BHist.e1 boundary)

def SignedDigitStreamFiniteWindowPattern (row : BHist) : Prop :=
  exists schedule normalized carry boundary : BHist,
    Cont schedule normalized carry ∧ hsame row (BHist.e1 boundary)

def SignedDigitStreamWindowLedger (row : BHist) : Prop :=
  exists carry hiddenTail boundary : BHist,
    Cont carry hiddenTail boundary ∧ hsame row (BHist.e1 boundary)

theorem SignedDigitStreamPacket_namecert_obligation_surface :
    SemanticNameCert SignedDigitStreamFiniteWindowSource SignedDigitStreamFiniteWindowPattern
      SignedDigitStreamWindowLedger hsame := by
  have source : SignedDigitStreamFiniteWindowSource (BHist.e1 BHist.Empty) := by
    exact Exists.intro BHist.Empty
      (Exists.intro BHist.Empty
        (Exists.intro BHist.Empty
          (Exists.intro BHist.Empty
            (Exists.intro BHist.Empty
              (And.intro (cont_left_unit BHist.Empty)
                (And.intro (cont_left_unit BHist.Empty)
                  (hsame_refl (BHist.e1 BHist.Empty))))))))
  constructor
  · constructor
    · exact Exists.intro (BHist.e1 BHist.Empty) source
    · intro row _source
      exact hsame_refl row
    · intro left right sameRows
      exact hsame_symm sameRows
    · intro left middle right sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro left right sameRows sourceLeft
      cases sourceLeft with
      | intro schedule scheduleData =>
          cases scheduleData with
          | intro normalized normalizedData =>
              cases normalizedData with
              | intro carry carryData =>
                  cases carryData with
                  | intro hiddenTail hiddenTailData =>
                      cases hiddenTailData with
                      | intro boundary packet =>
                          exact Exists.intro schedule
                            (Exists.intro normalized
                              (Exists.intro carry
                                (Exists.intro hiddenTail
                                  (Exists.intro boundary
                                    (And.intro packet.left
                                      (And.intro packet.right.left
                                        (hsame_trans (hsame_symm sameRows)
                                          packet.right.right)))))))
  · intro row sourceRow
    cases sourceRow with
    | intro schedule scheduleData =>
        cases scheduleData with
        | intro normalized normalizedData =>
            cases normalizedData with
            | intro carry carryData =>
                cases carryData with
                | intro hiddenTail hiddenTailData =>
                    cases hiddenTailData with
                    | intro boundary packet =>
                        exact Exists.intro schedule
                          (Exists.intro normalized
                            (Exists.intro carry
                              (Exists.intro boundary
                                (And.intro packet.left packet.right.right))))
  · intro row sourceRow
    cases sourceRow with
    | intro schedule scheduleData =>
        cases scheduleData with
        | intro normalized normalizedData =>
            cases normalizedData with
            | intro carry carryData =>
                cases carryData with
                | intro hiddenTail hiddenTailData =>
                    cases hiddenTailData with
                    | intro boundary packet =>
                        exact Exists.intro carry
                          (Exists.intro hiddenTail
                            (Exists.intro boundary
                              (And.intro packet.right.left packet.right.right)))

end BEDC.Derived.SignedDigitStreamUp
