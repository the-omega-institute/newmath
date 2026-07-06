import BEDC.FKernel.Cont.Units

namespace BEDC.Derived.StationaryWindowSealExhaustionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

def StationaryWindowSealExhaustionCarrier (Q S R D W E H C P N : BHist) : Prop :=
  Cont Q BHist.Empty S ∧
    Cont S BHist.Empty R ∧
      Cont R BHist.Empty D ∧
        Cont D BHist.Empty W ∧
          Cont E BHist.Empty Q ∧
            hsame H C ∧
              hsame P N

theorem StationaryWindowSealExhaustionCarrier_l10_handoff
    {Q S R D W E H C P N : BHist} :
    StationaryWindowSealExhaustionCarrier Q S R D W E H C P N →
      hsame S Q ∧ hsame R Q ∧ hsame D Q ∧ hsame W Q ∧ hsame E Q ∧
        hsame H C ∧ hsame P N := by
  -- BEDC touchpoint anchor: BHist Cont
  intro h
  cases h with
  | intro hQS hrest =>
      cases hrest with
      | intro hSR hrest =>
          cases hrest with
          | intro hRD hrest =>
              cases hrest with
              | intro hDW hrest =>
                  cases hrest with
                  | intro hEQ hrest =>
                      cases hrest with
                      | intro hHC hPN =>
                          have hSQ : hsame S Q := cont_right_unit_result hQS
                          have hRS : hsame R S := cont_right_unit_result hSR
                          have hDR : hsame D R := cont_right_unit_result hRD
                          have hWD : hsame W D := cont_right_unit_result hDW
                          have hQE : hsame Q E := cont_right_unit_result hEQ
                          have hRQ : hsame R Q := hsame_trans hRS hSQ
                          have hDQ : hsame D Q := hsame_trans hDR hRQ
                          have hWQ : hsame W Q := hsame_trans hWD hDQ
                          have hEQ' : hsame E Q := hsame_symm hQE
                          exact
                            ⟨hSQ, hRQ, hDQ, hWQ, hEQ', hHC, hPN⟩

theorem StationaryWindowSealExhaustionCarrier_exhaustion_row_obligations
    {Q S R D W E H C P N : BHist} :
    StationaryWindowSealExhaustionCarrier Q S R D W E H C P N ->
      Cont Q BHist.Empty S ∧ Cont S BHist.Empty R ∧ Cont R BHist.Empty D ∧
        Cont D BHist.Empty W ∧ Cont E BHist.Empty Q ∧ hsame S Q ∧ hsame R Q ∧
          hsame D Q ∧ hsame W Q ∧ hsame E Q ∧ hsame H C ∧ hsame P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro carrier
  cases carrier with
  | intro qToS rest =>
      cases rest with
      | intro sToR rest =>
          cases rest with
          | intro rToD rest =>
              cases rest with
              | intro dToW rest =>
                  cases rest with
                  | intro eToQ rest =>
                      cases rest with
                      | intro hToC pToN =>
                          have handoff :
                              hsame S Q ∧ hsame R Q ∧ hsame D Q ∧ hsame W Q ∧
                                hsame E Q ∧ hsame H C ∧ hsame P N :=
                            StationaryWindowSealExhaustionCarrier_l10_handoff
                              ⟨qToS, sToR, rToD, dToW, eToQ, hToC, pToN⟩
                          obtain ⟨sameS, sameR, sameD, sameW, sameE, sameH, sameP⟩ :=
                            handoff
                          exact
                            ⟨qToS, sToR, rToD, dToW, eToQ, sameS, sameR, sameD,
                              sameW, sameE, sameH, sameP⟩

end BEDC.Derived.StationaryWindowSealExhaustionUp
