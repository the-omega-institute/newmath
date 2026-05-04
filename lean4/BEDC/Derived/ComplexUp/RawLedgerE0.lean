import BEDC.Derived.ComplexUp

namespace BEDC.Derived.ComplexUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ComplexHistoryLedgerPolicy_e0_raw_absurd {tail visible : BHist} :
    ComplexHistoryLedgerPolicy (BHist.e0 tail) visible -> False := by
  intro ledger
  have components := ComplexHistoryCarrier_positive_components ledger.left
  cases components with
  | intro real rest =>
      cases rest with
      | intro imag data =>
          cases data with
          | intro _realCarrier data =>
              cases data with
              | intro _imagCarrier data =>
                  cases data with
                  | intro cont data =>
                      cases data with
                      | intro _positiveReal positiveImag =>
                          have resultCases := cont_e0_result_inversion cont
                          cases resultCases with
                          | inl emptyCase =>
                              cases emptyCase with
                              | intro imagEmpty _sameReal =>
                                  cases imagEmpty
                                  exact RatUp.PositiveUnaryDenominator_not_empty
                                    positiveImag (hsame_refl BHist.Empty)
                          | inr visibleCase =>
                              cases visibleCase with
                              | intro imagTail fields =>
                                  cases fields with
                                  | intro imagVisible _tailCont =>
                                      cases imagVisible
                                      exact RatUp.PositiveUnaryDenominator_e0_absurd
                                        positiveImag

end BEDC.Derived.ComplexUp
