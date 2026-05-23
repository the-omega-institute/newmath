import BEDC.Derived.MeasureUp

namespace BEDC.Derived.MeasureUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem MeasureRootRealStreamCarrierRegularity
    {event stream endpoint total ledger ledgerPrime : BHist} :
    MeasureZeroBHistCarrier event ->
      MeasureZeroBHistCarrier stream ->
        Cont event stream endpoint ->
          Cont endpoint BHist.Empty total ->
            hsame ledger endpoint ->
              hsame ledger ledgerPrime ->
                MeasureZeroBHistCarrier endpoint ∧ MeasureZeroBHistCarrier total ∧
                  MeasureZeroBHistClassifier ledger ledgerPrime ∧ UnaryHistory total ∧
                    hsame total endpoint := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro eventZero streamZero eventStreamEndpoint endpointTotal ledgerEndpoint
    ledgerLedgerPrime
  have endpointZero : MeasureZeroBHistCarrier endpoint :=
    cont_respects_hsame eventZero streamZero eventStreamEndpoint (cont_left_unit BHist.Empty)
  have totalEndpoint : hsame total endpoint :=
    cont_right_unit_result endpointTotal
  have totalZero : MeasureZeroBHistCarrier total :=
    hsame_trans totalEndpoint endpointZero
  have ledgerZero : MeasureZeroBHistCarrier ledger :=
    hsame_trans ledgerEndpoint endpointZero
  have ledgerPrimeZero : MeasureZeroBHistCarrier ledgerPrime :=
    hsame_trans (hsame_symm ledgerLedgerPrime) ledgerZero
  have ledgerClassifier : MeasureZeroBHistClassifier ledger ledgerPrime :=
    ⟨ledgerZero, ledgerPrimeZero, ledgerLedgerPrime⟩
  have totalUnary : UnaryHistory total :=
    unary_transport unary_empty (hsame_symm totalZero)
  exact ⟨endpointZero, totalZero, ledgerClassifier, totalUnary, totalEndpoint⟩

end BEDC.Derived.MeasureUp
