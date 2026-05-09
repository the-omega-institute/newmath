import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.RingOfIntegersUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

inductive RingOfIntegersEquationLedger : List BHist -> BHist -> Prop where
  | nil {endpoint : BHist} :
      hsame endpoint BHist.Empty -> RingOfIntegersEquationLedger [] endpoint
  | cons {equation tail endpoint : BHist} {rest : List BHist} :
      UnaryHistory equation -> RingOfIntegersEquationLedger rest tail ->
        Cont equation tail endpoint -> RingOfIntegersEquationLedger (equation :: rest) endpoint

theorem RingOfIntegersEquationLedger_endpoint_transport
    {ledger : List BHist} {endpoint endpoint' : BHist} :
    RingOfIntegersEquationLedger ledger endpoint -> hsame endpoint' endpoint ->
      RingOfIntegersEquationLedger ledger endpoint' ∧
        (hsame endpoint BHist.Empty -> hsame endpoint' BHist.Empty) := by
  intro ledgerSpine sameEndpoint
  induction ledgerSpine with
  | nil endpointEmpty =>
      exact And.intro
        (RingOfIntegersEquationLedger.nil (hsame_trans sameEndpoint endpointEmpty))
        (fun endpointWasEmpty => hsame_trans sameEndpoint endpointWasEmpty)
  | cons equationUnary restSpine cont ih =>
      exact And.intro
        (RingOfIntegersEquationLedger.cons equationUnary restSpine
          (cont_result_hsame_transport cont (hsame_symm sameEndpoint)))
        (fun endpointWasEmpty => hsame_trans sameEndpoint endpointWasEmpty)

end BEDC.Derived.RingOfIntegersUp
