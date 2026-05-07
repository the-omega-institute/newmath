import BEDC.Derived.LieAlgebraUp
import BEDC.Derived.LieGroupUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ExpMapUp

open BEDC.Derived.LieAlgebraUp
open BEDC.Derived.LieGroupUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem ExpMapClassifier_stability_obligation_surface
    {source source' target target' ledger ledger' endpoint endpoint' : BHist} :
    LieAlgebraSingletonCarrier source ->
      LieAlgebraSingletonCarrier source' ->
        LieGroupSingletonCarrier target ->
          LieGroupSingletonCarrier target' ->
            hsame source source' ->
              hsame target target' ->
                Cont source target ledger ->
                  Cont source' target' ledger' ->
                    Cont ledger BHist.Empty endpoint ->
                      Cont ledger' BHist.Empty endpoint' ->
                        hsame ledger ledger' ∧ hsame endpoint endpoint' ∧
                          UnaryHistory endpoint ∧ UnaryHistory endpoint' := by
  intro sourceCarrier sourceCarrier' targetCarrier targetCarrier'
    sameSource sameTarget ledgerRow ledgerRow' endpointRow endpointRow'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameSource sameTarget ledgerRow ledgerRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameLedger (hsame_refl BHist.Empty) endpointRow endpointRow'
  have ledgerEmpty : hsame ledger BHist.Empty :=
    cont_respects_hsame sourceCarrier targetCarrier ledgerRow (cont_left_unit BHist.Empty)
  have ledgerEmpty' : hsame ledger' BHist.Empty :=
    cont_respects_hsame sourceCarrier' targetCarrier' ledgerRow'
      (cont_left_unit BHist.Empty)
  have endpointEmpty : hsame endpoint BHist.Empty :=
    cont_respects_hsame ledgerEmpty (hsame_refl BHist.Empty) endpointRow
      (cont_left_unit BHist.Empty)
  have endpointEmpty' : hsame endpoint' BHist.Empty :=
    cont_respects_hsame ledgerEmpty' (hsame_refl BHist.Empty) endpointRow'
      (cont_left_unit BHist.Empty)
  have endpointUnary : UnaryHistory endpoint :=
    unary_transport unary_empty (hsame_symm endpointEmpty)
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport unary_empty (hsame_symm endpointEmpty')
  exact And.intro sameLedger
    (And.intro sameEndpoint (And.intro endpointUnary endpointUnary'))

theorem ExpMapCarrier_obligation_surface {tangent endpoint flow : BHist} :
    LieAlgebraSingletonCarrier tangent ->
      LieGroupSingletonCarrier endpoint ->
        Cont tangent endpoint flow ->
          LieAlgebraSingletonCarrier tangent ∧ LieGroupSingletonCarrier endpoint ∧
            LieGroupSingletonCarrier flow ∧ hsame flow BHist.Empty ∧ UnaryHistory flow := by
  intro tangentCarrier endpointCarrier flowRow
  have flowEmpty : hsame flow BHist.Empty :=
    cont_respects_hsame tangentCarrier endpointCarrier flowRow (cont_left_unit BHist.Empty)
  have flowUnary : UnaryHistory flow :=
    unary_transport unary_empty (hsame_symm flowEmpty)
  exact And.intro tangentCarrier
    (And.intro endpointCarrier (And.intro flowEmpty (And.intro flowEmpty flowUnary)))

end BEDC.Derived.ExpMapUp
