import BEDC.Derived.LieAlgebraUp
import BEDC.Derived.LieGroupUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ExpMapUp

open BEDC.Derived.LieAlgebraUp
open BEDC.Derived.LieGroupUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def ExpMapGraphCarrier (tangent endpoint flow : BHist) : Prop :=
  LieAlgebraSingletonCarrier tangent ∧ LieGroupSingletonCarrier endpoint ∧
    Cont tangent BHist.Empty flow ∧ hsame flow endpoint

theorem ExpMapCarrier_source_obligations {tangent endpoint flow : BHist} :
    ExpMapGraphCarrier tangent endpoint flow ->
      LieAlgebraSingletonCarrier tangent ∧ LieGroupSingletonCarrier endpoint ∧
        hsame flow endpoint ∧ UnaryHistory tangent ∧ UnaryHistory endpoint ∧
          UnaryHistory flow := by
  intro graph
  have tangentUnary : UnaryHistory tangent :=
    unary_transport unary_empty (hsame_symm graph.left)
  have endpointUnary : UnaryHistory endpoint :=
    unary_transport unary_empty (hsame_symm graph.right.left)
  have flowTangent : hsame flow tangent :=
    cont_right_unit_result graph.right.right.left
  have flowUnary : UnaryHistory flow :=
    unary_transport tangentUnary (hsame_symm flowTangent)
  exact And.intro graph.left
    (And.intro graph.right.left
      (And.intro graph.right.right.right
        (And.intro tangentUnary (And.intro endpointUnary flowUnary))))

theorem ExpMapGraphCarrier_obligation_surface {tangent flow endpoint : BHist} :
    LieAlgebraSingletonCarrier tangent ->
      LieGroupSingletonCarrier endpoint ->
        Cont tangent flow endpoint ->
          SemanticNameCert
              (fun row : BHist =>
                LieAlgebraSingletonCarrier tangent ∧ Cont tangent flow row ∧
                  LieGroupSingletonCarrier row)
              (fun row : BHist =>
                LieAlgebraSingletonCarrier tangent ∧ Cont tangent flow row ∧
                  LieGroupSingletonCarrier row)
              (fun row : BHist =>
                LieAlgebraSingletonCarrier tangent ∧ Cont tangent flow row ∧
                  LieGroupSingletonCarrier row)
              hsame ∧
            UnaryHistory endpoint := by
  intro tangentCarrier endpointCarrier endpointRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_transport unary_empty (hsame_symm endpointCarrier)
  constructor
  · constructor
    · constructor
      · exact Exists.intro endpoint (And.intro tangentCarrier (And.intro endpointRow endpointCarrier))
      · intro row _carrier
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same carrier
        exact And.intro carrier.left
          (And.intro (cont_result_hsame_transport carrier.right.left same)
            (hsame_trans (hsame_symm same) carrier.right.right))
    · intro _row source
      exact source
    · intro _row source
      exact source
  · exact endpointUnary

def ExpMapFlowLedger (tangent endpoint flow : BHist) : Prop :=
  LieAlgebraSingletonCarrier tangent ∧ LieGroupSingletonCarrier endpoint ∧
    Cont tangent BHist.Empty endpoint ∧ Cont endpoint BHist.Empty flow

theorem ExpMapFlowLedger_carrier_obligation_surface {tangent endpoint flow : BHist} :
    ExpMapFlowLedger tangent endpoint flow ->
      LieAlgebraSingletonCarrier tangent ∧ LieGroupSingletonCarrier endpoint ∧
        hsame endpoint tangent ∧ hsame flow endpoint ∧ UnaryHistory tangent ∧
          UnaryHistory endpoint ∧ UnaryHistory flow := by
  intro ledger
  have tangentCarrier : LieAlgebraSingletonCarrier tangent := ledger.left
  have endpointCarrier : LieGroupSingletonCarrier endpoint := ledger.right.left
  have sameEndpointTangent : hsame endpoint tangent :=
    cont_right_unit_result ledger.right.right.left
  have sameFlowEndpoint : hsame flow endpoint :=
    cont_right_unit_result ledger.right.right.right
  have tangentUnary : UnaryHistory tangent :=
    unary_transport unary_empty (hsame_symm tangentCarrier)
  have endpointUnary : UnaryHistory endpoint :=
    unary_transport tangentUnary (hsame_symm sameEndpointTangent)
  have flowUnary : UnaryHistory flow :=
    unary_transport endpointUnary (hsame_symm sameFlowEndpoint)
  exact And.intro tangentCarrier
    (And.intro endpointCarrier
      (And.intro sameEndpointTangent
        (And.intro sameFlowEndpoint
          (And.intro tangentUnary (And.intro endpointUnary flowUnary)))))

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
