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

theorem ExpMapGraphCarrier_hsame_transport {tangent endpoint flow tangent' endpoint'
    flow' : BHist} :
    ExpMapGraphCarrier tangent endpoint flow -> hsame tangent tangent' -> hsame endpoint endpoint' ->
      hsame flow flow' ->
        ExpMapGraphCarrier tangent' endpoint' flow' ∧ UnaryHistory tangent' ∧
          UnaryHistory endpoint' ∧ UnaryHistory flow' := by
  intro graph sameTangent sameEndpoint sameFlow
  have tangentCarrier' : LieAlgebraSingletonCarrier tangent' :=
    hsame_trans (hsame_symm sameTangent) graph.left
  have endpointCarrier' : LieGroupSingletonCarrier endpoint' :=
    hsame_trans (hsame_symm sameEndpoint) graph.right.left
  have flowRow' : Cont tangent' BHist.Empty flow' := by
    cases sameTangent
    exact cont_result_hsame_transport graph.right.right.left sameFlow
  have flowEndpoint' : hsame flow' endpoint' :=
    hsame_trans (hsame_symm sameFlow) (hsame_trans graph.right.right.right sameEndpoint)
  have graph' : ExpMapGraphCarrier tangent' endpoint' flow' :=
    And.intro tangentCarrier'
      (And.intro endpointCarrier' (And.intro flowRow' flowEndpoint'))
  have rows := ExpMapCarrier_source_obligations graph'
  exact And.intro graph'
    (And.intro rows.right.right.right.left
      (And.intro rows.right.right.right.right.left rows.right.right.right.right.right))

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

theorem ExpMapZeroFlow_obligation_surface {tangent endpoint flow composed : BHist} :
    ExpMapFlowLedger tangent endpoint flow ->
      Cont flow BHist.Empty composed ->
        hsame tangent endpoint ∧ hsame flow endpoint ∧ hsame composed endpoint ∧
          LieAlgebraSingletonCarrier tangent ∧ LieGroupSingletonCarrier endpoint ∧
            LieGroupSingletonCarrier composed ∧ UnaryHistory composed := by
  intro ledger composedRow
  have surface :
      LieAlgebraSingletonCarrier tangent ∧ LieGroupSingletonCarrier endpoint ∧
        hsame endpoint tangent ∧ hsame flow endpoint ∧ UnaryHistory tangent ∧
          UnaryHistory endpoint ∧ UnaryHistory flow :=
    ExpMapFlowLedger_carrier_obligation_surface ledger
  have sameTangentEndpoint : hsame tangent endpoint :=
    hsame_symm surface.right.right.left
  have sameComposedFlow : hsame composed flow :=
    cont_right_unit_result composedRow
  have sameComposedEndpoint : hsame composed endpoint :=
    hsame_trans sameComposedFlow surface.right.right.right.left
  have composedCarrier : LieGroupSingletonCarrier composed :=
    hsame_trans sameComposedEndpoint surface.right.left
  have composedUnary : UnaryHistory composed :=
    unary_transport surface.right.right.right.right.right.right (hsame_symm sameComposedFlow)
  exact And.intro sameTangentEndpoint
    (And.intro surface.right.right.right.left
      (And.intro sameComposedEndpoint
        (And.intro surface.left
          (And.intro surface.right.left
            (And.intro composedCarrier composedUnary)))))

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

theorem ExpMapZeroFlow_composition_obligation {tangent endpoint flow composite : BHist} :
    LieAlgebraSingletonCarrier tangent ->
      LieGroupSingletonCarrier endpoint ->
        Cont tangent BHist.Empty endpoint ->
          Cont endpoint BHist.Empty flow ->
            Cont tangent flow composite ->
              hsame endpoint tangent ∧ hsame flow endpoint ∧ hsame composite tangent ∧
                UnaryHistory tangent ∧ UnaryHistory endpoint ∧ UnaryHistory flow ∧
                  UnaryHistory composite := by
  intro tangentCarrier endpointCarrier endpointRow flowRow compositeRow
  have sameEndpointTangent : hsame endpoint tangent :=
    cont_right_unit_result endpointRow
  have sameFlowEndpoint : hsame flow endpoint :=
    cont_right_unit_result flowRow
  have tangentUnary : UnaryHistory tangent :=
    unary_transport unary_empty (hsame_symm tangentCarrier)
  have endpointUnary : UnaryHistory endpoint :=
    unary_transport tangentUnary (hsame_symm sameEndpointTangent)
  have flowUnary : UnaryHistory flow :=
    unary_transport endpointUnary (hsame_symm sameFlowEndpoint)
  have flowEmpty : hsame flow BHist.Empty :=
    hsame_trans sameFlowEndpoint endpointCarrier
  have sameComposite : hsame composite tangent :=
    cont_respects_hsame (hsame_refl tangent) flowEmpty compositeRow (cont_right_unit tangent)
  have compositeUnary : UnaryHistory composite :=
    unary_transport tangentUnary (hsame_symm sameComposite)
  exact And.intro sameEndpointTangent
    (And.intro sameFlowEndpoint
      (And.intro sameComposite
        (And.intro tangentUnary (And.intro endpointUnary (And.intro flowUnary compositeUnary)))))

theorem ExpMapGraphCarrier_zero_flow_composition_obligation
    {tangent endpoint zeroFlow firstFlow secondFlow directFlow : BHist} :
    LieAlgebraSingletonCarrier tangent ->
      LieGroupSingletonCarrier endpoint ->
        Cont tangent BHist.Empty zeroFlow ->
          Cont tangent endpoint firstFlow ->
            Cont firstFlow BHist.Empty secondFlow ->
              Cont tangent endpoint directFlow ->
                ExpMapGraphCarrier tangent endpoint zeroFlow ∧ hsame zeroFlow endpoint ∧
                  hsame secondFlow directFlow ∧ LieGroupSingletonCarrier firstFlow ∧
                    LieGroupSingletonCarrier secondFlow ∧ UnaryHistory zeroFlow ∧
                      UnaryHistory secondFlow := by
  intro tangentCarrier endpointCarrier zeroRow firstRow secondRow directRow
  have zeroSameTangent : hsame zeroFlow tangent :=
    cont_right_unit_result zeroRow
  have zeroSameEndpoint : hsame zeroFlow endpoint :=
    hsame_trans zeroSameTangent
      (hsame_trans tangentCarrier (hsame_symm endpointCarrier))
  have zeroEmpty : hsame zeroFlow BHist.Empty :=
    hsame_trans zeroSameTangent tangentCarrier
  have firstEmpty : hsame firstFlow BHist.Empty :=
    cont_respects_hsame tangentCarrier endpointCarrier firstRow
      (cont_left_unit BHist.Empty)
  have secondSameFirst : hsame secondFlow firstFlow :=
    cont_right_unit_result secondRow
  have secondEmpty : hsame secondFlow BHist.Empty :=
    hsame_trans secondSameFirst firstEmpty
  have directEmpty : hsame directFlow BHist.Empty :=
    cont_respects_hsame tangentCarrier endpointCarrier directRow
      (cont_left_unit BHist.Empty)
  have sameSecondDirect : hsame secondFlow directFlow :=
    hsame_trans secondEmpty (hsame_symm directEmpty)
  have zeroUnary : UnaryHistory zeroFlow :=
    unary_transport unary_empty (hsame_symm zeroEmpty)
  have secondUnary : UnaryHistory secondFlow :=
    unary_transport unary_empty (hsame_symm secondEmpty)
  exact And.intro
    (And.intro tangentCarrier
      (And.intro endpointCarrier (And.intro zeroRow zeroSameEndpoint)))
    (And.intro zeroSameEndpoint
      (And.intro sameSecondDirect
        (And.intro firstEmpty
          (And.intro secondEmpty (And.intro zeroUnary secondUnary)))))

theorem ExpMapFlowLedger_zero_flow_composition_obligations
    {zero identity zeroFlow tangent endpoint flow composed : BHist} :
    ExpMapFlowLedger zero identity zeroFlow -> ExpMapFlowLedger tangent endpoint flow ->
      Cont zeroFlow flow composed ->
        hsame zeroFlow identity ∧ hsame flow endpoint ∧ UnaryHistory zeroFlow ∧
          UnaryHistory flow ∧ UnaryHistory composed := by
  intro zeroLedger flowLedger composedRow
  have zeroObligations :=
    ExpMapFlowLedger_carrier_obligation_surface zeroLedger
  have flowObligations :=
    ExpMapFlowLedger_carrier_obligation_surface flowLedger
  have composedUnary : UnaryHistory composed :=
    unary_cont_closed zeroObligations.right.right.right.right.right.right
      flowObligations.right.right.right.right.right.right composedRow
  exact And.intro zeroObligations.right.right.right.left
    (And.intro flowObligations.right.right.right.left
      (And.intro zeroObligations.right.right.right.right.right.right
        (And.intro flowObligations.right.right.right.right.right.right composedUnary)))

theorem ExpMapFlowLedger_zero_composition_obligation {tangent endpoint flow composite : BHist} :
    ExpMapFlowLedger tangent endpoint flow -> hsame tangent BHist.Empty ->
      Cont endpoint flow composite ->
        hsame composite BHist.Empty ∧ UnaryHistory composite ∧
          LieAlgebraSingletonCarrier tangent ∧ LieGroupSingletonCarrier endpoint ∧
            hsame flow endpoint := by
  intro ledger _tangentEmpty compositeRow
  have tangentCarrier : LieAlgebraSingletonCarrier tangent := ledger.left
  have endpointCarrier : LieGroupSingletonCarrier endpoint := ledger.right.left
  have flowEndpoint : hsame flow endpoint :=
    cont_right_unit_result ledger.right.right.right
  have flowEmpty : hsame flow BHist.Empty :=
    hsame_trans flowEndpoint endpointCarrier
  have compositeEmpty : hsame composite BHist.Empty :=
    cont_respects_hsame endpointCarrier flowEmpty compositeRow (cont_left_unit BHist.Empty)
  have compositeUnary : UnaryHistory composite :=
    unary_transport unary_empty (hsame_symm compositeEmpty)
  exact And.intro compositeEmpty
    (And.intro compositeUnary
      (And.intro tangentCarrier (And.intro endpointCarrier flowEndpoint)))

def ExpMapGraphClassifier
    (source endpoint flow source' endpoint' flow' : BHist) : Prop :=
  hsame source source' ∧ hsame endpoint endpoint' ∧ hsame flow flow'

theorem ExpMapGraphClassifier_stability_obligations
    {source source' endpoint endpoint' flow flow' ledger ledger' : BHist} :
    ExpMapGraphCarrier source endpoint flow -> ExpMapGraphCarrier source' endpoint' flow' ->
      hsame source source' -> hsame endpoint endpoint' -> Cont source endpoint ledger ->
        Cont source' endpoint' ledger' -> hsame flow ledger -> hsame flow' ledger' ->
          ExpMapGraphClassifier source endpoint flow source' endpoint' flow' ∧
            hsame ledger ledger' ∧ UnaryHistory flow ∧ UnaryHistory flow' := by
  intro graph graph' sameSource sameEndpoint ledgerRow ledgerRow' sameFlowLedger
    sameFlowLedger'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameSource sameEndpoint ledgerRow ledgerRow'
  have sameFlow : hsame flow flow' :=
    hsame_trans sameFlowLedger (hsame_trans sameLedger (hsame_symm sameFlowLedger'))
  have graphRows := ExpMapCarrier_source_obligations graph
  have graphRows' := ExpMapCarrier_source_obligations graph'
  exact And.intro
    (And.intro sameSource (And.intro sameEndpoint sameFlow))
    (And.intro sameLedger
      (And.intro graphRows.right.right.right.right.right graphRows'.right.right.right.right.right))

end BEDC.Derived.ExpMapUp
