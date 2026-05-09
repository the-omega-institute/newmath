import BEDC.Derived.TreeUp

namespace BEDC.Derived.LambdaCalcUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.TreeUp

def LambdaCalcBHistTermCarrier (h : BHist) : Prop :=
  ∃ tag index connected acyclic root endpoint : BHist,
    UnaryHistory index ∧ TreeBHistCarrier tag index connected acyclic root endpoint ∧
      hsame h (append (BHist.e1 BHist.Empty) index)

def LambdaCalcBHistTermPacketCarrier
    (graph edge connected acyclic tag payload endpoint : BHist) : Prop :=
  TreeBHistCarrier graph edge connected acyclic tag endpoint ∧ UnaryHistory payload ∧
    UnaryHistory endpoint ∧ Cont tag payload endpoint

theorem LambdaCalcBHistTermCarrier_variable_constructor_carrier
    {i h tag endpoint connected acyclic root : BHist} :
    UnaryHistory i -> TreeBHistCarrier tag i connected acyclic root endpoint ->
      hsame h (append (BHist.e1 BHist.Empty) i) ->
        LambdaCalcBHistTermCarrier h ∧ UnaryHistory i := by
  intro indexUnary treeCarrier visibleEndpoint
  have rows := TreeBHistCarrier_exactness_rows treeCarrier
  have transportedVisible : hsame h (append (BHist.e1 BHist.Empty) i) :=
    hsame_trans visibleEndpoint (hsame_refl (append (BHist.e1 BHist.Empty) i))
  have termCarrier : LambdaCalcBHistTermCarrier h :=
    Exists.intro tag
      (Exists.intro i
        (Exists.intro connected
          (Exists.intro acyclic
            (Exists.intro root
              (Exists.intro endpoint
                (And.intro indexUnary (And.intro treeCarrier transportedVisible)))))))
  exact And.intro termCarrier rows.left.right.left

theorem LambdaCalcBHistTermCarrier_abstraction_application_closure
    {graph edge connected acyclic bodyTag bodyPayload bodyEndpoint binder absPayload absTag
      absEndpoint funTag funPayload funEndpoint argTag argPayload argEndpoint appPayload appTag
      appEndpoint : BHist} :
    LambdaCalcBHistTermPacketCarrier graph edge connected acyclic bodyTag bodyPayload bodyEndpoint ->
      LambdaCalcBHistTermPacketCarrier graph edge connected acyclic funTag funPayload funEndpoint ->
        LambdaCalcBHistTermPacketCarrier graph edge connected acyclic argTag argPayload argEndpoint ->
          UnaryHistory binder ->
            Cont binder bodyEndpoint absPayload ->
              TreeBHistCarrier graph edge connected acyclic absTag absEndpoint ->
                Cont absTag absPayload absEndpoint ->
                  Cont funEndpoint argEndpoint appPayload ->
                    TreeBHistCarrier graph edge connected acyclic appTag appEndpoint ->
                      Cont appTag appPayload appEndpoint ->
                        LambdaCalcBHistTermPacketCarrier graph edge connected acyclic absTag
                            absPayload absEndpoint ∧
                          LambdaCalcBHistTermPacketCarrier graph edge connected acyclic appTag
                              appPayload appEndpoint ∧
                            UnaryHistory absPayload ∧ UnaryHistory appPayload := by
  intro bodyCarrier funCarrier argCarrier binderUnary absPayloadRow absTree absEndpointRow
    appPayloadRow appTree appEndpointRow
  have absPayloadUnary : UnaryHistory absPayload :=
    unary_cont_closed binderUnary bodyCarrier.right.right.left absPayloadRow
  have absEndpointUnary : UnaryHistory absEndpoint :=
    absTree.right.right.left.left
  have appPayloadUnary : UnaryHistory appPayload :=
    unary_cont_closed funCarrier.right.right.left argCarrier.right.right.left appPayloadRow
  have appEndpointUnary : UnaryHistory appEndpoint :=
    appTree.right.right.left.left
  have absCarrier :
      LambdaCalcBHistTermPacketCarrier graph edge connected acyclic absTag absPayload absEndpoint :=
    And.intro absTree
      (And.intro absPayloadUnary
        (And.intro absEndpointUnary absEndpointRow))
  have appCarrier :
      LambdaCalcBHistTermPacketCarrier graph edge connected acyclic appTag appPayload appEndpoint :=
    And.intro appTree
      (And.intro appPayloadUnary
        (And.intro appEndpointUnary appEndpointRow))
  exact And.intro absCarrier
    (And.intro appCarrier
      (And.intro absPayloadUnary appPayloadUnary))

theorem LambdaCalcBHistTermPacketCarrier_public_endpoint_transport
    {graph edge connected acyclic tag tag' payload endpoint endpoint' : BHist} :
    LambdaCalcBHistTermPacketCarrier graph edge connected acyclic tag payload endpoint ->
      hsame tag tag' -> hsame endpoint endpoint' ->
        LambdaCalcBHistTermPacketCarrier graph edge connected acyclic tag' payload endpoint' ∧
          Cont tag' payload endpoint' ∧ UnaryHistory endpoint' := by
  intro carrier sameTag sameEndpoint
  have treeCarrier' :
      TreeBHistCarrier graph edge connected acyclic tag' endpoint' :=
    (TreeBHistCarrier_classifier_transport carrier.left (hsame_refl graph) (hsame_refl edge)
      (hsame_refl connected) (hsame_refl acyclic) sameTag sameEndpoint).left
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport carrier.right.right.left sameEndpoint
  have endpointRow' : Cont tag' payload endpoint' :=
    cont_hsame_transport sameTag (hsame_refl payload) sameEndpoint carrier.right.right.right
  have carrier' :
      LambdaCalcBHistTermPacketCarrier graph edge connected acyclic tag' payload endpoint' :=
    And.intro treeCarrier'
      (And.intro carrier.right.left
        (And.intro endpointUnary' endpointRow'))
  exact And.intro carrier' (And.intro endpointRow' endpointUnary')

theorem LambdaCalcBHistTermCarrier_constructor_source_disjointness
    {i hVar hAbs hApp : BHist} :
    UnaryHistory i ->
      hsame hVar (append (BHist.e1 BHist.Empty) i) ->
        hsame hAbs (append (BHist.e0 BHist.Empty) i) ->
          hsame hApp (append (BHist.e1 (BHist.e1 BHist.Empty)) i) ->
            (hsame hVar hAbs -> False) ∧ (hsame hAbs hApp -> False) := by
  intro _indexUnary sameVar sameAbs sameApp
  constructor
  · intro mixed
    have sourcesSame :
        hsame (append (BHist.e1 BHist.Empty) i) (append (BHist.e0 BHist.Empty) i) :=
      hsame_trans (hsame_symm sameVar) (hsame_trans mixed sameAbs)
    have tagsSame : hsame (BHist.e1 BHist.Empty) (BHist.e0 BHist.Empty) :=
      append_right_cancel (k := i) sourcesSame
    exact not_hsame_e1_e0 tagsSame
  · intro mixed
    have sourcesSame :
        hsame (append (BHist.e0 BHist.Empty) i)
          (append (BHist.e1 (BHist.e1 BHist.Empty)) i) :=
      hsame_trans (hsame_symm sameAbs) (hsame_trans mixed sameApp)
    have tagsSame :
        hsame (BHist.e0 BHist.Empty) (BHist.e1 (BHist.e1 BHist.Empty)) :=
      append_right_cancel (k := i) sourcesSame
    exact not_hsame_e0_e1 tagsSame

theorem LambdaCalcBHistTermCarrier_constructor_case_exhaustion {i hVar hAbs hApp : BHist} :
    UnaryHistory i ->
      hsame hVar (append (BHist.e1 BHist.Empty) i) ->
        hsame hAbs (append (BHist.e0 BHist.Empty) i) ->
          hsame hApp (append (BHist.e1 (BHist.e1 BHist.Empty)) i) ->
            (hsame hVar hAbs -> False) ∧ (hsame hAbs hApp -> False) ∧
              (hsame hVar hApp -> False) := by
  intro _indexUnary sameVar sameAbs sameApp
  constructor
  · intro mixed
    have sourcesSame :
        hsame (append (BHist.e1 BHist.Empty) i) (append (BHist.e0 BHist.Empty) i) :=
      hsame_trans (hsame_symm sameVar) (hsame_trans mixed sameAbs)
    have tagsSame : hsame (BHist.e1 BHist.Empty) (BHist.e0 BHist.Empty) :=
      append_right_cancel (k := i) sourcesSame
    exact not_hsame_e1_e0 tagsSame
  · constructor
    · intro mixed
      have sourcesSame :
          hsame (append (BHist.e0 BHist.Empty) i)
            (append (BHist.e1 (BHist.e1 BHist.Empty)) i) :=
        hsame_trans (hsame_symm sameAbs) (hsame_trans mixed sameApp)
      have tagsSame :
          hsame (BHist.e0 BHist.Empty) (BHist.e1 (BHist.e1 BHist.Empty)) :=
        append_right_cancel (k := i) sourcesSame
      exact not_hsame_e0_e1 tagsSame
    · intro mixed
      have sourcesSame :
          hsame (append (BHist.e1 BHist.Empty) i)
            (append (BHist.e1 (BHist.e1 BHist.Empty)) i) :=
        hsame_trans (hsame_symm sameVar) (hsame_trans mixed sameApp)
      have tagsSame :
          hsame (BHist.e1 BHist.Empty) (BHist.e1 (BHist.e1 BHist.Empty)) :=
        append_right_cancel (k := i) sourcesSame
      have tailsSame : hsame BHist.Empty (BHist.e1 BHist.Empty) :=
        hsame_e1_iff.mp tagsSame
      exact not_hsame_emp_e1 tailsSame

theorem LambdaCalcBHistTermPacketCarrier_substitution_output_determinacy
    {graph edge connected acyclic tag payload endpoint endpoint' : BHist} :
    LambdaCalcBHistTermPacketCarrier graph edge connected acyclic tag payload endpoint ->
      TreeBHistCarrier graph edge connected acyclic tag endpoint' ->
        Cont tag payload endpoint' ->
          LambdaCalcBHistTermPacketCarrier graph edge connected acyclic tag payload endpoint' ∧
            hsame endpoint endpoint' ∧ UnaryHistory endpoint' := by
  intro packet treeCarrier endpointRow
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed
      (TreeBHistCarrier_exactness_rows treeCarrier).right.right.right.right.right.right.left
      packet.right.left endpointRow
  have packet' :
      LambdaCalcBHistTermPacketCarrier graph edge connected acyclic tag payload endpoint' :=
    And.intro treeCarrier (And.intro packet.right.left (And.intro endpointUnary' endpointRow))
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame (hsame_refl tag) (hsame_refl payload) packet.right.right.right endpointRow
  exact And.intro packet' (And.intro sameEndpoint endpointUnary')

theorem LambdaCalcBHistTermPacketCarrier_substitution_ledger_scope
    {graph edge connected acyclic tag payload endpoint substTag substPayload substEndpoint
      varIndex ledger result : BHist} :
    LambdaCalcBHistTermPacketCarrier graph edge connected acyclic tag payload endpoint ->
      LambdaCalcBHistTermPacketCarrier graph edge connected acyclic substTag substPayload
          substEndpoint ->
        UnaryHistory varIndex ->
          Cont endpoint substEndpoint ledger ->
            Cont ledger varIndex result ->
              UnaryHistory ledger ∧ UnaryHistory result ∧ hsame ledger
                  (append endpoint substEndpoint) ∧
                hsame result (append (append endpoint substEndpoint) varIndex) := by
  intro packet substPacket varUnary ledgerRow resultRow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed packet.right.right.left substPacket.right.right.left ledgerRow
  have resultUnary : UnaryHistory result :=
    unary_cont_closed ledgerUnary varUnary resultRow
  have resultReadback : hsame result (append (append endpoint substEndpoint) varIndex) := by
    cases ledgerRow
    exact resultRow
  exact And.intro ledgerUnary
    (And.intro resultUnary (And.intro ledgerRow resultReadback))

theorem LambdaCalcBHistTermPacketCarrier_free_variable_ledger_coverage
    {graph edge connected acyclic tag payload endpoint freeVariable freeLedger : BHist} :
    LambdaCalcBHistTermPacketCarrier graph edge connected acyclic tag payload endpoint ->
      UnaryHistory freeVariable ->
        Cont endpoint freeVariable freeLedger ->
          UnaryHistory freeLedger ∧ hsame freeLedger (append endpoint freeVariable) ∧
            LambdaCalcBHistTermPacketCarrier graph edge connected acyclic tag payload endpoint := by
  intro packet freeVariableUnary freeLedgerCont
  have freeLedgerUnary : UnaryHistory freeLedger :=
    unary_cont_closed packet.right.right.left freeVariableUnary freeLedgerCont
  exact And.intro freeLedgerUnary (And.intro freeLedgerCont packet)

end BEDC.Derived.LambdaCalcUp
