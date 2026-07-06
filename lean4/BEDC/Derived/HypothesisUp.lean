import BEDC.Derived.ProbSpaceUp
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.HypothesisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.PreorderUp
open BEDC.Derived.ProbSpaceUp

theorem HypothesisDecisionCarrier_type_one_error_ledger
    {nullBound rejectEvent complement errorBudget : BHist} :
    ProbSpacePublicEventPacket nullBound errorBudget rejectEvent complement errorBudget ->
      hsame complement BHist.Empty ->
        hsame nullBound errorBudget ∧ hsame rejectEvent errorBudget ∧
          PreorderPrefixLE rejectEvent errorBudget ∧ UnaryHistory rejectEvent ∧
            UnaryHistory errorBudget := by
  intro packet complementEmpty
  have bounds :
      hsame errorBudget errorBudget ∧ UnaryHistory errorBudget ∧
        Cont rejectEvent complement errorBudget ∧ PreorderPrefixLE rejectEvent errorBudget :=
    ProbSpacePublicEventPacket_normalization_bounds packet
  have rejectBudget : hsame rejectEvent errorBudget := by
    have rejectToSelf : Cont rejectEvent BHist.Empty rejectEvent := cont_right_unit rejectEvent
    have rejectWithEmptyComplement : Cont rejectEvent BHist.Empty errorBudget :=
      cont_hsame_transport (hsame_refl rejectEvent) complementEmpty
        (hsame_refl errorBudget) bounds.right.right.left
    exact cont_deterministic rejectToSelf rejectWithEmptyComplement
  exact And.intro packet.right.right.right.left
    (And.intro rejectBudget
      (And.intro bounds.right.right.right
        (And.intro packet.left bounds.right.left)))

theorem HypothesisTestDecisionCarrier_type_one_error_ledger
    {null reject budget ledger endpoint : BHist} :
    UnaryHistory null -> UnaryHistory reject -> UnaryHistory budget ->
      Cont reject budget ledger -> Cont null ledger endpoint ->
        UnaryHistory ledger ∧ UnaryHistory endpoint ∧ hsame ledger (append reject budget) ∧
          hsame endpoint (append null ledger) := by
  intro nullUnary rejectUnary budgetUnary ledgerRow endpointRow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed rejectUnary budgetUnary ledgerRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed nullUnary ledgerUnary endpointRow
  exact ⟨ledgerUnary, endpointUnary, ledgerRow, endpointRow⟩

theorem HypothesisTestDecisionCarrier_distribution_boundary
    {null alternative sample statistic threshold decision nullLedger altLedger surface : BHist} :
    UnaryHistory null -> UnaryHistory alternative -> UnaryHistory sample -> UnaryHistory statistic ->
      UnaryHistory threshold -> Cont sample statistic decision -> Cont decision threshold nullLedger ->
        Cont alternative threshold altLedger -> Cont nullLedger altLedger surface ->
          UnaryHistory decision ∧ UnaryHistory nullLedger ∧ UnaryHistory altLedger ∧
            UnaryHistory surface ∧ hsame decision (append sample statistic) ∧
              hsame nullLedger (append decision threshold) ∧
                hsame altLedger (append alternative threshold) ∧
                  hsame surface (append nullLedger altLedger) := by
  intro nullUnary alternativeUnary sampleUnary statisticUnary thresholdUnary decisionRow
    nullLedgerRow altLedgerRow surfaceRow
  have decisionUnary : UnaryHistory decision :=
    unary_cont_closed sampleUnary statisticUnary decisionRow
  have nullLedgerUnary : UnaryHistory nullLedger :=
    unary_cont_closed decisionUnary thresholdUnary nullLedgerRow
  have altLedgerUnary : UnaryHistory altLedger :=
    unary_cont_closed alternativeUnary thresholdUnary altLedgerRow
  have surfaceUnary : UnaryHistory surface :=
    unary_cont_closed nullLedgerUnary altLedgerUnary surfaceRow
  exact
    ⟨decisionUnary, nullLedgerUnary, altLedgerUnary, surfaceUnary, decisionRow, nullLedgerRow,
      altLedgerRow, surfaceRow⟩

theorem HypothesisTestDecisionCarrier_type_two_error_ledger
    {altBound acceptEvent complement typeI typeII jointLedger : BHist} :
    ProbSpacePublicEventPacket altBound typeII acceptEvent complement typeII ->
      hsame complement BHist.Empty ->
        UnaryHistory typeI ->
          Cont typeI typeII jointLedger ->
            hsame altBound typeII ∧ hsame acceptEvent typeII ∧
              PreorderPrefixLE acceptEvent typeII ∧ UnaryHistory jointLedger ∧
                hsame jointLedger (append typeI typeII) := by
  intro packet complementEmpty typeIUnary jointRow
  have bounds :
      hsame typeII typeII ∧ UnaryHistory typeII ∧
        Cont acceptEvent complement typeII ∧ PreorderPrefixLE acceptEvent typeII :=
    ProbSpacePublicEventPacket_normalization_bounds packet
  have acceptSelf : Cont acceptEvent BHist.Empty acceptEvent :=
    cont_right_unit acceptEvent
  have acceptWithEmptyComplement : Cont acceptEvent BHist.Empty typeII :=
    cont_hsame_transport (hsame_refl acceptEvent) complementEmpty
      (hsame_refl typeII) bounds.right.right.left
  have acceptTypeII : hsame acceptEvent typeII :=
    cont_deterministic acceptSelf acceptWithEmptyComplement
  have jointUnary : UnaryHistory jointLedger :=
    unary_cont_closed typeIUnary bounds.right.left jointRow
  exact
    ⟨packet.right.right.right.left,
      acceptTypeII,
      bounds.right.right.right,
      jointUnary,
      jointRow⟩

theorem HypothesisTestDecisionCarrier_namecert_obligation_surface
    {null reject complement budget ledger endpoint alt accept altComplement typeII joint surface :
      BHist} :
    ProbSpacePublicEventPacket null budget reject complement budget ->
      hsame complement BHist.Empty ->
        ProbSpacePublicEventPacket alt typeII accept altComplement typeII ->
          hsame altComplement BHist.Empty ->
            Cont reject budget ledger ->
              Cont null ledger endpoint ->
                Cont accept typeII joint ->
                  Cont ledger joint surface ->
                    SemanticNameCert (fun h : BHist => hsame h surface)
                      (fun h : BHist => hsame h surface)
                      (fun h : BHist => hsame h surface) hsame ∧
                      hsame endpoint (append null ledger) ∧
                        hsame surface (append ledger joint) := by
  intro nullPacket complementEmpty altPacket altComplementEmpty rejectBudget nullLedger acceptTypeII
    ledgerJoint
  have nullBounds :
      hsame budget budget ∧ UnaryHistory budget ∧ Cont reject complement budget ∧
        PreorderPrefixLE reject budget :=
    ProbSpacePublicEventPacket_normalization_bounds nullPacket
  have nullUnary : UnaryHistory null :=
    unary_transport nullBounds.right.left (hsame_symm nullPacket.right.right.right.left)
  have typeOne :
      UnaryHistory ledger ∧ UnaryHistory endpoint ∧ hsame ledger (append reject budget) ∧
        hsame endpoint (append null ledger) :=
    HypothesisTestDecisionCarrier_type_one_error_ledger nullUnary
      (HypothesisDecisionCarrier_type_one_error_ledger nullPacket complementEmpty).right.right.right.left
      nullBounds.right.left rejectBudget nullLedger
  have typeTwo :
      hsame alt typeII ∧ hsame accept typeII ∧ PreorderPrefixLE accept typeII ∧
        UnaryHistory joint ∧ hsame joint (append accept typeII) :=
    HypothesisTestDecisionCarrier_type_two_error_ledger altPacket altComplementEmpty altPacket.left
      acceptTypeII
  have surfaceCert :
      SemanticNameCert (fun h : BHist => hsame h surface)
        (fun h : BHist => hsame h surface)
        (fun h : BHist => hsame h surface) hsame := by
    constructor
    · constructor
      · exact ⟨surface, hsame_refl surface⟩
      · intro h _surfaceH
        exact hsame_refl h
      · intro h k sameHK
        exact hsame_symm sameHK
      · intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      · intro h k sameHK surfaceH
        exact hsame_trans (hsame_symm sameHK) surfaceH
    · intro h sourceH
      exact sourceH
    · intro h sourceH
      exact sourceH
  exact
    ⟨surfaceCert,
      typeOne.right.right.right,
      ledgerJoint⟩

theorem HypothesisTestDecisionCarrier_finite_risk_boundary
    {null reject complement budget ledger endpoint alt accept altComplement typeII joint surface :
      BHist} :
    ProbSpacePublicEventPacket null budget reject complement budget ->
      hsame complement BHist.Empty ->
        ProbSpacePublicEventPacket alt typeII accept altComplement typeII ->
          hsame altComplement BHist.Empty ->
            Cont reject budget ledger ->
              Cont null ledger endpoint ->
                Cont accept typeII joint ->
                  Cont ledger joint surface ->
                    hsame endpoint (append null ledger) ∧ hsame surface (append ledger joint) ∧
                      UnaryHistory ledger ∧ UnaryHistory joint ∧ UnaryHistory surface := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory ProbSpacePublicEventPacket
  intro nullPacket complementEmpty altPacket altComplementEmpty rejectBudget nullLedger
    acceptTypeII ledgerJoint
  have typeOneLedger :
      hsame null budget ∧ hsame reject budget ∧ PreorderPrefixLE reject budget ∧
        UnaryHistory reject ∧ UnaryHistory budget :=
    HypothesisDecisionCarrier_type_one_error_ledger nullPacket complementEmpty
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed typeOneLedger.right.right.right.left typeOneLedger.right.right.right.right
      rejectBudget
  have typeTwoLedger :
      hsame alt typeII ∧ hsame accept typeII ∧ PreorderPrefixLE accept typeII ∧
        UnaryHistory joint ∧ hsame joint (append accept typeII) :=
    HypothesisTestDecisionCarrier_type_two_error_ledger altPacket altComplementEmpty
      altPacket.left acceptTypeII
  have surfaceUnary : UnaryHistory surface :=
    unary_cont_closed ledgerUnary typeTwoLedger.right.right.right.left ledgerJoint
  exact
    ⟨nullLedger, ledgerJoint, ledgerUnary, typeTwoLedger.right.right.right.left,
      surfaceUnary⟩

theorem HypothesisTestDecisionCarrier_decision_transport_stability
    {null reject complement budget ledger endpoint alt accept altComplement typeII joint surface
      null' ledger' endpoint' joint' surface' : BHist} :
    ProbSpacePublicEventPacket null budget reject complement budget →
      hsame complement BHist.Empty →
        ProbSpacePublicEventPacket alt typeII accept altComplement typeII →
          hsame altComplement BHist.Empty →
            Cont reject budget ledger →
              Cont null ledger endpoint →
                Cont accept typeII joint →
                  Cont ledger joint surface →
                    hsame null null' →
                      hsame ledger ledger' →
                        hsame endpoint endpoint' →
                          hsame joint joint' →
                            hsame surface surface' →
                              hsame endpoint' (append null' ledger') ∧
                                hsame surface' (append ledger' joint') ∧
                                  UnaryHistory ledger' ∧ UnaryHistory joint' ∧
                                    UnaryHistory surface' := by
  -- BEDC touchpoint anchor: BHist Cont append hsame UnaryHistory ProbSpacePublicEventPacket
  intro nullPacket complementEmpty altPacket altComplementEmpty rejectBudget nullLedger
    acceptTypeII ledgerJoint sameNull sameLedger sameEndpoint sameJoint sameSurface
  have finite :
      hsame endpoint (append null ledger) ∧ hsame surface (append ledger joint) ∧
        UnaryHistory ledger ∧ UnaryHistory joint ∧ UnaryHistory surface :=
    HypothesisTestDecisionCarrier_finite_risk_boundary nullPacket complementEmpty
      altPacket altComplementEmpty rejectBudget nullLedger acceptTypeII ledgerJoint
  have endpointRead : hsame endpoint' (append null' ledger') := by
    cases sameNull
    cases sameLedger
    cases sameEndpoint
    exact finite.left
  have surfaceRead : hsame surface' (append ledger' joint') := by
    cases sameLedger
    cases sameJoint
    cases sameSurface
    exact finite.right.left
  have ledgerUnary : UnaryHistory ledger' :=
    unary_transport finite.right.right.left sameLedger
  have jointUnary : UnaryHistory joint' :=
    unary_transport finite.right.right.right.left sameJoint
  have surfaceUnary : UnaryHistory surface' :=
    unary_transport finite.right.right.right.right sameSurface
  exact ⟨endpointRead, surfaceRead, ledgerUnary, jointUnary, surfaceUnary⟩

end BEDC.Derived.HypothesisUp
