import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ModelTheoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ModelTheoryBHistStructurePacket [AskSetup] [PackageSetup]
    (firstOrder structureRow valuation satisfaction elementary provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory firstOrder ∧
    UnaryHistory structureRow ∧
      UnaryHistory satisfaction ∧
        UnaryHistory elementary ∧
          Cont firstOrder structureRow valuation ∧
            Cont valuation satisfaction provenance ∧
              Cont provenance elementary endpoint ∧
                PkgSig bundle endpoint pkg

theorem ModelTheoryBHistStructurePacket_firstorder_dependency_surface [AskSetup]
    [PackageSetup]
    {firstOrder structureRow valuation satisfaction elementary provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModelTheoryBHistStructurePacket firstOrder structureRow valuation satisfaction elementary
      provenance endpoint bundle pkg ->
        UnaryHistory firstOrder ∧
          UnaryHistory structureRow ∧
            hsame valuation (append firstOrder structureRow) ∧
              hsame provenance (append valuation satisfaction) ∧
                hsame endpoint (append provenance elementary) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  exact
    And.intro packet.left
      (And.intro packet.right.left
          (And.intro packet.right.right.right.right.left
            (And.intro packet.right.right.right.right.right.left
              (And.intro packet.right.right.right.right.right.right.left
                packet.right.right.right.right.right.right.right))))

theorem ModelTheoryBHistStructurePacket_satisfaction_exactness_ledger [AskSetup] [PackageSetup]
    {firstOrder structureRow valuation satisfaction elementary provenance endpoint
      elementaryLedger exactnessLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModelTheoryBHistStructurePacket firstOrder structureRow valuation satisfaction elementary
        provenance endpoint bundle pkg ->
      Cont satisfaction elementary elementaryLedger ->
        Cont valuation elementaryLedger exactnessLedger ->
          UnaryHistory valuation ∧ UnaryHistory elementaryLedger ∧ UnaryHistory exactnessLedger ∧
            hsame elementaryLedger (append satisfaction elementary) ∧
              hsame exactnessLedger (append valuation (append satisfaction elementary)) ∧
                hsame endpoint (append provenance elementary) ∧ PkgSig bundle endpoint pkg := by
  intro packet elementaryLedgerRow exactnessLedgerRow
  have valuationUnary : UnaryHistory valuation :=
    unary_cont_closed packet.left packet.right.left packet.right.right.right.right.left
  have elementaryLedgerUnary : UnaryHistory elementaryLedger :=
    unary_cont_closed packet.right.right.left packet.right.right.right.left elementaryLedgerRow
  have exactnessLedgerUnary : UnaryHistory exactnessLedger :=
    unary_cont_closed valuationUnary elementaryLedgerUnary exactnessLedgerRow
  have exactnessReadback :
      hsame exactnessLedger (append valuation (append satisfaction elementary)) :=
    hsame_trans exactnessLedgerRow
      (congrArg (fun h : BHist => append valuation h) elementaryLedgerRow)
  exact And.intro valuationUnary
    (And.intro elementaryLedgerUnary
      (And.intro exactnessLedgerUnary
        (And.intro elementaryLedgerRow
          (And.intro exactnessReadback
            (And.intro packet.right.right.right.right.right.right.left
              packet.right.right.right.right.right.right.right)))))

theorem ModelTheoryBHistStructurePacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {firstOrder structureRow valuation satisfaction elementary provenance endpoint
      elementaryLedger exactnessLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModelTheoryBHistStructurePacket firstOrder structureRow valuation satisfaction elementary
        provenance endpoint bundle pkg ->
      Cont satisfaction elementary elementaryLedger ->
        Cont valuation elementaryLedger exactnessLedger ->
          UnaryHistory firstOrder ∧ UnaryHistory structureRow ∧ UnaryHistory valuation ∧
            UnaryHistory satisfaction ∧ UnaryHistory elementary ∧ UnaryHistory provenance ∧
              UnaryHistory elementaryLedger ∧ UnaryHistory exactnessLedger ∧
                hsame valuation (append firstOrder structureRow) ∧
                  hsame provenance (append valuation satisfaction) ∧
                    hsame elementaryLedger (append satisfaction elementary) ∧
                      hsame exactnessLedger
                        (append valuation (append satisfaction elementary)) ∧
                        hsame endpoint (append provenance elementary) ∧
                          PkgSig bundle endpoint pkg := by
  intro packet elementaryLedgerRow exactnessLedgerRow
  have valuationRow : Cont firstOrder structureRow valuation :=
    packet.right.right.right.right.left
  have provenanceRow : Cont valuation satisfaction provenance :=
    packet.right.right.right.right.right.left
  have endpointRow : Cont provenance elementary endpoint :=
    packet.right.right.right.right.right.right.left
  have valuationUnary : UnaryHistory valuation :=
    unary_cont_closed packet.left packet.right.left valuationRow
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed valuationUnary packet.right.right.left provenanceRow
  have elementaryLedgerUnary : UnaryHistory elementaryLedger :=
    unary_cont_closed packet.right.right.left packet.right.right.right.left elementaryLedgerRow
  have exactnessLedgerUnary : UnaryHistory exactnessLedger :=
    unary_cont_closed valuationUnary elementaryLedgerUnary exactnessLedgerRow
  have exactnessReadback :
      hsame exactnessLedger (append valuation (append satisfaction elementary)) :=
    hsame_trans exactnessLedgerRow
      (congrArg (fun h : BHist => append valuation h) elementaryLedgerRow)
  exact And.intro packet.left
    (And.intro packet.right.left
      (And.intro valuationUnary
        (And.intro packet.right.right.left
          (And.intro packet.right.right.right.left
            (And.intro provenanceUnary
              (And.intro elementaryLedgerUnary
                (And.intro exactnessLedgerUnary
                  (And.intro valuationRow
                    (And.intro provenanceRow
                      (And.intro elementaryLedgerRow
                        (And.intro exactnessReadback
                          (And.intro endpointRow
                            packet.right.right.right.right.right.right.right))))))))))))

theorem ModelTheoryBHistStructurePacket_satisfaction_exactness_row [AskSetup] [PackageSetup]
    {firstOrder structureRow valuation satisfaction elementary provenance endpoint formula formulaRead
      assignmentRead satisfactionRecord : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModelTheoryBHistStructurePacket firstOrder structureRow valuation satisfaction elementary
        provenance endpoint bundle pkg ->
      UnaryHistory formula ->
        Cont firstOrder formula formulaRead ->
          Cont valuation formulaRead assignmentRead ->
            Cont assignmentRead satisfaction satisfactionRecord ->
              UnaryHistory formulaRead ∧ UnaryHistory assignmentRead ∧
                UnaryHistory satisfactionRecord ∧
                  hsame formulaRead (append firstOrder formula) ∧
                    hsame assignmentRead (append valuation (append firstOrder formula)) ∧
                      hsame satisfactionRecord
                        (append (append valuation (append firstOrder formula)) satisfaction) ∧
                        PkgSig bundle endpoint pkg := by
  intro packet formulaUnary formulaRow assignmentRow satisfactionRow
  have valuationUnary : UnaryHistory valuation :=
    unary_cont_closed packet.left packet.right.left packet.right.right.right.right.left
  have formulaReadUnary : UnaryHistory formulaRead :=
    unary_cont_closed packet.left formulaUnary formulaRow
  have assignmentReadUnary : UnaryHistory assignmentRead :=
    unary_cont_closed valuationUnary formulaReadUnary assignmentRow
  have satisfactionRecordUnary : UnaryHistory satisfactionRecord :=
    unary_cont_closed assignmentReadUnary packet.right.right.left satisfactionRow
  have assignmentReadback : hsame assignmentRead (append valuation (append firstOrder formula)) :=
    hsame_trans assignmentRow (congrArg (fun row : BHist => append valuation row) formulaRow)
  have satisfactionReadback :
      hsame satisfactionRecord (append (append valuation (append firstOrder formula)) satisfaction) :=
    hsame_trans satisfactionRow
      (congrArg (fun row : BHist => append row satisfaction) assignmentReadback)
  exact And.intro formulaReadUnary
    (And.intro assignmentReadUnary
      (And.intro satisfactionRecordUnary
        (And.intro formulaRow
          (And.intro assignmentReadback
            (And.intro satisfactionReadback
              packet.right.right.right.right.right.right.right)))))

theorem ModelTheoryBHistStructurePacket_elementary_transport [AskSetup] [PackageSetup]
    {firstOrder structureRow valuation satisfaction elementary provenance endpoint valuation'
      satisfaction' elementary' provenance' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModelTheoryBHistStructurePacket firstOrder structureRow valuation satisfaction elementary
        provenance endpoint bundle pkg ->
      hsame satisfaction satisfaction' ->
        hsame elementary elementary' ->
          Cont firstOrder structureRow valuation' ->
            Cont valuation' satisfaction' provenance' ->
              Cont provenance' elementary' endpoint' ->
                ModelTheoryBHistStructurePacket firstOrder structureRow valuation' satisfaction'
                    elementary' provenance' endpoint' bundle pkg ∧ hsame endpoint endpoint' := by
  intro packet sameSatisfaction sameElementary valuationCont' provenanceCont' endpointCont'
  have satisfactionUnary' : UnaryHistory satisfaction' :=
    unary_transport packet.right.right.left sameSatisfaction
  have elementaryUnary' : UnaryHistory elementary' :=
    unary_transport packet.right.right.right.left sameElementary
  have sameValuation : hsame valuation valuation' :=
    cont_respects_hsame (hsame_refl firstOrder) (hsame_refl structureRow)
      packet.right.right.right.right.left valuationCont'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameValuation sameSatisfaction
      packet.right.right.right.right.right.left provenanceCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameElementary
      packet.right.right.right.right.right.right.left endpointCont'
  have pkgSig : PkgSig bundle endpoint' pkg := by
    cases sameEndpoint
    exact packet.right.right.right.right.right.right.right
  exact And.intro
    (And.intro packet.left
      (And.intro packet.right.left
        (And.intro satisfactionUnary'
          (And.intro elementaryUnary'
            (And.intro valuationCont'
              (And.intro provenanceCont' (And.intro endpointCont' pkgSig)))))))
    sameEndpoint

theorem ModelTheoryBHistStructurePacket_elementary_ledger_coverage [AskSetup] [PackageSetup]
    {firstOrder structureRow valuation satisfaction elementary provenance endpoint elementaryRead
      elementaryEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModelTheoryBHistStructurePacket firstOrder structureRow valuation satisfaction elementary
        provenance endpoint bundle pkg ->
      Cont satisfaction elementary elementaryRead ->
        Cont elementaryRead provenance elementaryEndpoint ->
          UnaryHistory elementaryRead ∧ UnaryHistory elementaryEndpoint ∧
            hsame elementaryRead (append satisfaction elementary) ∧
              hsame elementaryEndpoint (append elementaryRead provenance) ∧
                hsame endpoint (append provenance elementary) ∧ PkgSig bundle endpoint pkg := by
  intro packet elementaryReadRow elementaryEndpointRow
  have valuationUnary : UnaryHistory valuation :=
    unary_cont_closed packet.left packet.right.left packet.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed valuationUnary packet.right.right.left
      packet.right.right.right.right.right.left
  have elementaryReadUnary : UnaryHistory elementaryRead :=
    unary_cont_closed packet.right.right.left packet.right.right.right.left elementaryReadRow
  have elementaryEndpointUnary : UnaryHistory elementaryEndpoint :=
    unary_cont_closed elementaryReadUnary provenanceUnary elementaryEndpointRow
  exact And.intro elementaryReadUnary
    (And.intro elementaryEndpointUnary
      (And.intro elementaryReadRow
        (And.intro elementaryEndpointRow
          (And.intro packet.right.right.right.right.right.right.left
            packet.right.right.right.right.right.right.right))))

theorem ModelTheoryBHistStructurePacket_satisfaction_exactness_scope [AskSetup]
    [PackageSetup]
    {firstOrder structureRow valuation satisfaction elementary provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModelTheoryBHistStructurePacket firstOrder structureRow valuation satisfaction elementary
      provenance endpoint bundle pkg ->
        UnaryHistory valuation ∧ UnaryHistory provenance ∧
          hsame valuation (append firstOrder structureRow) ∧
            hsame provenance (append valuation satisfaction) ∧
              hsame endpoint (append provenance elementary) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have valuationUnary : UnaryHistory valuation :=
    unary_cont_closed packet.left packet.right.left packet.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed valuationUnary packet.right.right.left
      packet.right.right.right.right.right.left
  exact And.intro valuationUnary
    (And.intro provenanceUnary
      (And.intro packet.right.right.right.right.left
        (And.intro packet.right.right.right.right.right.left
          (And.intro packet.right.right.right.right.right.right.left
            packet.right.right.right.right.right.right.right))))

theorem ModelTheoryBHistStructurePacket_carrier_classifier_stability [AskSetup] [PackageSetup]
    {firstOrder structureRow valuation satisfaction elementary provenance endpoint valuation'
      provenance' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModelTheoryBHistStructurePacket firstOrder structureRow valuation satisfaction elementary
        provenance endpoint bundle pkg ->
      Cont firstOrder structureRow valuation' ->
        Cont valuation' satisfaction provenance' ->
          Cont provenance' elementary endpoint' ->
            ModelTheoryBHistStructurePacket firstOrder structureRow valuation' satisfaction
                elementary provenance' endpoint' bundle pkg ∧
              hsame valuation valuation' ∧ hsame provenance provenance' ∧ hsame endpoint endpoint' := by
  intro packet valuationCont' provenanceCont' endpointCont'
  have sameValuation : hsame valuation valuation' :=
    cont_respects_hsame (hsame_refl firstOrder) (hsame_refl structureRow)
      packet.right.right.right.right.left valuationCont'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameValuation (hsame_refl satisfaction)
      packet.right.right.right.right.right.left provenanceCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance (hsame_refl elementary)
      packet.right.right.right.right.right.right.left endpointCont'
  have pkgSig' : PkgSig bundle endpoint' pkg := by
    cases sameEndpoint
    exact packet.right.right.right.right.right.right.right
  exact And.intro
    (And.intro packet.left
      (And.intro packet.right.left
        (And.intro packet.right.right.left
          (And.intro packet.right.right.right.left
            (And.intro valuationCont'
              (And.intro provenanceCont' (And.intro endpointCont' pkgSig')))))))
    (And.intro sameValuation (And.intro sameProvenance sameEndpoint))

theorem ModelTheoryBHistStructurePacket_downstream_consumer_row [AskSetup] [PackageSetup]
    {firstOrder structureRow valuation satisfaction elementary provenance endpoint formula formulaRead
      assignmentRead satisfactionRecord elementaryRead elementaryEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModelTheoryBHistStructurePacket firstOrder structureRow valuation satisfaction elementary
        provenance endpoint bundle pkg ->
      UnaryHistory formula ->
        Cont firstOrder formula formulaRead ->
          Cont valuation formulaRead assignmentRead ->
            Cont assignmentRead satisfaction satisfactionRecord ->
              Cont satisfaction elementary elementaryRead ->
                Cont elementaryRead provenance elementaryEndpoint ->
                  UnaryHistory firstOrder ∧ UnaryHistory structureRow ∧ UnaryHistory valuation ∧
                    UnaryHistory satisfaction ∧ UnaryHistory elementary ∧ UnaryHistory formulaRead ∧
                      UnaryHistory assignmentRead ∧ UnaryHistory satisfactionRecord ∧
                        UnaryHistory elementaryRead ∧ UnaryHistory elementaryEndpoint ∧
                          hsame formulaRead (append firstOrder formula) ∧
                            hsame assignmentRead (append valuation (append firstOrder formula)) ∧
                              hsame satisfactionRecord
                                (append (append valuation (append firstOrder formula))
                                  satisfaction) ∧
                                hsame elementaryRead (append satisfaction elementary) ∧
                                  hsame elementaryEndpoint (append elementaryRead provenance) ∧
                                    PkgSig bundle endpoint pkg := by
  intro packet formulaUnary formulaRow assignmentRow satisfactionRow elementaryReadRow
    elementaryEndpointRow
  have satisfactionExact :=
    ModelTheoryBHistStructurePacket_satisfaction_exactness_row
      (firstOrder := firstOrder) (structureRow := structureRow) (valuation := valuation)
      (satisfaction := satisfaction) (elementary := elementary) (provenance := provenance)
      (endpoint := endpoint) (formula := formula) (formulaRead := formulaRead)
      (assignmentRead := assignmentRead) (satisfactionRecord := satisfactionRecord)
      (bundle := bundle) (pkg := pkg) packet formulaUnary formulaRow assignmentRow satisfactionRow
  have elementaryCoverage :=
    ModelTheoryBHistStructurePacket_elementary_ledger_coverage
      (firstOrder := firstOrder) (structureRow := structureRow) (valuation := valuation)
      (satisfaction := satisfaction) (elementary := elementary) (provenance := provenance)
      (endpoint := endpoint) (elementaryRead := elementaryRead)
      (elementaryEndpoint := elementaryEndpoint) (bundle := bundle) (pkg := pkg) packet
      elementaryReadRow elementaryEndpointRow
  have valuationUnary : UnaryHistory valuation :=
    unary_cont_closed packet.left packet.right.left packet.right.right.right.right.left
  exact And.intro packet.left
    (And.intro packet.right.left
      (And.intro valuationUnary
        (And.intro packet.right.right.left
          (And.intro packet.right.right.right.left
            (And.intro satisfactionExact.left
              (And.intro satisfactionExact.right.left
                (And.intro satisfactionExact.right.right.left
                  (And.intro elementaryCoverage.left
                    (And.intro elementaryCoverage.right.left
                      (And.intro satisfactionExact.right.right.right.left
                        (And.intro satisfactionExact.right.right.right.right.left
                          (And.intro satisfactionExact.right.right.right.right.right.left
                            (And.intro elementaryCoverage.right.right.left
                              (And.intro elementaryCoverage.right.right.right.left
                                satisfactionExact.right.right.right.right.right.right))))))))))))))

def ModelTheoryElementaryReadbackLedgerSpine (start : BHist) : List BHist -> BHist -> Prop
  | [], final => hsame final start
  | row :: rows, final =>
      UnaryHistory row ∧
        exists next : BHist, Cont start row next ∧
          ModelTheoryElementaryReadbackLedgerSpine next rows final

private theorem ModelTheoryElementaryReadbackLedgerSpine_normalized_cont_aux
    {start final : BHist} {rows : List BHist} :
    ModelTheoryElementaryReadbackLedgerSpine start rows final ->
      exists ledger : BHist, UnaryHistory ledger ∧ Cont start ledger final := by
  intro spine
  induction rows generalizing start final with
  | nil =>
      exact Exists.intro BHist.Empty (And.intro unary_empty spine)
  | cons row rows ih =>
      cases spine with
      | intro rowUnary nextData =>
          cases nextData with
          | intro next nextRows =>
              cases nextRows with
              | intro rowCont tailSpine =>
                  have tailPack := ih tailSpine
                  cases tailPack with
                  | intro tail tailRows =>
                      have ledgerUnary : UnaryHistory (append row tail) :=
                        unary_append_closed rowUnary tailRows.left
                      have ledgerCont : Cont start (append row tail) final :=
                        hsame_trans tailRows.right
                          ((congrArg (fun h : BHist => append h tail) rowCont).trans
                            (append_assoc start row tail))
                      exact Exists.intro (append row tail) (And.intro ledgerUnary ledgerCont)

theorem ModelTheoryElementaryReadbackLedgerSpine_normalized_cont [AskSetup] [PackageSetup]
    {satisfaction elementary final : BHist} {rows : List BHist} :
    ModelTheoryElementaryReadbackLedgerSpine elementary rows final ->
      hsame elementary (append satisfaction elementary) ->
        exists ledger : BHist, UnaryHistory ledger ∧
          Cont (append satisfaction elementary) ledger final := by
  intro spine elementaryNormalized
  have ledgerPack := ModelTheoryElementaryReadbackLedgerSpine_normalized_cont_aux spine
  cases ledgerPack with
  | intro ledger ledgerRows =>
      have ledgerCont : Cont (append satisfaction elementary) ledger final :=
        hsame_trans ledgerRows.right
          (congrArg (fun h : BHist => append h ledger) elementaryNormalized)
      exact Exists.intro ledger (And.intro ledgerRows.left ledgerCont)

end BEDC.Derived.ModelTheoryUp
