import BEDC.Derived.ConnectionUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.ConnectionUp

theorem CurvatureBracketCarrier_visible_ledger_coverage [AskSetup] [PackageSetup]
    {connection base fibre secRow tangentLeft tangentRight derivativeLeftRight
      derivativeRightLeft boundary ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory connection ->
      UnaryHistory base ->
        UnaryHistory fibre ->
          UnaryHistory secRow ->
            UnaryHistory tangentLeft ->
              UnaryHistory tangentRight ->
                UnaryHistory derivativeLeftRight ->
                  UnaryHistory derivativeRightLeft ->
                    UnaryHistory ledger ->
                      Cont derivativeLeftRight derivativeRightLeft boundary ->
                        Cont boundary ledger endpoint ->
                          PkgSig bundle endpoint pkg ->
                            UnaryHistory boundary ∧
                              UnaryHistory endpoint ∧
                                hsame boundary
                                  (append derivativeLeftRight derivativeRightLeft) ∧
                                  hsame endpoint
                                    (append (append derivativeLeftRight derivativeRightLeft)
                                      ledger) ∧
                                    PkgSig bundle endpoint pkg := by
  intro _connectionUnary _baseUnary _fibreUnary _secUnary _tangentLeftUnary
    _tangentRightUnary derivativeLeftRightUnary derivativeRightLeftUnary ledgerUnary
    boundaryCont endpointCont pkgSig
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed derivativeLeftRightUnary derivativeRightLeftUnary boundaryCont
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed boundaryUnary ledgerUnary endpointCont
  have endpointReadback :
      hsame endpoint (append (append derivativeLeftRight derivativeRightLeft) ledger) :=
    endpointCont.trans
      (congrArg (fun row : BHist => append row ledger) boundaryCont)
  exact And.intro boundaryUnary
    (And.intro endpointUnary
      (And.intro boundaryCont
        (And.intro endpointReadback pkgSig)))

theorem CurvatureCarrierPacket_connection_boundary_source_projection
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB boundary
      curvatureLedger : BHist} :
    ConnectionCarrierPacket base fibre sec tangentA derivativeA provenance ledgerA ->
      ConnectionCarrierPacket base fibre sec tangentB derivativeB provenance ledgerB ->
        Cont derivativeA derivativeB boundary ->
          Cont boundary provenance curvatureLedger ->
            UnaryHistory base ∧ UnaryHistory fibre ∧ UnaryHistory sec ∧
              UnaryHistory tangentA ∧ UnaryHistory tangentB ∧ UnaryHistory derivativeA ∧
                UnaryHistory derivativeB ∧ UnaryHistory boundary ∧
                  UnaryHistory curvatureLedger ∧
                    hsame curvatureLedger
                      (append (append (append base fibre) tangentA)
                        (append (append (append base fibre) tangentB) provenance)) := by
  intro packetA packetB boundaryCont curvatureCont
  have exactA :=
    ConnectionCarrierPacket_stability_ledger_exactness_obligation packetA
  have exactB :=
    ConnectionCarrierPacket_stability_ledger_exactness_obligation packetB
  have boundary :=
    ConnectionCarrierPacket_curvature_boundary_obligation packetA packetB boundaryCont curvatureCont
  exact And.intro packetA.left
    (And.intro packetA.right.left
      (And.intro exactA.left
        (And.intro packetA.right.right.left
          (And.intro packetB.right.right.left
            (And.intro exactA.right.left
              (And.intro exactB.right.left
                (And.intro boundary.left
                  (And.intro boundary.right.left boundary.right.right.right.right))))))))

theorem CurvatureBoundarySource_connection_projection
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB boundary
      curvatureLedger : BHist} :
    ConnectionCarrierPacket base fibre sec tangentA derivativeA provenance ledgerA ->
      ConnectionCarrierPacket base fibre sec tangentB derivativeB provenance ledgerB ->
        Cont derivativeA derivativeB boundary ->
          Cont boundary provenance curvatureLedger ->
            hsame ledgerA (append (append (append base fibre) tangentA) provenance) ∧
              hsame ledgerB (append (append (append base fibre) tangentB) provenance) ∧
                hsame boundary (append derivativeA derivativeB) ∧
                  hsame curvatureLedger (append boundary provenance) := by
  intro packetA packetB boundaryCont curvatureCont
  have exactA :=
    ConnectionCarrierPacket_stability_ledger_exactness_obligation packetA
  have exactB :=
    ConnectionCarrierPacket_stability_ledger_exactness_obligation packetB
  have boundaryRows :=
    ConnectionCarrierPacket_curvature_boundary_obligation packetA packetB boundaryCont curvatureCont
  exact And.intro exactA.right.right.right.right.right
    (And.intro exactB.right.right.right.right.right
      (And.intro boundaryRows.right.right.left boundaryRows.right.right.right.left))

def CurvatureBracketCarrier
    (base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB
      boundary curvatureLedger : BHist) : Prop :=
  ConnectionCarrierPacket base fibre sec tangentA derivativeA provenance ledgerA ∧
    ConnectionCarrierPacket base fibre sec tangentB derivativeB provenance ledgerB ∧
      Cont derivativeA derivativeB boundary ∧ Cont boundary provenance curvatureLedger

theorem CurvatureBracketCarrier_boundary_rows
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB
      boundary curvatureLedger : BHist} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance
        ledgerA ledgerB boundary curvatureLedger ->
      Cont derivativeA derivativeB boundary ∧ Cont boundary provenance curvatureLedger := by
  intro carrier
  exact carrier.right.right

theorem CurvatureBracketCarrier_boundary_source_obligation
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB boundary
      curvatureLedger : BHist} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA
      ledgerB boundary curvatureLedger ->
      UnaryHistory boundary ∧ UnaryHistory curvatureLedger ∧
        hsame boundary (append derivativeA derivativeB) ∧
          hsame curvatureLedger (append boundary provenance) := by
  intro carrier
  have boundaryProjection :=
    ConnectionCarrierPacket_curvature_boundary_obligation carrier.left carrier.right.left
      carrier.right.right.left carrier.right.right.right
  exact And.intro boundaryProjection.left
    (And.intro boundaryProjection.right.left
      (And.intro boundaryProjection.right.right.left boundaryProjection.right.right.right.left))

def CurvatureChernWeilSourceEnvelope [AskSetup] [PackageSetup]
    (curvatureLedger derham provenance connectionLedger classifier : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory curvatureLedger ∧ UnaryHistory derham ∧ UnaryHistory provenance ∧
    UnaryHistory connectionLedger ∧ UnaryHistory classifier ∧
      Cont curvatureLedger derham provenance ∧ Cont provenance connectionLedger classifier ∧
        hsame classifier (append (append curvatureLedger derham) connectionLedger) ∧
          PkgSig bundle classifier pkg

theorem CurvatureChernWeilSourceEnvelope_coverage [AskSetup] [PackageSetup]
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance0 ledgerA ledgerB boundary
      curvatureLedger derham provenance connectionLedger classifier : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance0
        ledgerA ledgerB boundary curvatureLedger ->
      UnaryHistory derham ->
        UnaryHistory connectionLedger ->
          Cont curvatureLedger derham provenance ->
            Cont provenance connectionLedger classifier ->
              PkgSig bundle classifier pkg ->
                CurvatureChernWeilSourceEnvelope curvatureLedger derham provenance
                    connectionLedger classifier bundle pkg ∧
                  hsame classifier (append (append curvatureLedger derham) connectionLedger) := by
  intro carrier derhamUnary connectionLedgerUnary provenanceCont classifierCont pkgSig
  have curvatureRows :=
    CurvatureBracketCarrier_boundary_source_obligation carrier
  have curvatureUnary : UnaryHistory curvatureLedger :=
    curvatureRows.right.left
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed curvatureUnary derhamUnary provenanceCont
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed provenanceUnary connectionLedgerUnary classifierCont
  have classifierReadback :
      hsame classifier (append (append curvatureLedger derham) connectionLedger) :=
    hsame_trans classifierCont
      (congrArg (fun row : BHist => append row connectionLedger) provenanceCont)
  have envelope :
      CurvatureChernWeilSourceEnvelope curvatureLedger derham provenance connectionLedger
        classifier bundle pkg :=
    And.intro curvatureUnary
      (And.intro derhamUnary
        (And.intro provenanceUnary
          (And.intro connectionLedgerUnary
            (And.intro classifierUnary
              (And.intro provenanceCont
                (And.intro classifierCont
                  (And.intro classifierReadback pkgSig)))))))
  exact And.intro envelope classifierReadback

theorem CurvatureChernWeilSourceEnvelope_consumer_stability [AskSetup] [PackageSetup]
    {curvature curvature' derham provenance connectionLedger classifier classifier' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CurvatureChernWeilSourceEnvelope curvature derham provenance connectionLedger classifier
        bundle pkg ->
      hsame curvature curvature' ->
        Cont curvature' derham provenance ->
          Cont provenance connectionLedger classifier' ->
            PkgSig bundle classifier' pkg ->
              CurvatureChernWeilSourceEnvelope curvature' derham provenance connectionLedger
                  classifier' bundle pkg ∧
                hsame classifier classifier' := by
  intro envelope sameCurvature provenanceCont' classifierCont' pkgSig'
  have curvatureUnary' : UnaryHistory curvature' :=
    unary_transport envelope.left sameCurvature
  have derhamUnary : UnaryHistory derham :=
    envelope.right.left
  have provenanceUnary : UnaryHistory provenance :=
    envelope.right.right.left
  have connectionLedgerUnary : UnaryHistory connectionLedger :=
    envelope.right.right.right.left
  have classifierUnary' : UnaryHistory classifier' :=
    unary_cont_closed provenanceUnary connectionLedgerUnary classifierCont'
  have sameClassifier : hsame classifier classifier' :=
    cont_respects_hsame (hsame_refl provenance) (hsame_refl connectionLedger)
      envelope.right.right.right.right.right.right.left classifierCont'
  have classifierReadback' :
      hsame classifier' (append (append curvature' derham) connectionLedger) :=
    hsame_trans classifierCont'
      (congrArg (fun row : BHist => append row connectionLedger) provenanceCont')
  have envelope' :
      CurvatureChernWeilSourceEnvelope curvature' derham provenance connectionLedger
        classifier' bundle pkg :=
    And.intro curvatureUnary'
      (And.intro derhamUnary
        (And.intro provenanceUnary
          (And.intro connectionLedgerUnary
            (And.intro classifierUnary'
              (And.intro provenanceCont'
                (And.intro classifierCont'
                  (And.intro classifierReadback' pkgSig')))))))
  exact And.intro envelope' sameClassifier

theorem CurvatureBracketCarrier_connection_classifier_stability
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB boundary
      curvatureLedger base' fibre' sec' tangentA' tangentB' derivativeA' derivativeB'
      provenance' ledgerA' ledgerB' boundary' curvatureLedger' : BHist} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance
        ledgerA ledgerB boundary curvatureLedger ->
      hsame base base' ->
        hsame fibre fibre' ->
          hsame sec sec' ->
            hsame tangentA tangentA' ->
              hsame tangentB tangentB' ->
                hsame derivativeA derivativeA' ->
                  hsame derivativeB derivativeB' ->
                    hsame provenance provenance' ->
                      ConnectionCarrierPacket base' fibre' sec' tangentA' derivativeA'
                          provenance' ledgerA' ->
                        ConnectionCarrierPacket base' fibre' sec' tangentB' derivativeB'
                            provenance' ledgerB' ->
                          Cont derivativeA' derivativeB' boundary' ->
                            Cont boundary' provenance' curvatureLedger' ->
                              CurvatureBracketCarrier base' fibre' sec' tangentA' tangentB'
                                  derivativeA' derivativeB' provenance' ledgerA' ledgerB'
                                  boundary' curvatureLedger' ∧
                                hsame boundary boundary' ∧
                                  hsame curvatureLedger curvatureLedger' := by
  intro carrier _sameBase _sameFibre _sameSec _sameTangentA _sameTangentB sameDerivativeA
    sameDerivativeB sameProvenance packetA' packetB' boundaryCont' curvatureCont'
  have carrier' :
      CurvatureBracketCarrier base' fibre' sec' tangentA' tangentB' derivativeA' derivativeB'
        provenance' ledgerA' ledgerB' boundary' curvatureLedger' :=
    And.intro packetA' (And.intro packetB' (And.intro boundaryCont' curvatureCont'))
  have sameBoundary : hsame boundary boundary' :=
    cont_respects_hsame sameDerivativeA sameDerivativeB carrier.right.right.left boundaryCont'
  have sameCurvature : hsame curvatureLedger curvatureLedger' :=
    cont_respects_hsame sameBoundary sameProvenance carrier.right.right.right curvatureCont'
  exact And.intro carrier' (And.intro sameBoundary sameCurvature)

theorem CurvatureBracketCarrier_tensorial_endpoint_transport
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB boundary
      curvatureLedger base' fibre' sec' tangentA' tangentB' derivativeA' derivativeB'
      provenance' ledgerA' ledgerB' boundary' curvatureLedger' : BHist} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance
        ledgerA ledgerB boundary curvatureLedger ->
      ConnectionCarrierPacket base' fibre' sec' tangentA' derivativeA' provenance' ledgerA' ->
        ConnectionCarrierPacket base' fibre' sec' tangentB' derivativeB' provenance' ledgerB' ->
          hsame derivativeA derivativeA' ->
            hsame derivativeB derivativeB' ->
              hsame provenance provenance' ->
                Cont derivativeA' derivativeB' boundary' ->
                  Cont boundary' provenance' curvatureLedger' ->
                    CurvatureBracketCarrier base' fibre' sec' tangentA' tangentB' derivativeA'
                        derivativeB' provenance' ledgerA' ledgerB' boundary' curvatureLedger' ∧
                      hsame boundary boundary' ∧ hsame curvatureLedger curvatureLedger' := by
  intro carrier packetA' packetB' sameDerivativeA sameDerivativeB sameProvenance
    boundaryCont' curvatureCont'
  have boundaryCont : Cont derivativeA derivativeB boundary :=
    carrier.right.right.left
  have curvatureCont : Cont boundary provenance curvatureLedger :=
    carrier.right.right.right
  have sameBoundary : hsame boundary boundary' :=
    cont_respects_hsame sameDerivativeA sameDerivativeB boundaryCont boundaryCont'
  have sameCurvatureLedger : hsame curvatureLedger curvatureLedger' :=
    cont_respects_hsame sameBoundary sameProvenance curvatureCont curvatureCont'
  have transported :
      CurvatureBracketCarrier base' fibre' sec' tangentA' tangentB' derivativeA' derivativeB'
        provenance' ledgerA' ledgerB' boundary' curvatureLedger' :=
    And.intro packetA' (And.intro packetB' (And.intro boundaryCont' curvatureCont'))
  exact And.intro transported (And.intro sameBoundary sameCurvatureLedger)

end BEDC.Derived.CurvatureUp
