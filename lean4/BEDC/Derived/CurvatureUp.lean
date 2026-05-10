import BEDC.Derived.ConnectionUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem CurvatureBracketCarrier_boundary_row_determinacy
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB boundary
      boundaryPrime curvatureLedger curvatureLedgerPrime : BHist} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA
        ledgerB boundary curvatureLedger ->
      CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA
          ledgerB boundaryPrime curvatureLedgerPrime ->
        Cont derivativeA derivativeB boundary ∧
          Cont derivativeA derivativeB boundaryPrime ∧
            Cont boundary provenance curvatureLedger ∧
              Cont boundaryPrime provenance curvatureLedgerPrime ∧
                hsame boundary boundaryPrime ∧ hsame curvatureLedger curvatureLedgerPrime := by
  intro carrier carrierPrime
  have boundaryCont : Cont derivativeA derivativeB boundary :=
    carrier.right.right.left
  have boundaryContPrime : Cont derivativeA derivativeB boundaryPrime :=
    carrierPrime.right.right.left
  have curvatureCont : Cont boundary provenance curvatureLedger :=
    carrier.right.right.right
  have curvatureContPrime : Cont boundaryPrime provenance curvatureLedgerPrime :=
    carrierPrime.right.right.right
  have sameBoundary : hsame boundary boundaryPrime :=
    cont_deterministic boundaryCont boundaryContPrime
  have sameCurvatureLedger : hsame curvatureLedger curvatureLedgerPrime :=
    cont_respects_hsame sameBoundary (hsame_refl provenance) curvatureCont curvatureContPrime
  exact And.intro boundaryCont
    (And.intro boundaryContPrime
      (And.intro curvatureCont
        (And.intro curvatureContPrime
          (And.intro sameBoundary sameCurvatureLedger))))

theorem CurvatureBracketCarrier_antisymmetric_bracket_obligation
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB boundary
      swappedBoundary curvatureLedger swappedCurvatureLedger : BHist} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance
        ledgerA ledgerB boundary curvatureLedger ->
      Cont derivativeB derivativeA swappedBoundary ->
        Cont swappedBoundary provenance swappedCurvatureLedger ->
          CurvatureBracketCarrier base fibre sec tangentB tangentA derivativeB derivativeA
              provenance ledgerB ledgerA swappedBoundary swappedCurvatureLedger ∧
            hsame boundary swappedBoundary ∧ hsame curvatureLedger swappedCurvatureLedger := by
  intro carrier swappedBoundaryCont swappedCurvatureCont
  have exactA :=
    ConnectionCarrierPacket_stability_ledger_exactness_obligation carrier.left
  have exactB :=
    ConnectionCarrierPacket_stability_ledger_exactness_obligation carrier.right.left
  have sameBoundary : hsame boundary swappedBoundary :=
    unary_cont_comm exactA.right.left exactB.right.left carrier.right.right.left
      swappedBoundaryCont
  have sameCurvatureLedger : hsame curvatureLedger swappedCurvatureLedger :=
    cont_respects_hsame sameBoundary (hsame_refl provenance) carrier.right.right.right
      swappedCurvatureCont
  have swappedCarrier :
      CurvatureBracketCarrier base fibre sec tangentB tangentA derivativeB derivativeA
        provenance ledgerB ledgerA swappedBoundary swappedCurvatureLedger :=
    And.intro carrier.right.left
      (And.intro carrier.left (And.intro swappedBoundaryCont swappedCurvatureCont))
  exact And.intro swappedCarrier (And.intro sameBoundary sameCurvatureLedger)

theorem CurvatureBracketCarrier_source_row_coverage
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB boundary
      curvatureLedger : BHist} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance
        ledgerA ledgerB boundary curvatureLedger ->
      ConnectionCarrierPacket base fibre sec tangentA derivativeA provenance ledgerA ∧
        ConnectionCarrierPacket base fibre sec tangentB derivativeB provenance ledgerB ∧
          Cont derivativeA derivativeB boundary ∧
            Cont boundary provenance curvatureLedger ∧
              UnaryHistory boundary ∧
                UnaryHistory curvatureLedger ∧
                  hsame boundary (append derivativeA derivativeB) ∧
                    hsame curvatureLedger (append boundary provenance) := by
  intro carrier
  have boundaryRows :=
    CurvatureBracketCarrier_boundary_source_obligation carrier
  exact And.intro carrier.left
    (And.intro carrier.right.left
      (And.intro carrier.right.right.left
        (And.intro carrier.right.right.right
          (And.intro boundaryRows.left
            (And.intro boundaryRows.right.left
              (And.intro boundaryRows.right.right.left boundaryRows.right.right.right))))))

theorem CurvatureBracketCarrier_semantic_name_certificate
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB boundary
      curvatureLedger : BHist} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance
        ledgerA ledgerB boundary curvatureLedger ->
      SemanticNameCert (fun e : BHist => exists b : BHist, CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB b e) (fun e : BHist => exists b : BHist, CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB b e) (fun e : BHist => exists b : BHist, CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB b e)
        (fun left right : BHist => (exists lb : BHist, CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB lb left) /\ (exists rb : BHist, CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB rb right) /\ hsame left right) := by
  intro carrier
  exact {
    core := { carrier_inhabited := Exists.intro curvatureLedger (Exists.intro boundary carrier), equiv_refl := by intro h source; exact And.intro source (And.intro source (hsame_refl h)), equiv_symm := by intro h k classified; exact And.intro classified.right.left (And.intro classified.left (hsame_symm classified.right.right)), equiv_trans := by intro h k r classifiedHK classifiedKR; exact And.intro classifiedHK.left (And.intro classifiedKR.right.left (hsame_trans classifiedHK.right.right classifiedKR.right.right)), carrier_respects_equiv := by intro h k classified _source; exact classified.right.left }
    pattern_sound := by intro h source; exact source
    ledger_sound := by intro h source; exact source
  }

theorem CurvatureBracketCarrier_classifier_transport_row
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB boundary
      curvatureLedger boundary' curvatureLedger' : BHist} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA
        ledgerB boundary curvatureLedger ->
      hsame boundary boundary' ->
        Cont boundary' provenance curvatureLedger' ->
          CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance
              ledgerA ledgerB boundary' curvatureLedger' ∧
            hsame curvatureLedger curvatureLedger' := by
  intro carrier sameBoundary curvatureCont'
  have boundaryCont' : Cont derivativeA derivativeB boundary' :=
    cont_result_hsame_transport carrier.right.right.left sameBoundary
  have sameCurvature : hsame curvatureLedger curvatureLedger' :=
    cont_respects_hsame sameBoundary (hsame_refl provenance) carrier.right.right.right
      curvatureCont'
  exact And.intro
    (And.intro carrier.left
      (And.intro carrier.right.left
        (And.intro boundaryCont' curvatureCont')))
    sameCurvature

theorem CurvatureBracketCarrier_bianchi_ledger_obligation
    {base fibre sec tangentA tangentB tangentC derivativeAB derivativeBC derivativeCA provenance
      ledgerA ledgerB ledgerC boundaryAB boundaryBC boundaryCA curvatureAB curvatureBC curvatureCA
      bianchiAB bianchiLedger : BHist} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeAB derivativeBC provenance
        ledgerA ledgerB boundaryAB curvatureAB ->
      CurvatureBracketCarrier base fibre sec tangentB tangentC derivativeBC derivativeCA provenance
          ledgerB ledgerC boundaryBC curvatureBC ->
        CurvatureBracketCarrier base fibre sec tangentC tangentA derivativeCA derivativeAB provenance
            ledgerC ledgerA boundaryCA curvatureCA ->
          Cont boundaryAB boundaryBC bianchiAB ->
            Cont bianchiAB boundaryCA bianchiLedger ->
              UnaryHistory boundaryAB ∧ UnaryHistory boundaryBC ∧ UnaryHistory boundaryCA ∧
                UnaryHistory bianchiAB ∧ UnaryHistory bianchiLedger ∧
                  hsame bianchiLedger (append (append boundaryAB boundaryBC) boundaryCA) := by
  intro carrierAB carrierBC carrierCA bianchiABCont bianchiLedgerCont
  have rowsAB := CurvatureBracketCarrier_boundary_source_obligation carrierAB
  have rowsBC := CurvatureBracketCarrier_boundary_source_obligation carrierBC
  have rowsCA := CurvatureBracketCarrier_boundary_source_obligation carrierCA
  have bianchiABUnary : UnaryHistory bianchiAB :=
    unary_cont_closed rowsAB.left rowsBC.left bianchiABCont
  have bianchiLedgerUnary : UnaryHistory bianchiLedger :=
    unary_cont_closed bianchiABUnary rowsCA.left bianchiLedgerCont
  have bianchiLedgerReadback :
      hsame bianchiLedger (append (append boundaryAB boundaryBC) boundaryCA) :=
    hsame_trans bianchiLedgerCont
      (congrArg (fun row : BHist => append row boundaryCA) bianchiABCont)
  exact And.intro rowsAB.left
    (And.intro rowsBC.left
      (And.intro rowsCA.left
        (And.intro bianchiABUnary
          (And.intro bianchiLedgerUnary bianchiLedgerReadback))))

theorem CurvatureBracketCarrier_boundary_determinacy
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB boundary
      boundary' curvatureLedger curvatureLedger' : BHist} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA
        ledgerB boundary curvatureLedger ->
      Cont derivativeA derivativeB boundary' ->
        Cont boundary' provenance curvatureLedger' ->
          hsame boundary boundary' ∧ hsame curvatureLedger curvatureLedger' := by
  intro carrier boundaryCont' curvatureCont'
  have sameBoundary : hsame boundary boundary' :=
    cont_deterministic carrier.right.right.left boundaryCont'
  have sameCurvature : hsame curvatureLedger curvatureLedger' :=
    cont_respects_hsame sameBoundary (hsame_refl provenance) carrier.right.right.right
      curvatureCont'
  exact And.intro sameBoundary sameCurvature

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

theorem CurvatureChernWeilSourceEnvelope_curvature_transport [AskSetup] [PackageSetup]
    {curvatureLedger curvatureLedger' derham provenance provenance' connectionLedger classifier
      classifier' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CurvatureChernWeilSourceEnvelope curvatureLedger derham provenance connectionLedger classifier
        bundle pkg ->
      hsame curvatureLedger curvatureLedger' ->
        Cont curvatureLedger' derham provenance' ->
          Cont provenance' connectionLedger classifier' ->
            PkgSig bundle classifier' pkg ->
              CurvatureChernWeilSourceEnvelope curvatureLedger' derham provenance'
                  connectionLedger classifier' bundle pkg ∧
                hsame provenance provenance' ∧ hsame classifier classifier' := by
  intro envelope sameCurvature provenanceCont' classifierCont' pkgSig'
  have curvatureUnary' : UnaryHistory curvatureLedger' :=
    unary_transport envelope.left sameCurvature
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed curvatureUnary' envelope.right.left provenanceCont'
  have classifierUnary' : UnaryHistory classifier' :=
    unary_cont_closed provenanceUnary' envelope.right.right.right.left classifierCont'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameCurvature (hsame_refl derham)
      envelope.right.right.right.right.right.left provenanceCont'
  have sameClassifier : hsame classifier classifier' :=
    cont_respects_hsame sameProvenance (hsame_refl connectionLedger)
      envelope.right.right.right.right.right.right.left classifierCont'
  have classifierReadback' :
      hsame classifier' (append (append curvatureLedger' derham) connectionLedger) :=
    classifierCont'.trans
      (congrArg (fun row : BHist => append row connectionLedger) provenanceCont')
  have envelope' :
      CurvatureChernWeilSourceEnvelope curvatureLedger' derham provenance' connectionLedger
        classifier' bundle pkg :=
    And.intro curvatureUnary'
      (And.intro envelope.right.left
        (And.intro provenanceUnary'
          (And.intro envelope.right.right.right.left
            (And.intro classifierUnary'
              (And.intro provenanceCont'
                (And.intro classifierCont'
                  (And.intro classifierReadback' pkgSig')))))))
  exact And.intro envelope' (And.intro sameProvenance sameClassifier)

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

theorem CurvatureBracketCarrier_bianchi_ledger_row
    {base fibre sec tangentA tangentB tangentC derivativeAB derivativeBC derivativeCA provenance
      ledgerAB ledgerBC ledgerCA boundaryAB boundaryBC boundaryCA curvatureAB curvatureBC
      curvatureCA pair cyclic : BHist} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeAB derivativeBC provenance
        ledgerAB ledgerBC boundaryAB curvatureAB ->
      CurvatureBracketCarrier base fibre sec tangentB tangentC derivativeBC derivativeCA provenance
          ledgerBC ledgerCA boundaryBC curvatureBC ->
        CurvatureBracketCarrier base fibre sec tangentC tangentA derivativeCA derivativeAB provenance
            ledgerCA ledgerAB boundaryCA curvatureCA ->
          Cont boundaryAB boundaryBC pair ->
            Cont pair boundaryCA cyclic ->
              UnaryHistory boundaryAB ∧ UnaryHistory boundaryBC ∧ UnaryHistory boundaryCA ∧
                hsame pair (append boundaryAB boundaryBC) ∧
                  hsame cyclic (append (append boundaryAB boundaryBC) boundaryCA) := by
  intro carrierAB carrierBC carrierCA pairCont cyclicCont
  have rowsAB := CurvatureBracketCarrier_boundary_source_obligation carrierAB
  have rowsBC := CurvatureBracketCarrier_boundary_source_obligation carrierBC
  have rowsCA := CurvatureBracketCarrier_boundary_source_obligation carrierCA
  have cyclicReadback : hsame cyclic (append (append boundaryAB boundaryBC) boundaryCA) :=
    cyclicCont.trans (congrArg (fun row : BHist => append row boundaryCA) pairCont)
  exact And.intro rowsAB.left
    (And.intro rowsBC.left
      (And.intro rowsCA.left
        (And.intro pairCont cyclicReadback)))

theorem CurvatureChernWeilHandoffPacket_bianchi_transport [AskSetup] [PackageSetup]
    {base fibre sec tangentA tangentB derivativeA derivativeB derivativeA' derivativeB'
      provenance ledgerA ledgerB ledgerA' ledgerB' boundary curvatureLedger boundary'
      curvatureLedger' derham provenanceCW provenanceCW' connectionLedger classifier
      classifier' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance
        ledgerA ledgerB boundary curvatureLedger ->
      ConnectionCarrierPacket base fibre sec tangentA derivativeA' provenance ledgerA' ->
        ConnectionCarrierPacket base fibre sec tangentB derivativeB' provenance ledgerB' ->
          hsame derivativeA derivativeA' ->
            hsame derivativeB derivativeB' ->
              Cont derivativeA' derivativeB' boundary' ->
                Cont boundary' provenance curvatureLedger' ->
                  CurvatureChernWeilSourceEnvelope curvatureLedger derham provenanceCW
                      connectionLedger classifier bundle pkg ->
                    Cont curvatureLedger' derham provenanceCW' ->
                      Cont provenanceCW' connectionLedger classifier' ->
                        PkgSig bundle classifier' pkg ->
                          CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA'
                              derivativeB' provenance ledgerA' ledgerB' boundary' curvatureLedger' ∧
                            CurvatureChernWeilSourceEnvelope curvatureLedger' derham
                              provenanceCW' connectionLedger classifier' bundle pkg ∧
                              hsame curvatureLedger curvatureLedger' := by
  intro carrier packetA' packetB' sameDerivativeA sameDerivativeB boundaryCont'
    curvatureCont' envelope provenanceCont' classifierCont' pkgSig'
  have transported :=
    CurvatureBracketCarrier_tensorial_endpoint_transport carrier packetA' packetB'
      sameDerivativeA sameDerivativeB (hsame_refl provenance) boundaryCont' curvatureCont'
  have curvatureRows :=
    CurvatureBracketCarrier_boundary_source_obligation transported.left
  have provenanceUnary' : UnaryHistory provenanceCW' :=
    unary_cont_closed curvatureRows.right.left envelope.right.left provenanceCont'
  have classifierUnary' : UnaryHistory classifier' :=
    unary_cont_closed provenanceUnary' envelope.right.right.right.left classifierCont'
  have classifierReadback' :
      hsame classifier' (append (append curvatureLedger' derham) connectionLedger) :=
    hsame_trans classifierCont'
      (congrArg (fun row : BHist => append row connectionLedger) provenanceCont')
  have envelope' :
      CurvatureChernWeilSourceEnvelope curvatureLedger' derham provenanceCW' connectionLedger
        classifier' bundle pkg :=
    And.intro curvatureRows.right.left
      (And.intro envelope.right.left
        (And.intro provenanceUnary'
          (And.intro envelope.right.right.right.left
            (And.intro classifierUnary'
              (And.intro provenanceCont'
                (And.intro classifierCont'
                  (And.intro classifierReadback' pkgSig')))))))
  exact And.intro transported.left
    (And.intro envelope' transported.right.right)

end BEDC.Derived.CurvatureUp
