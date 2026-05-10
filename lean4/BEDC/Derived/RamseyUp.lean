import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RamseyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RamseyColouringCarrier [AskSetup] [PackageSetup]
    (vertexSpine subsetSpine colourTable witnessRows transportRows lookupRoutes provenance
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory vertexSpine ∧ UnaryHistory subsetSpine ∧ UnaryHistory colourTable ∧
    UnaryHistory transportRows ∧ UnaryHistory provenance ∧ UnaryHistory endpoint ∧
      Cont vertexSpine subsetSpine lookupRoutes ∧
        Cont lookupRoutes colourTable witnessRows ∧
          Cont witnessRows transportRows provenance ∧
            Cont provenance transportRows endpoint ∧ PkgSig bundle endpoint pkg

theorem RamseyColouringCarrier_witness_scope [AskSetup] [PackageSetup]
    {vertex subset colour witnessRows transportRows lookup provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RamseyColouringCarrier vertex subset colour witnessRows transportRows lookup provenance
        endpoint bundle pkg ->
      UnaryHistory vertex ∧ UnaryHistory subset ∧ UnaryHistory colour ∧
        UnaryHistory transportRows ∧ UnaryHistory provenance ∧ UnaryHistory lookup ∧
          UnaryHistory witnessRows ∧ UnaryHistory endpoint ∧ Cont vertex subset lookup ∧
            Cont lookup colour witnessRows ∧ Cont witnessRows transportRows provenance ∧
              Cont provenance transportRows endpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  have vertexUnary : UnaryHistory vertex := carrier.left
  have subsetUnary : UnaryHistory subset := carrier.right.left
  have colourUnary : UnaryHistory colour := carrier.right.right.left
  have transportUnary : UnaryHistory transportRows := carrier.right.right.right.left
  have provenanceUnary : UnaryHistory provenance := carrier.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint := carrier.right.right.right.right.right.left
  have lookupRoute : Cont vertex subset lookup :=
    carrier.right.right.right.right.right.right.left
  have witnessRoute : Cont lookup colour witnessRows :=
    carrier.right.right.right.right.right.right.right.left
  have provenanceRoute : Cont witnessRows transportRows provenance :=
    carrier.right.right.right.right.right.right.right.right.left
  have endpointRoute : Cont provenance transportRows endpoint :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have endpointPkg : PkgSig bundle endpoint pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right
  have lookupUnary : UnaryHistory lookup :=
    unary_cont_closed vertexUnary subsetUnary lookupRoute
  have witnessUnary : UnaryHistory witnessRows :=
    unary_cont_closed lookupUnary colourUnary witnessRoute
  exact
    ⟨vertexUnary,
      subsetUnary,
      colourUnary,
      transportUnary,
      provenanceUnary,
      lookupUnary,
      witnessUnary,
      endpointUnary,
      lookupRoute,
      witnessRoute,
      provenanceRoute,
      endpointRoute,
      endpointPkg⟩

theorem RamseyColouringCarrier_monochrome_classifier_stability [AskSetup] [PackageSetup]
    {vertex subset colour lookup provenance endpoint vertex' subset' colour' lookup'
      provenance' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RamseyColouringCarrier vertex subset colour endpoint BHist.Empty lookup provenance
        endpoint bundle pkg ->
      hsame vertex vertex' ->
        hsame subset subset' ->
          hsame colour colour' ->
            hsame provenance provenance' ->
              Cont vertex' subset' lookup' ->
                Cont lookup' colour' endpoint' ->
                  PkgSig bundle endpoint' pkg ->
                    RamseyColouringCarrier vertex' subset' colour' endpoint' BHist.Empty
                        lookup' provenance' endpoint' bundle pkg ∧ hsame lookup lookup' ∧
                      hsame endpoint endpoint' := by
  intro carrier sameVertex sameSubset sameColour sameProvenance lookupRoute'
    endpointRoute' endpointPkg'
  have lookupRoute : Cont vertex subset lookup :=
    carrier.right.right.right.right.right.right.left
  have endpointRoute : Cont lookup colour endpoint :=
    carrier.right.right.right.right.right.right.right.left
  have sourceWitnessProvenance : Cont endpoint BHist.Empty provenance :=
    carrier.right.right.right.right.right.right.right.right.left
  have sourceProvenanceEndpoint : Cont provenance BHist.Empty endpoint :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have sameLookup : hsame lookup lookup' :=
    cont_respects_hsame sameVertex sameSubset lookupRoute lookupRoute'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameLookup sameColour endpointRoute endpointRoute'
  have witnessProvenance' : Cont endpoint' BHist.Empty provenance' :=
    hsame_trans (hsame_symm sameProvenance)
      (hsame_trans (cont_right_unit_result sourceWitnessProvenance) sameEndpoint)
  have provenanceEndpoint' : Cont provenance' BHist.Empty endpoint' :=
    hsame_trans (hsame_symm sameEndpoint)
      (hsame_trans (cont_right_unit_result sourceProvenanceEndpoint) sameProvenance)
  have transportedCarrier :
      RamseyColouringCarrier vertex' subset' colour' endpoint' BHist.Empty lookup'
        provenance' endpoint' bundle pkg :=
    ⟨unary_transport carrier.left sameVertex,
      unary_transport carrier.right.left sameSubset,
      unary_transport carrier.right.right.left sameColour,
      unary_empty,
      unary_transport carrier.right.right.right.right.left sameProvenance,
      unary_transport carrier.right.right.right.right.right.left sameEndpoint,
      lookupRoute',
      endpointRoute',
      witnessProvenance',
      provenanceEndpoint',
      endpointPkg'⟩
  exact And.intro transportedCarrier (And.intro sameLookup sameEndpoint)

theorem RamseyColouringCarrier_monochrome_witness_scope [AskSetup] [PackageSetup]
    {vertex subset colour lookup provenance endpoint witness consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RamseyColouringCarrier vertex subset colour endpoint BHist.Empty lookup provenance
        endpoint bundle pkg ->
      UnaryHistory witness ->
        Cont endpoint witness consumer ->
          UnaryHistory lookup ∧ UnaryHistory endpoint ∧ UnaryHistory consumer ∧
            hsame lookup (append vertex subset) ∧ hsame endpoint (append lookup colour) ∧
              hsame consumer (append endpoint witness) ∧ PkgSig bundle endpoint pkg := by
  intro carrier witnessUnary consumerRow
  have vertexUnary : UnaryHistory vertex := carrier.left
  have subsetUnary : UnaryHistory subset := carrier.right.left
  have colourUnary : UnaryHistory colour := carrier.right.right.left
  have lookupRow : Cont vertex subset lookup :=
    carrier.right.right.right.right.right.right.left
  have endpointRow : Cont lookup colour endpoint :=
    carrier.right.right.right.right.right.right.right.left
  have lookupUnary : UnaryHistory lookup :=
    unary_cont_closed vertexUnary subsetUnary lookupRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed lookupUnary colourUnary endpointRow
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed endpointUnary witnessUnary consumerRow
  exact
    ⟨lookupUnary,
      endpointUnary,
      consumerUnary,
      lookupRow,
      endpointRow,
      consumerRow,
      carrier.right.right.right.right.right.right.right.right.right.right⟩

theorem RamseyColouringCarrier_obligation_surface [AskSetup] [PackageSetup]
    {vertexSpine subsetSpine colorEndpoint lookupLedger provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory vertexSpine ->
      UnaryHistory subsetSpine ->
        UnaryHistory colorEndpoint ->
          Cont vertexSpine subsetSpine lookupLedger ->
            Cont lookupLedger colorEndpoint provenance ->
              Cont provenance colorEndpoint endpoint ->
                PkgSig bundle endpoint pkg ->
                  UnaryHistory lookupLedger ∧ UnaryHistory provenance ∧
                    UnaryHistory endpoint ∧ hsame lookupLedger (append vertexSpine subsetSpine) ∧
                      hsame provenance (append lookupLedger colorEndpoint) ∧
                        hsame endpoint (append provenance colorEndpoint) ∧
                          PkgSig bundle endpoint pkg := by
  intro vertexUnary subsetUnary colorUnary lookupRow provenanceRow endpointRow pkgSig
  have lookupUnary : UnaryHistory lookupLedger :=
    unary_cont_closed vertexUnary subsetUnary lookupRow
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed lookupUnary colorUnary provenanceRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary colorUnary endpointRow
  exact
    ⟨lookupUnary,
      provenanceUnary,
      endpointUnary,
      lookupRow,
      provenanceRow,
      endpointRow,
      pkgSig⟩

theorem RamseyColouringCarrier_classifier_stability [AskSetup] [PackageSetup]
    {vertexSpine subsetSpine colourTable witnessRows transportRows lookupRoutes provenance
      endpoint vertexSpine' subsetSpine' colourTable' witnessRows' transportRows'
      lookupRoutes' provenance' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RamseyColouringCarrier vertexSpine subsetSpine colourTable witnessRows transportRows
        lookupRoutes provenance endpoint bundle pkg ->
      hsame vertexSpine vertexSpine' ->
        hsame subsetSpine subsetSpine' ->
          hsame colourTable colourTable' ->
            hsame transportRows transportRows' ->
              Cont vertexSpine' subsetSpine' lookupRoutes' ->
                Cont lookupRoutes' colourTable' witnessRows' ->
                  Cont witnessRows' transportRows' provenance' ->
                    Cont provenance' transportRows' endpoint' ->
                      PkgSig bundle endpoint' pkg ->
                        RamseyColouringCarrier vertexSpine' subsetSpine' colourTable'
                            witnessRows' transportRows' lookupRoutes' provenance' endpoint'
                            bundle pkg ∧
                          hsame lookupRoutes lookupRoutes' ∧ hsame witnessRows witnessRows' ∧
                            hsame provenance provenance' ∧ hsame endpoint endpoint' := by
  intro carrier sameVertex sameSubset sameColour sameTransport lookupCont witnessCont
    provenanceCont endpointCont endpointPkg
  have sameLookup : hsame lookupRoutes lookupRoutes' :=
    cont_respects_hsame sameVertex sameSubset
      carrier.right.right.right.right.right.right.left lookupCont
  have sameWitness : hsame witnessRows witnessRows' :=
    cont_respects_hsame sameLookup sameColour
      carrier.right.right.right.right.right.right.right.left witnessCont
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameWitness sameTransport
      carrier.right.right.right.right.right.right.right.right.left provenanceCont
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameTransport
      carrier.right.right.right.right.right.right.right.right.right.left endpointCont
  have transportedCarrier :
      RamseyColouringCarrier vertexSpine' subsetSpine' colourTable' witnessRows'
        transportRows' lookupRoutes' provenance' endpoint' bundle pkg :=
    ⟨unary_transport carrier.left sameVertex,
      unary_transport carrier.right.left sameSubset,
      unary_transport carrier.right.right.left sameColour,
      unary_transport carrier.right.right.right.left sameTransport,
      unary_transport carrier.right.right.right.right.left sameProvenance,
      unary_transport carrier.right.right.right.right.right.left sameEndpoint,
      lookupCont,
      witnessCont,
      provenanceCont,
      endpointCont,
      endpointPkg⟩
  exact And.intro transportedCarrier
    (And.intro sameLookup
      (And.intro sameWitness (And.intro sameProvenance sameEndpoint)))

theorem RamseyColouringCarrier_finite_ledger_exactness [AskSetup] [PackageSetup]
    {vertex subset colour witnessRows transportRows lookup provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RamseyColouringCarrier vertex subset colour witnessRows transportRows lookup provenance
        endpoint bundle pkg ->
      UnaryHistory vertex ∧ UnaryHistory subset ∧ UnaryHistory colour ∧
        UnaryHistory transportRows ∧ UnaryHistory lookup ∧ UnaryHistory witnessRows ∧
          UnaryHistory provenance ∧ UnaryHistory endpoint ∧
            hsame lookup (append vertex subset) ∧
              hsame witnessRows (append lookup colour) ∧
                hsame provenance (append witnessRows transportRows) ∧
                  hsame endpoint (append provenance transportRows) ∧
                    PkgSig bundle endpoint pkg := by
  intro carrier
  have lookupUnary : UnaryHistory lookup :=
    unary_cont_closed carrier.left carrier.right.left
      carrier.right.right.right.right.right.right.left
  have witnessUnary : UnaryHistory witnessRows :=
    unary_cont_closed lookupUnary carrier.right.right.left
      carrier.right.right.right.right.right.right.right.left
  exact
    ⟨carrier.left,
      carrier.right.left,
      carrier.right.right.left,
      carrier.right.right.right.left,
      lookupUnary,
      witnessUnary,
      carrier.right.right.right.right.left,
      carrier.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.right⟩

theorem RamseyColouringCarrier_downstream_boundary [AskSetup] [PackageSetup]
    {vertex subset colour lookup provenance endpoint graphProjection consumerEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RamseyColouringCarrier vertex subset colour endpoint BHist.Empty lookup provenance endpoint
        bundle pkg ->
      UnaryHistory graphProjection ->
        Cont endpoint graphProjection consumerEndpoint ->
          UnaryHistory vertex ∧ UnaryHistory subset ∧ UnaryHistory colour ∧
            UnaryHistory lookup ∧ UnaryHistory endpoint ∧ UnaryHistory consumerEndpoint ∧
              hsame lookup (append vertex subset) ∧ hsame endpoint (append lookup colour) ∧
                hsame consumerEndpoint (append endpoint graphProjection) ∧
                  PkgSig bundle endpoint pkg := by
  intro carrier graphProjectionUnary consumerRoute
  have finiteExact :=
    RamseyColouringCarrier_finite_ledger_exactness carrier
  have consumerUnary : UnaryHistory consumerEndpoint :=
    unary_cont_closed finiteExact.right.right.right.right.right.right.right.left
      graphProjectionUnary consumerRoute
  exact
    ⟨finiteExact.left,
      finiteExact.right.left,
      finiteExact.right.right.left,
      finiteExact.right.right.right.right.left,
      finiteExact.right.right.right.right.right.right.right.left,
      consumerUnary,
      finiteExact.right.right.right.right.right.right.right.right.left,
      finiteExact.right.right.right.right.right.right.right.right.right.left,
      consumerRoute,
      finiteExact.right.right.right.right.right.right.right.right.right.right.right.right⟩

theorem RamseyColouringCarrier_namecert_obligation_assembly [AskSetup] [PackageSetup]
    {vertex subset colour witnessRows transportRows lookup provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RamseyColouringCarrier vertex subset colour witnessRows transportRows lookup provenance
        endpoint bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            RamseyColouringCarrier vertex subset colour witnessRows transportRows lookup provenance
              endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            RamseyColouringCarrier vertex subset colour witnessRows transportRows lookup provenance
              endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            RamseyColouringCarrier vertex subset colour witnessRows transportRows lookup provenance
              endpoint bundle pkg ∧ hsame row endpoint)
          hsame ∧
        UnaryHistory lookup ∧ UnaryHistory witnessRows ∧ UnaryHistory endpoint ∧
          PkgSig bundle endpoint pkg := by
  intro carrier
  have lookupUnary : UnaryHistory lookup :=
    unary_cont_closed carrier.left carrier.right.left
      carrier.right.right.right.right.right.right.left
  have witnessUnary : UnaryHistory witnessRows :=
    unary_cont_closed lookupUnary carrier.right.right.left
      carrier.right.right.right.right.right.right.right.left
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            RamseyColouringCarrier vertex subset colour witnessRows transportRows lookup provenance
              endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            RamseyColouringCarrier vertex subset colour witnessRows transportRows lookup provenance
              endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            RamseyColouringCarrier vertex subset colour witnessRows transportRows lookup provenance
              endpoint bundle pkg ∧ hsame row endpoint)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint (And.intro carrier (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert
    (And.intro lookupUnary
      (And.intro witnessUnary
        (And.intro carrier.right.right.right.right.right.left
          carrier.right.right.right.right.right.right.right.right.right.right)))

theorem RamseyColouringCarrier_public_projection_package [AskSetup] [PackageSetup]
    {vertex subset colour witnessRows transportRows lookup provenance endpoint graphProjection
      consumerEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RamseyColouringCarrier vertex subset colour witnessRows transportRows lookup provenance
        endpoint bundle pkg ->
      UnaryHistory graphProjection ->
        Cont endpoint graphProjection consumerEndpoint ->
          RamseyColouringCarrier vertex subset colour witnessRows transportRows lookup provenance
              endpoint bundle pkg ∧
            UnaryHistory vertex ∧ UnaryHistory subset ∧ UnaryHistory colour ∧
              UnaryHistory lookup ∧ UnaryHistory witnessRows ∧ UnaryHistory provenance ∧
                UnaryHistory endpoint ∧ UnaryHistory consumerEndpoint ∧
                  hsame lookup (append vertex subset) ∧
                    hsame witnessRows (append lookup colour) ∧
                      hsame provenance (append witnessRows transportRows) ∧
                        hsame endpoint (append provenance transportRows) ∧
                          hsame consumerEndpoint (append endpoint graphProjection) ∧
                            PkgSig bundle endpoint pkg := by
  intro carrier graphProjectionUnary consumerRoute
  have finiteExact :=
    RamseyColouringCarrier_finite_ledger_exactness carrier
  have consumerUnary : UnaryHistory consumerEndpoint :=
    unary_cont_closed finiteExact.right.right.right.right.right.right.right.left
      graphProjectionUnary consumerRoute
  exact
    ⟨carrier,
      finiteExact.left,
      finiteExact.right.left,
      finiteExact.right.right.left,
      finiteExact.right.right.right.right.left,
      finiteExact.right.right.right.right.right.left,
      finiteExact.right.right.right.right.right.right.left,
      finiteExact.right.right.right.right.right.right.right.left,
      consumerUnary,
      finiteExact.right.right.right.right.right.right.right.right.left,
      finiteExact.right.right.right.right.right.right.right.right.right.left,
      finiteExact.right.right.right.right.right.right.right.right.right.right.left,
      finiteExact.right.right.right.right.right.right.right.right.right.right.right.left,
      consumerRoute,
      finiteExact.right.right.right.right.right.right.right.right.right.right.right.right⟩

end BEDC.Derived.RamseyUp
