import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.CriticalStripZetaZeroWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CriticalStripZetaZeroWitnessPacket [AskSetup] [PackageSetup]
    (strip zero line boundary transport route provenance name endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory strip ∧ UnaryHistory zero ∧ UnaryHistory line ∧ UnaryHistory boundary ∧
    UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
      UnaryHistory name ∧ UnaryHistory endpoint ∧ Cont strip zero transport ∧
        Cont line boundary route ∧ Cont transport route endpoint ∧
          Cont endpoint provenance name ∧ hsame endpoint (append transport route) ∧
            PkgSig bundle endpoint pkg

theorem CriticalStripZetaZeroWitnessPacket_namecert_obligations [AskSetup] [PackageSetup]
    {strip zero line boundary transport route provenance name endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CriticalStripZetaZeroWitnessPacket strip zero line boundary transport route provenance name
        endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CriticalStripZetaZeroWitnessPacket strip zero line boundary transport route provenance
              name endpoint bundle pkg ∧
            hsame row endpoint)
        (fun row : BHist =>
          CriticalStripZetaZeroWitnessPacket strip zero line boundary transport route provenance
              name endpoint bundle pkg ∧
            hsame row endpoint)
        (fun row : BHist =>
          CriticalStripZetaZeroWitnessPacket strip zero line boundary transport route provenance
              name endpoint bundle pkg ∧
            hsame row endpoint)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint (And.intro packet (hsame_refl endpoint))
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
        intro _row _row' sameRows sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm sameRows) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }

def CriticalStripZetaZeroWitnessCarrier [AskSetup] [PackageSetup]
    (strip zero line boundary transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory strip ∧ UnaryHistory zero ∧ UnaryHistory line ∧ UnaryHistory boundary ∧
    UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
      Cont strip route provenance ∧ Cont zero route provenance ∧ PkgSig bundle provenance pkg

theorem CriticalStripZetaZeroWitnessCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {strip zero line boundary transport route provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CriticalStripZetaZeroWitnessCarrier strip zero line boundary transport route provenance name
        bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CriticalStripZetaZeroWitnessCarrier strip zero line boundary transport route provenance
            name bundle pkg ∧ hsame row provenance)
        (fun row : BHist =>
          Cont strip route row ∧ Cont zero route row ∧ PkgSig bundle row pkg)
        (fun _row : BHist =>
          UnaryHistory strip ∧ UnaryHistory zero ∧ UnaryHistory line ∧
            UnaryHistory boundary ∧ UnaryHistory transport ∧ UnaryHistory route ∧
              UnaryHistory provenance ∧ UnaryHistory name)
        hsame := by
  intro carrier
  have stripUnary : UnaryHistory strip := carrier.left
  have zeroUnary : UnaryHistory zero := carrier.right.left
  have lineUnary : UnaryHistory line := carrier.right.right.left
  have boundaryUnary : UnaryHistory boundary := carrier.right.right.right.left
  have transportUnary : UnaryHistory transport := carrier.right.right.right.right.left
  have routeUnary : UnaryHistory route := carrier.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance := carrier.right.right.right.right.right.right.left
  have nameUnary : UnaryHistory name := carrier.right.right.right.right.right.right.right.left
  have stripRoute : Cont strip route provenance :=
    carrier.right.right.right.right.right.right.right.right.left
  have zeroRoute : Cont zero route provenance :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have provenancePkg : PkgSig bundle provenance pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro provenance (And.intro carrier (hsame_refl provenance))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _left _right same
        exact hsame_symm same
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _left _right same source
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    }
    pattern_sound := by
      intro row source
      have same : hsame row provenance := source.right
      cases same
      exact And.intro stripRoute (And.intro zeroRoute provenancePkg)
    ledger_sound := by
      intro _row _source
      exact
        And.intro stripUnary
          (And.intro zeroUnary
            (And.intro lineUnary
              (And.intro boundaryUnary
                (And.intro transportUnary
                  (And.intro routeUnary
                    (And.intro provenanceUnary nameUnary))))))
  }

theorem CriticalStripZetaZeroWitnessPacket_package_sameness [AskSetup] [PackageSetup]
    {strip zero line boundary transport route provenance name endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg pkg' : Pkg} :
    CriticalStripZetaZeroWitnessPacket strip zero line boundary transport route provenance name
        endpoint bundle pkg ->
      CriticalStripZetaZeroWitnessPacket strip zero line boundary transport route provenance name
        endpoint bundle pkg' ->
      psame bundle pkg pkg' := by
  intro leftPacket rightPacket
  have leftPkg : PkgSig bundle endpoint pkg :=
    leftPacket.right.right.right.right.right.right.right.right.right.right.right.right.right.right
  have rightPkg : PkgSig bundle endpoint pkg' :=
    rightPacket.right.right.right.right.right.right.right.right.right.right.right.right.right.right
  exact PkgSig_psame_intro leftPkg rightPkg (hsame_refl endpoint)

theorem CriticalStripZetaZeroWitnessPacket_critical_line_boundary [AskSetup] [PackageSetup]
    {strip zero line boundary transport route provenance name endpoint lineRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CriticalStripZetaZeroWitnessPacket strip zero line boundary transport route provenance name
        endpoint bundle pkg ->
      Cont line boundary lineRead ->
        PkgSig bundle lineRead pkg ->
          UnaryHistory line ∧ UnaryHistory boundary ∧ UnaryHistory lineRead ∧
            Cont line boundary route ∧ Cont line boundary lineRead ∧
              PkgSig bundle endpoint pkg ∧ PkgSig bundle lineRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet lineBoundaryRead lineReadPkg
  obtain ⟨_stripUnary, _zeroUnary, lineUnary, boundaryUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, _endpointUnary, _stripZeroTransport,
    lineBoundaryRoute, _transportRouteEndpoint, _endpointProvenanceName,
    _endpointSameTransportRoute, endpointPkg⟩ := packet
  have lineReadUnary : UnaryHistory lineRead :=
    unary_cont_closed lineUnary boundaryUnary lineBoundaryRead
  exact
    ⟨lineUnary, boundaryUnary, lineReadUnary, lineBoundaryRoute, lineBoundaryRead,
      endpointPkg, lineReadPkg⟩

theorem CriticalStripZetaZeroWitnessPacket_concretizes_rh [AskSetup] [PackageSetup]
    {strip zero line boundary transport route provenance name endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CriticalStripZetaZeroWitnessPacket strip zero line boundary transport route provenance name
        endpoint bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            CriticalStripZetaZeroWitnessPacket strip zero line boundary transport route provenance
                name endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            Cont strip zero transport ∧ Cont line boundary route ∧ hsame row endpoint)
          (fun row : BHist =>
            PkgSig bundle endpoint pkg ∧ hsame endpoint (append transport route) ∧
              hsame row endpoint)
          hsame ∧
        Cont strip zero transport ∧ Cont line boundary route ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet
  have packetSource := packet
  obtain ⟨_stripUnary, _zeroUnary, _lineUnary, _boundaryUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, _endpointUnary, stripZeroTransport,
    lineBoundaryRoute, _transportRouteEndpoint, _endpointProvenanceName,
    endpointSameTransportRoute, endpointPkg⟩ := packet
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro endpoint (And.intro packetSource (hsame_refl endpoint))
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
          intro _row _row' sameRows sourceRow
          exact And.intro sourceRow.left (hsame_trans (hsame_symm sameRows) sourceRow.right)
      }
      pattern_sound := by
        intro row sourceRow
        exact And.intro stripZeroTransport (And.intro lineBoundaryRoute sourceRow.right)
      ledger_sound := by
        intro row sourceRow
        exact
          And.intro endpointPkg
            (And.intro endpointSameTransportRoute sourceRow.right)
    }
  · exact And.intro stripZeroTransport (And.intro lineBoundaryRoute endpointPkg)

theorem CriticalStripZetaZeroWitnessPacket_source_route_exhaustion [AskSetup] [PackageSetup]
    {strip zero line boundary transport route provenance name endpoint sourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CriticalStripZetaZeroWitnessPacket strip zero line boundary transport route provenance name
        endpoint bundle pkg ->
      Cont sourceRead route endpoint ->
        hsame sourceRead transport ∧ UnaryHistory sourceRead ∧ Cont strip zero sourceRead ∧
          PkgSig bundle endpoint pkg := by
  intro packet sourceRouteEndpoint
  obtain ⟨_stripUnary, _zeroUnary, _lineUnary, _boundaryUnary, transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, _endpointUnary, stripZeroTransport, _lineBoundaryRoute,
    transportRouteEndpoint, _endpointProvenanceName, _endpointSameTransportRoute,
    endpointPkg⟩ := packet
  have sameSourceTransport : hsame sourceRead transport :=
    cont_right_cancel sourceRouteEndpoint transportRouteEndpoint
  have sourceUnary : UnaryHistory sourceRead :=
    unary_transport transportUnary (hsame_symm sameSourceTransport)
  have stripZeroSource : Cont strip zero sourceRead :=
    cont_result_hsame_transport stripZeroTransport (hsame_symm sameSourceTransport)
  exact ⟨sameSourceTransport, sourceUnary, stripZeroSource, endpointPkg⟩

theorem CriticalStripZetaZeroWitnessPacket_rh_premise_exhaustion [AskSetup] [PackageSetup]
    {strip zero line boundary transport route provenance name endpoint premiseRead lineRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CriticalStripZetaZeroWitnessPacket strip zero line boundary transport route provenance name
        endpoint bundle pkg ->
      Cont strip zero premiseRead ->
        Cont line boundary lineRead ->
          PkgSig bundle premiseRead pkg ->
            PkgSig bundle lineRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
                  (fun row : BHist => hsame row endpoint)
                  (fun row : BHist => PkgSig bundle endpoint pkg ∧ hsame row endpoint)
                  hsame ∧
                UnaryHistory premiseRead ∧ UnaryHistory lineRead ∧ hsame premiseRead transport ∧
                  hsame lineRead route ∧ Cont strip zero transport ∧ Cont line boundary route ∧
                    PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet premiseRoute lineRoute _premisePkg _linePkg
  obtain ⟨stripUnary, zeroUnary, lineUnary, boundaryUnary, transportUnary, routeUnary,
    _provenanceUnary, _nameUnary, _endpointUnary, stripZeroTransport, lineBoundaryRoute,
    _transportRouteEndpoint, _endpointProvenanceName, _endpointSameTransportRoute,
    endpointPkg⟩ := packet
  have premiseReadUnary : UnaryHistory premiseRead :=
    unary_cont_closed stripUnary zeroUnary premiseRoute
  have lineReadUnary : UnaryHistory lineRead :=
    unary_cont_closed lineUnary boundaryUnary lineRoute
  have premiseSameTransport : hsame premiseRead transport :=
    cont_deterministic premiseRoute stripZeroTransport
  have lineReadSameRoute : hsame lineRead route :=
    cont_deterministic lineRoute lineBoundaryRoute
  have endpointSource : hsame endpoint endpoint ∧ PkgSig bundle endpoint pkg :=
    And.intro (hsame_refl endpoint) endpointPkg
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
          (fun row : BHist => hsame row endpoint)
          (fun row : BHist => PkgSig bundle endpoint pkg ∧ hsame row endpoint)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint endpointSource
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
        intro _row _row' sameRows sourceRow
        exact And.intro (hsame_trans (hsame_symm sameRows) sourceRow.left) sourceRow.right
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow.left
    ledger_sound := by
      intro _row sourceRow
      exact And.intro sourceRow.right sourceRow.left
  }
  exact
    ⟨cert, premiseReadUnary, lineReadUnary, premiseSameTransport, lineReadSameRoute,
      stripZeroTransport, lineBoundaryRoute, endpointPkg⟩

end BEDC.Derived.CriticalStripZetaZeroWitnessUp
