import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SpectralMeasureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SpectralMeasurePacket [AskSetup] [PackageSetup]
    (hilbert observable event projection orthogonality finiteAdd route provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory hilbert ∧ UnaryHistory observable ∧ UnaryHistory event ∧
    UnaryHistory projection ∧ UnaryHistory orthogonality ∧ UnaryHistory finiteAdd ∧
      Cont event projection route ∧ Cont orthogonality finiteAdd endpoint ∧
        Cont provenance route endpoint ∧ PkgSig bundle endpoint pkg

theorem SpectralMeasurePacket_hsame_stability [AskSetup] [PackageSetup]
    {hilbert observable event projection orthogonality finiteAdd route provenance endpoint
      hilbert' observable' event' projection' orthogonality' finiteAdd' route' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpectralMeasurePacket hilbert observable event projection orthogonality finiteAdd route
        provenance endpoint bundle pkg ->
      hsame hilbert hilbert' -> hsame observable observable' -> hsame event event' ->
        hsame projection projection' -> hsame orthogonality orthogonality' ->
          hsame finiteAdd finiteAdd' -> Cont event' projection' route' ->
            Cont orthogonality' finiteAdd' endpoint' -> Cont provenance route' endpoint' ->
              PkgSig bundle endpoint' pkg ->
                SpectralMeasurePacket hilbert' observable' event' projection' orthogonality'
                    finiteAdd' route' provenance endpoint' bundle pkg ∧
                  hsame route route' ∧ hsame endpoint endpoint' := by
  intro packet sameHilbert sameObservable sameEvent sameProjection sameOrthogonality
    sameFiniteAdd routeCont' endpointCont' provenanceCont' pkgSig'
  have hilbertUnary' : UnaryHistory hilbert' :=
    unary_transport packet.left sameHilbert
  have observableUnary' : UnaryHistory observable' :=
    unary_transport packet.right.left sameObservable
  have eventUnary' : UnaryHistory event' :=
    unary_transport packet.right.right.left sameEvent
  have projectionUnary' : UnaryHistory projection' :=
    unary_transport packet.right.right.right.left sameProjection
  have orthogonalityUnary' : UnaryHistory orthogonality' :=
    unary_transport packet.right.right.right.right.left sameOrthogonality
  have finiteAddUnary' : UnaryHistory finiteAdd' :=
    unary_transport packet.right.right.right.right.right.left sameFiniteAdd
  have sameRoute : hsame route route' :=
    cont_respects_hsame sameEvent sameProjection
      packet.right.right.right.right.right.right.left routeCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameOrthogonality sameFiniteAdd
      packet.right.right.right.right.right.right.right.left endpointCont'
  exact
    ⟨⟨hilbertUnary', observableUnary', eventUnary', projectionUnary', orthogonalityUnary',
        finiteAddUnary', routeCont', endpointCont', provenanceCont', pkgSig'⟩,
      sameRoute, sameEndpoint⟩

def SpectralMeasureCarrier [AskSetup] [PackageSetup]
    (hilbert observable event projection orthogonality additivity route provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory hilbert ∧ UnaryHistory observable ∧ UnaryHistory event ∧
    UnaryHistory projection ∧ UnaryHistory orthogonality ∧ UnaryHistory additivity ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ Cont hilbert observable projection ∧
        Cont event projection route ∧ Cont orthogonality additivity provenance ∧
          PkgSig bundle provenance pkg

theorem SpectralMeasureCarrier_hsame_stability [AskSetup] [PackageSetup]
    {hilbert observable event projection orthogonality additivity route provenance hilbert'
      observable' event' projection' orthogonality' additivity' route' provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpectralMeasureCarrier hilbert observable event projection orthogonality additivity route
        provenance bundle pkg ->
      hsame hilbert hilbert' ->
        hsame observable observable' ->
          hsame event event' ->
            hsame orthogonality orthogonality' ->
              hsame additivity additivity' ->
                Cont hilbert' observable' projection' ->
                  Cont event' projection' route' ->
                    Cont orthogonality' additivity' provenance' ->
                      PkgSig bundle provenance' pkg ->
                        SpectralMeasureCarrier hilbert' observable' event' projection'
                            orthogonality' additivity' route' provenance' bundle pkg ∧
                          hsame projection projection' ∧ hsame route route' ∧
                            hsame provenance provenance' := by
  intro carrier sameHilbert sameObservable sameEvent sameOrthogonality sameAdditivity
    projectionRow' routeRow' provenanceRow' pkg'
  have hilbertUnary' : UnaryHistory hilbert' :=
    unary_transport carrier.left sameHilbert
  have observableUnary' : UnaryHistory observable' :=
    unary_transport carrier.right.left sameObservable
  have eventUnary' : UnaryHistory event' :=
    unary_transport carrier.right.right.left sameEvent
  have orthogonalityUnary' : UnaryHistory orthogonality' :=
    unary_transport carrier.right.right.right.right.left sameOrthogonality
  have additivityUnary' : UnaryHistory additivity' :=
    unary_transport carrier.right.right.right.right.right.left sameAdditivity
  have sameProjection : hsame projection projection' :=
    cont_respects_hsame sameHilbert sameObservable
      carrier.right.right.right.right.right.right.right.right.left projectionRow'
  have projectionUnary' : UnaryHistory projection' :=
    unary_cont_closed hilbertUnary' observableUnary' projectionRow'
  have sameRoute : hsame route route' :=
    cont_respects_hsame sameEvent sameProjection
      carrier.right.right.right.right.right.right.right.right.right.left routeRow'
  have routeUnary' : UnaryHistory route' :=
    unary_cont_closed eventUnary' projectionUnary' routeRow'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameOrthogonality sameAdditivity
      carrier.right.right.right.right.right.right.right.right.right.right.left
      provenanceRow'
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed orthogonalityUnary' additivityUnary' provenanceRow'
  exact
    And.intro
      (And.intro hilbertUnary'
        (And.intro observableUnary'
          (And.intro eventUnary'
            (And.intro projectionUnary'
              (And.intro orthogonalityUnary'
                (And.intro additivityUnary'
                  (And.intro routeUnary'
                    (And.intro provenanceUnary'
                      (And.intro projectionRow'
                        (And.intro routeRow'
                          (And.intro provenanceRow' pkg')))))))))))
      (And.intro sameProjection (And.intro sameRoute sameProvenance))

def SpectralMeasureFiniteAdditivityLedger [AskSetup] [PackageSetup]
    (event projection other union orthogonality additivity : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory event ∧ UnaryHistory projection ∧ UnaryHistory other ∧
    UnaryHistory orthogonality ∧ Cont projection other union ∧
      Cont union orthogonality additivity ∧ PkgSig bundle additivity pkg

theorem SpectralMeasureOrthogonalFiniteAdditivity_row [AskSetup] [PackageSetup]
    {event projection other union orthogonality additivity event' projection' other' union'
      orthogonality' additivity' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpectralMeasureFiniteAdditivityLedger event projection other union orthogonality additivity
        bundle pkg ->
      hsame event event' -> hsame projection projection' -> hsame other other' ->
        hsame orthogonality orthogonality' -> Cont projection' other' union' ->
          Cont union' orthogonality' additivity' -> PkgSig bundle additivity' pkg ->
            SpectralMeasureFiniteAdditivityLedger event' projection' other' union'
                orthogonality' additivity' bundle pkg ∧
              hsame union union' ∧ hsame additivity additivity' := by
  intro ledger sameEvent sameProjection sameOther sameOrthogonality unionRow' additivityRow'
    pkgSig'
  have eventUnary' : UnaryHistory event' :=
    unary_transport ledger.left sameEvent
  have projectionUnary' : UnaryHistory projection' :=
    unary_transport ledger.right.left sameProjection
  have otherUnary' : UnaryHistory other' :=
    unary_transport ledger.right.right.left sameOther
  have orthogonalityUnary' : UnaryHistory orthogonality' :=
    unary_transport ledger.right.right.right.left sameOrthogonality
  have sameUnion : hsame union union' :=
    cont_respects_hsame sameProjection sameOther ledger.right.right.right.right.left unionRow'
  have unionUnary' : UnaryHistory union' :=
    unary_cont_closed projectionUnary' otherUnary' unionRow'
  have sameAdditivity : hsame additivity additivity' :=
    cont_respects_hsame sameUnion sameOrthogonality ledger.right.right.right.right.right.left
      additivityRow'
  exact
    And.intro
      (And.intro eventUnary'
        (And.intro projectionUnary'
          (And.intro otherUnary'
            (And.intro orthogonalityUnary'
              (And.intro unionRow'
                (And.intro additivityRow' pkgSig'))))))
      (And.intro sameUnion sameAdditivity)

def SpectralMeasureFinitePacket [AskSetup] [PackageSetup]
    (hilbert observable event projection orthogonality additivity transport provenance
      endpoint : BHist)
    (probe : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory hilbert ∧ UnaryHistory observable ∧ UnaryHistory event ∧
    UnaryHistory projection ∧ UnaryHistory orthogonality ∧ UnaryHistory additivity ∧
      UnaryHistory transport ∧ UnaryHistory provenance ∧ UnaryHistory endpoint ∧
        Cont observable event projection ∧ Cont projection orthogonality additivity ∧
          Cont additivity transport endpoint ∧ PkgSig probe provenance pkg

theorem SpectralMeasureFinitePacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {hilbert observable event projection orthogonality additivity transport provenance
      endpoint : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    SpectralMeasureFinitePacket hilbert observable event projection orthogonality additivity
        transport provenance endpoint probe pkg ->
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              SpectralMeasureFinitePacket hilbert observable event projection orthogonality
                additivity transport provenance e probe pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              SpectralMeasureFinitePacket hilbert observable event projection orthogonality
                additivity transport provenance e probe pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              SpectralMeasureFinitePacket hilbert observable event projection orthogonality
                additivity transport provenance e probe pkg ∧ hsame row e)
          hsame ∧
        Cont observable event projection ∧ Cont projection orthogonality additivity ∧
          Cont additivity transport endpoint ∧ PkgSig probe provenance pkg := by
  intro packet
  have endpointSource :
      (fun row : BHist =>
        exists e : BHist,
          SpectralMeasureFinitePacket hilbert observable event projection orthogonality
            additivity transport provenance e probe pkg ∧ hsame row e) endpoint :=
    Exists.intro endpoint (And.intro packet (hsame_refl endpoint))
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              SpectralMeasureFinitePacket hilbert observable event projection orthogonality
                additivity transport provenance e probe pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              SpectralMeasureFinitePacket hilbert observable event projection orthogonality
                additivity transport provenance e probe pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              SpectralMeasureFinitePacket hilbert observable event projection orthogonality
                additivity transport provenance e probe pkg ∧ hsame row e)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint endpointSource
      equiv_refl := by
        intro row _carrier
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' sameRows carrierRow
        cases carrierRow with
        | intro e endpointWitness =>
            exact Exists.intro e
              (And.intro endpointWitness.left
                (hsame_trans (hsame_symm sameRows) endpointWitness.right))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert
    (And.intro packet.right.right.right.right.right.right.right.right.right.left
      (And.intro packet.right.right.right.right.right.right.right.right.right.right.left
        (And.intro packet.right.right.right.right.right.right.right.right.right.right.right.left
          packet.right.right.right.right.right.right.right.right.right.right.right.right)))

theorem SpectralMeasureFinitePacket_projection_ledger_transport [AskSetup] [PackageSetup]
    {hilbert observable event projection orthogonality additivity transport provenance endpoint
      hilbert' observable' event' projection' orthogonality' additivity' transport'
      endpoint' : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    SpectralMeasureFinitePacket hilbert observable event projection orthogonality additivity
        transport provenance endpoint probe pkg ->
      hsame hilbert hilbert' ->
        hsame observable observable' ->
          hsame event event' ->
            hsame orthogonality orthogonality' ->
              hsame transport transport' ->
                Cont observable' event' projection' ->
                  Cont projection' orthogonality' additivity' ->
                    Cont additivity' transport' endpoint' ->
                      PkgSig probe provenance pkg ->
                        SpectralMeasureFinitePacket hilbert' observable' event' projection'
                            orthogonality' additivity' transport' provenance endpoint' probe
                            pkg ∧
                          hsame projection projection' ∧ hsame additivity additivity' ∧
                            hsame endpoint endpoint' := by
  intro packet sameHilbert sameObservable sameEvent sameOrthogonality sameTransport
    projectionRow' additivityRow' endpointRow' pkgSig'
  have hilbertUnary' : UnaryHistory hilbert' :=
    unary_transport packet.left sameHilbert
  have observableUnary' : UnaryHistory observable' :=
    unary_transport packet.right.left sameObservable
  have eventUnary' : UnaryHistory event' :=
    unary_transport packet.right.right.left sameEvent
  have orthogonalityUnary' : UnaryHistory orthogonality' :=
    unary_transport packet.right.right.right.right.left sameOrthogonality
  have transportUnary' : UnaryHistory transport' :=
    unary_transport packet.right.right.right.right.right.right.left sameTransport
  have provenanceUnary : UnaryHistory provenance :=
    packet.right.right.right.right.right.right.right.left
  have sameProjection : hsame projection projection' :=
    cont_respects_hsame sameObservable sameEvent
      packet.right.right.right.right.right.right.right.right.right.left projectionRow'
  have projectionUnary' : UnaryHistory projection' :=
    unary_cont_closed observableUnary' eventUnary' projectionRow'
  have sameAdditivity : hsame additivity additivity' :=
    cont_respects_hsame sameProjection sameOrthogonality
      packet.right.right.right.right.right.right.right.right.right.right.left additivityRow'
  have additivityUnary' : UnaryHistory additivity' :=
    unary_cont_closed projectionUnary' orthogonalityUnary' additivityRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameAdditivity sameTransport
      packet.right.right.right.right.right.right.right.right.right.right.right.left
      endpointRow'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed additivityUnary' transportUnary' endpointRow'
  exact
    ⟨⟨hilbertUnary', observableUnary', eventUnary', projectionUnary', orthogonalityUnary',
        additivityUnary', transportUnary', provenanceUnary, endpointUnary', projectionRow',
        additivityRow', endpointRow', pkgSig'⟩,
      sameProjection, sameAdditivity, sameEndpoint⟩

end BEDC.Derived.SpectralMeasureUp
