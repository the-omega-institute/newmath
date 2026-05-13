import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicCoverPacket [AskSetup] [PackageSetup]
    (centers radii intervals mesh window transport routes provenance nameCert endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory centers ∧ UnaryHistory radii ∧ UnaryHistory intervals ∧
    UnaryHistory mesh ∧ UnaryHistory window ∧ UnaryHistory transport ∧
      UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory nameCert ∧
        UnaryHistory endpoint ∧ Cont centers radii intervals ∧ Cont intervals mesh window ∧
          Cont window routes endpoint ∧ hsame nameCert endpoint ∧ PkgSig bundle endpoint pkg

theorem DyadicCoverPacket_namecert_obligations [AskSetup] [PackageSetup]
    {centers radii intervals mesh window transport routes provenance nameCert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicCoverPacket centers radii intervals mesh window transport routes provenance nameCert
        endpoint bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row endpoint ∧
              DyadicCoverPacket centers radii intervals mesh window transport routes provenance
                nameCert endpoint bundle pkg)
          (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
          hsame ∧
        UnaryHistory centers ∧ UnaryHistory radii ∧ UnaryHistory intervals ∧
          UnaryHistory mesh ∧ UnaryHistory window ∧ Cont centers radii intervals ∧
            Cont intervals mesh window ∧ Cont window routes endpoint ∧
              PkgSig bundle endpoint pkg := by
  intro packet
  have centerUnary : UnaryHistory centers :=
    packet.left
  have radiiUnary : UnaryHistory radii :=
    packet.right.left
  have intervalsUnary : UnaryHistory intervals :=
    packet.right.right.left
  have meshUnary : UnaryHistory mesh :=
    packet.right.right.right.left
  have windowUnary : UnaryHistory window :=
    packet.right.right.right.right.left
  have centersRadiiIntervals : Cont centers radii intervals :=
    packet.right.right.right.right.right.right.right.right.right.right.left
  have intervalsMeshWindow : Cont intervals mesh window :=
    packet.right.right.right.right.right.right.right.right.right.right.right.left
  have windowRoutesEndpoint : Cont window routes endpoint :=
    packet.right.right.right.right.right.right.right.right.right.right.right.right.left
  have endpointPkg : PkgSig bundle endpoint pkg :=
    packet.right.right.right.right.right.right.right.right.right.right.right.right.right.right
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row endpoint ∧
            DyadicCoverPacket centers radii intervals mesh window transport routes provenance
              nameCert endpoint bundle pkg)
        (fun row : BHist => hsame row endpoint)
        (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
        hsame := by
    constructor
    · constructor
      · exact Exists.intro endpoint (And.intro (hsame_refl endpoint) packet)
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact And.intro (hsame_trans (hsame_symm same) source.left) source.right
    · intro row source
      exact source.left
    · intro row source
      exact And.intro source.left endpointPkg
  exact
    ⟨cert, centerUnary, radiiUnary, intervalsUnary, meshUnary, windowUnary,
      centersRadiiIntervals, intervalsMeshWindow, windowRoutesEndpoint, endpointPkg⟩

theorem DyadicCoverPacket_finite_refinement_transport [AskSetup] [PackageSetup]
    {centers radii intervals mesh window transport routes provenance nameCert endpoint
      refinedMesh refinedWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicCoverPacket centers radii intervals mesh window transport routes provenance nameCert
        endpoint bundle pkg →
      hsame mesh refinedMesh →
        hsame window refinedWindow →
          Cont intervals refinedMesh refinedWindow →
            Cont refinedWindow routes endpoint →
              DyadicCoverPacket centers radii intervals refinedMesh refinedWindow transport routes
                provenance nameCert endpoint bundle pkg := by
  intro packet meshSame windowSame intervalsRefined refinedRoutes
  have centerUnary : UnaryHistory centers :=
    packet.left
  have radiiUnary : UnaryHistory radii :=
    packet.right.left
  have intervalsUnary : UnaryHistory intervals :=
    packet.right.right.left
  have meshUnary : UnaryHistory mesh :=
    packet.right.right.right.left
  have windowUnary : UnaryHistory window :=
    packet.right.right.right.right.left
  have transportUnary : UnaryHistory transport :=
    packet.right.right.right.right.right.left
  have routesUnary : UnaryHistory routes :=
    packet.right.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    packet.right.right.right.right.right.right.right.left
  have nameCertUnary : UnaryHistory nameCert :=
    packet.right.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    packet.right.right.right.right.right.right.right.right.right.left
  have centersRadiiIntervals : Cont centers radii intervals :=
    packet.right.right.right.right.right.right.right.right.right.right.left
  have nameCertEndpoint : hsame nameCert endpoint :=
    packet.right.right.right.right.right.right.right.right.right.right.right.right.right.left
  have endpointPkg : PkgSig bundle endpoint pkg :=
    packet.right.right.right.right.right.right.right.right.right.right.right.right.right.right
  have refinedMeshUnary : UnaryHistory refinedMesh :=
    unary_transport meshUnary meshSame
  have refinedWindowUnary : UnaryHistory refinedWindow :=
    unary_transport windowUnary windowSame
  exact
    ⟨centerUnary, radiiUnary, intervalsUnary, refinedMeshUnary, refinedWindowUnary,
      transportUnary, routesUnary, provenanceUnary, nameCertUnary, endpointUnary,
      centersRadiiIntervals, intervalsRefined, refinedRoutes, nameCertEndpoint, endpointPkg⟩

theorem DyadicCoverPacket_finite_refinement [AskSetup] [PackageSetup]
    {centers radii intervals mesh window transport routes provenance nameCert endpoint centers'
      radii' intervals' refinedMesh refinedWindow transport' routes' provenance' nameCert'
      refinedEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicCoverPacket centers radii intervals mesh window transport routes provenance nameCert
        endpoint bundle pkg ->
      hsame centers centers' -> hsame radii radii' -> hsame intervals intervals' ->
        hsame transport transport' -> hsame routes routes' -> hsame provenance provenance' ->
          hsame nameCert nameCert' -> hsame endpoint refinedEndpoint ->
            Cont intervals' refinedMesh refinedWindow ->
              Cont refinedWindow routes' refinedEndpoint ->
                PkgSig bundle refinedEndpoint pkg ->
                  DyadicCoverPacket centers' radii' intervals' refinedMesh refinedWindow
                      transport' routes' provenance' nameCert' refinedEndpoint bundle pkg ∧
                    hsame endpoint refinedEndpoint := by
  intro packet sameCenters sameRadii sameIntervals sameTransport sameRoutes sameProvenance
    sameNameCert sameEndpoint refinedWindowRow refinedEndpointRow refinedPkg
  have centersUnary' : UnaryHistory centers' :=
    unary_transport packet.left sameCenters
  have radiiUnary' : UnaryHistory radii' :=
    unary_transport packet.right.left sameRadii
  have intervalsUnary' : UnaryHistory intervals' :=
    unary_transport packet.right.right.left sameIntervals
  have transportUnary' : UnaryHistory transport' :=
    unary_transport packet.right.right.right.right.right.left sameTransport
  have routesUnary' : UnaryHistory routes' :=
    unary_transport packet.right.right.right.right.right.right.left sameRoutes
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport packet.right.right.right.right.right.right.right.left sameProvenance
  have nameCertUnary' : UnaryHistory nameCert' :=
    unary_transport packet.right.right.right.right.right.right.right.right.left sameNameCert
  have refinedEndpointUnary : UnaryHistory refinedEndpoint :=
    unary_transport packet.right.right.right.right.right.right.right.right.right.left sameEndpoint
  have refinedWindowUnary : UnaryHistory refinedWindow :=
    unary_cont_left_factor refinedEndpointRow refinedEndpointUnary
  have refinedMeshUnary : UnaryHistory refinedMesh :=
    unary_cont_right_factor refinedWindowRow refinedWindowUnary
  have centersRadiiIntervals' : Cont centers' radii' intervals' := by
    cases sameCenters
    cases sameRadii
    cases sameIntervals
    exact packet.right.right.right.right.right.right.right.right.right.right.left
  have nameCertEndpoint : hsame nameCert' refinedEndpoint :=
    hsame_trans (hsame_symm sameNameCert)
      (hsame_trans packet.right.right.right.right.right.right.right.right.right.right.right.right.right.left
        sameEndpoint)
  exact
    ⟨⟨centersUnary',
      radiiUnary',
      intervalsUnary',
      refinedMeshUnary,
      refinedWindowUnary,
      transportUnary',
      routesUnary',
      provenanceUnary',
      nameCertUnary',
      refinedEndpointUnary,
      centersRadiiIntervals',
      refinedWindowRow,
      refinedEndpointRow,
      nameCertEndpoint,
      refinedPkg⟩,
      sameEndpoint⟩

theorem DyadicCoverPacket_finite_window_obligation_triad [AskSetup] [PackageSetup]
    {centers radii intervals mesh window transport routes provenance nameCert endpoint incidence
      radiusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicCoverPacket centers radii intervals mesh window transport routes provenance nameCert
        endpoint bundle pkg ->
      Cont window routes incidence ->
        Cont radii incidence radiusRead ->
          PkgSig bundle incidence pkg ->
            PkgSig bundle radiusRead pkg ->
              UnaryHistory centers ∧ UnaryHistory radii ∧ UnaryHistory intervals ∧
                UnaryHistory mesh ∧ UnaryHistory window ∧ UnaryHistory incidence ∧
                  UnaryHistory radiusRead ∧ Cont centers radii intervals ∧
                    Cont intervals mesh window ∧ Cont window routes endpoint ∧
                      Cont window routes incidence ∧ Cont radii incidence radiusRead ∧
                        PkgSig bundle endpoint pkg ∧ PkgSig bundle incidence pkg ∧
                          PkgSig bundle radiusRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet windowRoutesIncidence radiiIncidenceRadiusRead incidencePkg radiusReadPkg
  obtain ⟨centersUnary, radiiUnary, intervalsUnary, meshUnary, windowUnary,
    _transportUnary, routesUnary, _provenanceUnary, _nameCertUnary, _endpointUnary,
    centersRadiiIntervals, intervalsMeshWindow, windowRoutesEndpoint, _nameCertEndpoint,
    endpointPkg⟩ := packet
  have incidenceUnary : UnaryHistory incidence :=
    unary_cont_closed windowUnary routesUnary windowRoutesIncidence
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed radiiUnary incidenceUnary radiiIncidenceRadiusRead
  exact
    ⟨centersUnary, radiiUnary, intervalsUnary, meshUnary, windowUnary, incidenceUnary,
      radiusReadUnary, centersRadiiIntervals, intervalsMeshWindow, windowRoutesEndpoint,
      windowRoutesIncidence, radiiIncidenceRadiusRead, endpointPkg, incidencePkg,
      radiusReadPkg⟩

theorem DyadicCoverPacket_mesh_refinement_carrier_transport [AskSetup] [PackageSetup]
    {centers radii intervals mesh window transport routes provenance nameCert endpoint centers'
      radii' intervals' refinedMesh refinedWindow transport' routes' provenance' nameCert'
      refinedEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicCoverPacket centers radii intervals mesh window transport routes provenance nameCert
        endpoint bundle pkg ->
      hsame centers centers' -> hsame radii radii' -> hsame intervals intervals' ->
        hsame transport transport' -> hsame routes routes' -> hsame provenance provenance' ->
          hsame nameCert nameCert' -> hsame endpoint refinedEndpoint ->
            Cont intervals' refinedMesh refinedWindow ->
              Cont refinedWindow routes' refinedEndpoint ->
                PkgSig bundle refinedEndpoint pkg ->
                  DyadicCoverPacket centers' radii' intervals' refinedMesh refinedWindow
                      transport' routes' provenance' nameCert' refinedEndpoint bundle pkg ∧
                    SemanticNameCert
                      (fun row : BHist =>
                        hsame row refinedEndpoint ∧
                          DyadicCoverPacket centers' radii' intervals' refinedMesh refinedWindow
                            transport' routes' provenance' nameCert' refinedEndpoint bundle pkg)
                      (fun row : BHist => hsame row refinedEndpoint)
                      (fun row : BHist => hsame row refinedEndpoint ∧
                        PkgSig bundle refinedEndpoint pkg)
                      hsame ∧
                    hsame endpoint refinedEndpoint := by
  intro packet sameCenters sameRadii sameIntervals sameTransport sameRoutes sameProvenance
    sameNameCert sameEndpoint refinedWindowRow refinedEndpointRow refinedPkg
  have refined :
      DyadicCoverPacket centers' radii' intervals' refinedMesh refinedWindow transport' routes'
          provenance' nameCert' refinedEndpoint bundle pkg ∧
        hsame endpoint refinedEndpoint :=
    DyadicCoverPacket_finite_refinement packet sameCenters sameRadii sameIntervals sameTransport
      sameRoutes sameProvenance sameNameCert sameEndpoint refinedWindowRow refinedEndpointRow
      refinedPkg
  have certSurface :=
    DyadicCoverPacket_namecert_obligations refined.left
  exact ⟨refined.left, certSurface.left, refined.right⟩

theorem DyadicCoverPacket_finite_window_envelope_factorization [AskSetup] [PackageSetup]
    {centers radii intervals mesh window transport routes provenance nameCert endpoint incidence
      radiusRead envelopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicCoverPacket centers radii intervals mesh window transport routes provenance nameCert
        endpoint bundle pkg →
      Cont window routes incidence →
        Cont radii incidence radiusRead →
          Cont incidence routes envelopeRead →
            PkgSig bundle incidence pkg →
              PkgSig bundle radiusRead pkg →
                PkgSig bundle envelopeRead pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        hsame row endpoint ∧
                          DyadicCoverPacket centers radii intervals mesh window transport routes
                            provenance nameCert endpoint bundle pkg)
                      (fun row : BHist => hsame row endpoint)
                      (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
                      hsame ∧
                    UnaryHistory window ∧
                    UnaryHistory incidence ∧
                    UnaryHistory radiusRead ∧
                    UnaryHistory envelopeRead ∧
                    Cont intervals mesh window ∧
                    Cont window routes incidence ∧
                    Cont radii incidence radiusRead ∧
                    Cont incidence routes envelopeRead ∧
                    PkgSig bundle endpoint pkg ∧
                    PkgSig bundle envelopeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro packet windowRoutesIncidence radiiIncidenceRadiusRead incidenceRoutesEnvelopeRead
    _incidencePkg _radiusReadPkg envelopeReadPkg
  have certSurface :=
    DyadicCoverPacket_namecert_obligations packet
  obtain ⟨_centersUnary, radiiUnary, _intervalsUnary, _meshUnary, windowUnary,
    _transportUnary, routesUnary, _provenanceUnary, _nameCertUnary, _endpointUnary,
    _centersRadiiIntervals, intervalsMeshWindow, _windowRoutesEndpoint, _nameCertEndpoint,
    endpointPkg⟩ := packet
  have incidenceUnary : UnaryHistory incidence :=
    unary_cont_closed windowUnary routesUnary windowRoutesIncidence
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed radiiUnary incidenceUnary radiiIncidenceRadiusRead
  have envelopeReadUnary : UnaryHistory envelopeRead :=
    unary_cont_closed incidenceUnary routesUnary incidenceRoutesEnvelopeRead
  exact
    ⟨certSurface.left,
      windowUnary,
      incidenceUnary,
      radiusReadUnary,
      envelopeReadUnary,
      intervalsMeshWindow,
      windowRoutesIncidence,
      radiiIncidenceRadiusRead,
      incidenceRoutesEnvelopeRead,
      endpointPkg,
      envelopeReadPkg⟩

theorem DyadicCoverPacket_refined_window_total_bounded_package [AskSetup] [PackageSetup]
    {centers radii intervals mesh window transport routes provenance nameCert endpoint centers'
      radii' intervals' refinedMesh refinedWindow transport' routes' provenance' nameCert'
      refinedEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicCoverPacket centers radii intervals mesh window transport routes provenance nameCert
        endpoint bundle pkg ->
      hsame centers centers' -> hsame radii radii' -> hsame intervals intervals' ->
        hsame transport transport' -> hsame routes routes' -> hsame provenance provenance' ->
          hsame nameCert nameCert' -> hsame endpoint refinedEndpoint ->
            Cont intervals' refinedMesh refinedWindow ->
              Cont refinedWindow routes' refinedEndpoint ->
                PkgSig bundle refinedEndpoint pkg ->
                  DyadicCoverPacket centers' radii' intervals' refinedMesh refinedWindow
                      transport' routes' provenance' nameCert' refinedEndpoint bundle pkg ∧
                    SemanticNameCert
                      (fun row : BHist =>
                        hsame row refinedEndpoint ∧
                          DyadicCoverPacket centers' radii' intervals' refinedMesh refinedWindow
                            transport' routes' provenance' nameCert' refinedEndpoint bundle pkg)
                      (fun row : BHist => hsame row refinedEndpoint)
                      (fun row : BHist => hsame row refinedEndpoint ∧
                        PkgSig bundle refinedEndpoint pkg)
                      hsame ∧
                    Cont centers' radii' intervals' ∧
                    Cont intervals' refinedMesh refinedWindow ∧
                    Cont refinedWindow routes' refinedEndpoint ∧
                    PkgSig bundle refinedEndpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig SemanticNameCert hsame
  intro packet sameCenters sameRadii sameIntervals sameTransport sameRoutes sameProvenance
    sameNameCert sameEndpoint refinedWindowRow refinedEndpointRow refinedPkg
  have refined :
      DyadicCoverPacket centers' radii' intervals' refinedMesh refinedWindow transport' routes'
          provenance' nameCert' refinedEndpoint bundle pkg ∧
        hsame endpoint refinedEndpoint :=
    DyadicCoverPacket_finite_refinement packet sameCenters sameRadii sameIntervals sameTransport
      sameRoutes sameProvenance sameNameCert sameEndpoint refinedWindowRow refinedEndpointRow
      refinedPkg
  have certSurface :=
    DyadicCoverPacket_namecert_obligations refined.left
  exact
    ⟨refined.left, certSurface.left,
      refined.left.right.right.right.right.right.right.right.right.right.right.left,
      refinedWindowRow, refinedEndpointRow, refinedPkg⟩

theorem DyadicCoverPacket_total_bounded_handoff [AskSetup] [PackageSetup]
    {centers radii intervals mesh window transport routes provenance nameCert endpoint
      consumerRead totalBoundedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicCoverPacket centers radii intervals mesh window transport routes provenance nameCert
        endpoint bundle pkg →
      Cont endpoint routes consumerRead →
        Cont centers radii totalBoundedRead →
          PkgSig bundle consumerRead pkg →
            PkgSig bundle totalBoundedRead pkg →
              UnaryHistory centers ∧
                UnaryHistory radii ∧
                UnaryHistory intervals ∧
                UnaryHistory mesh ∧
                UnaryHistory window ∧
                UnaryHistory consumerRead ∧
                UnaryHistory totalBoundedRead ∧
                Cont centers radii intervals ∧
                Cont intervals mesh window ∧
                Cont window routes endpoint ∧
                Cont endpoint routes consumerRead ∧
                Cont centers radii totalBoundedRead ∧
                PkgSig bundle endpoint pkg ∧
                PkgSig bundle consumerRead pkg ∧
                PkgSig bundle totalBoundedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet endpointRoutesConsumer centersRadiiTotal consumerPkg totalBoundedPkg
  obtain ⟨centersUnary, radiiUnary, intervalsUnary, meshUnary, windowUnary,
    _transportUnary, routesUnary, _provenanceUnary, _nameCertUnary, endpointUnary,
    centersRadiiIntervals, intervalsMeshWindow, windowRoutesEndpoint, _nameCertEndpoint,
    endpointPkg⟩ := packet
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed endpointUnary routesUnary endpointRoutesConsumer
  have totalBoundedUnary : UnaryHistory totalBoundedRead :=
    unary_cont_closed centersUnary radiiUnary centersRadiiTotal
  exact
    ⟨centersUnary, radiiUnary, intervalsUnary, meshUnary, windowUnary, consumerUnary,
      totalBoundedUnary, centersRadiiIntervals, intervalsMeshWindow, windowRoutesEndpoint,
      endpointRoutesConsumer, centersRadiiTotal, endpointPkg, consumerPkg, totalBoundedPkg⟩

theorem DyadicCoverPacket_window_cell_incidence [AskSetup] [PackageSetup]
    {centers radii intervals mesh window transport routes provenance nameCert endpoint incidence
      streamRead regularRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicCoverPacket centers radii intervals mesh window transport routes provenance nameCert
        endpoint bundle pkg →
      Cont window routes incidence →
        Cont incidence routes streamRead →
          Cont streamRead routes regularRead →
            Cont regularRead routes realRead →
              PkgSig bundle incidence pkg →
                PkgSig bundle streamRead pkg →
                  PkgSig bundle regularRead pkg →
                    PkgSig bundle realRead pkg →
                      UnaryHistory centers ∧
                        UnaryHistory radii ∧
                        UnaryHistory intervals ∧
                        UnaryHistory window ∧
                        UnaryHistory incidence ∧
                        UnaryHistory streamRead ∧
                        UnaryHistory regularRead ∧
                        UnaryHistory realRead ∧
                        Cont intervals mesh window ∧
                        Cont window routes incidence ∧
                        Cont incidence routes streamRead ∧
                        Cont streamRead routes regularRead ∧
                        Cont regularRead routes realRead ∧
                        PkgSig bundle endpoint pkg ∧
                        PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet windowRoutesIncidence incidenceRoutesStream streamRoutesRegular
    regularRoutesReal _incidencePkg _streamPkg _regularPkg realPkg
  obtain ⟨centersUnary, radiiUnary, intervalsUnary, _meshUnary, windowUnary,
    _transportUnary, routesUnary, _provenanceUnary, _nameCertUnary, _endpointUnary,
    _centersRadiiIntervals, intervalsMeshWindow, _windowRoutesEndpoint, _nameCertEndpoint,
    endpointPkg⟩ := packet
  have incidenceUnary : UnaryHistory incidence :=
    unary_cont_closed windowUnary routesUnary windowRoutesIncidence
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed incidenceUnary routesUnary incidenceRoutesStream
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed streamUnary routesUnary streamRoutesRegular
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regularUnary routesUnary regularRoutesReal
  exact
    ⟨centersUnary, radiiUnary, intervalsUnary, windowUnary, incidenceUnary, streamUnary,
      regularUnary, realUnary, intervalsMeshWindow, windowRoutesIncidence,
      incidenceRoutesStream, streamRoutesRegular, regularRoutesReal, endpointPkg, realPkg⟩

end BEDC.Derived.DyadicCoverUp
