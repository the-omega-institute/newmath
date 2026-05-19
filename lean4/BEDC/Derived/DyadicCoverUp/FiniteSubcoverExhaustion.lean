import BEDC.Derived.DyadicCoverUp

namespace BEDC.Derived.DyadicCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicCoverPacket_finite_subcover_exhaustion [AskSetup] [PackageSetup]
    {centers radii intervals mesh window transport routes provenance nameCert endpoint incidence
      radiusRead envelopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicCoverPacket centers radii intervals mesh window transport routes provenance nameCert
        endpoint bundle pkg →
      Cont window routes incidence →
        Cont radii incidence radiusRead →
          Cont incidence endpoint envelopeRead →
            PkgSig bundle incidence pkg →
              PkgSig bundle radiusRead pkg →
                PkgSig bundle envelopeRead pkg →
                  UnaryHistory centers ∧ UnaryHistory radii ∧ UnaryHistory intervals ∧
                    UnaryHistory mesh ∧ UnaryHistory window ∧ UnaryHistory incidence ∧
                      UnaryHistory radiusRead ∧ UnaryHistory envelopeRead ∧
                        Cont centers radii intervals ∧ Cont intervals mesh window ∧
                          Cont window routes incidence ∧ Cont radii incidence radiusRead ∧
                            Cont incidence endpoint envelopeRead ∧ PkgSig bundle endpoint pkg ∧
                              PkgSig bundle incidence pkg ∧ PkgSig bundle radiusRead pkg ∧
                                PkgSig bundle envelopeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet windowRoutesIncidence radiiIncidenceRadius incidenceEndpointEnvelope
    incidencePkg radiusPkg envelopePkg
  obtain ⟨centersUnary, radiiUnary, intervalsUnary, meshUnary, windowUnary,
    _transportUnary, routesUnary, _provenanceUnary, _nameCertUnary, endpointUnary,
    centersRadiiIntervals, intervalsMeshWindow, _windowRoutesEndpoint, _nameCertEndpoint,
    endpointPkg⟩ := packet
  have incidenceUnary : UnaryHistory incidence :=
    unary_cont_closed windowUnary routesUnary windowRoutesIncidence
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed radiiUnary incidenceUnary radiiIncidenceRadius
  have envelopeUnary : UnaryHistory envelopeRead :=
    unary_cont_closed incidenceUnary endpointUnary incidenceEndpointEnvelope
  exact
    ⟨centersUnary, radiiUnary, intervalsUnary, meshUnary, windowUnary, incidenceUnary,
      radiusUnary, envelopeUnary, centersRadiiIntervals, intervalsMeshWindow,
      windowRoutesIncidence, radiiIncidenceRadius, incidenceEndpointEnvelope, endpointPkg,
      incidencePkg, radiusPkg, envelopePkg⟩

theorem DyadicCoverPacket_finite_window_total_bounded_correspondence
    [AskSetup] [PackageSetup]
    {centers radii intervals mesh window transport routes provenance nameCert endpoint incidence
      radiusRead totalBoundedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicCoverPacket centers radii intervals mesh window transport routes provenance nameCert
        endpoint bundle pkg ->
      Cont window routes incidence ->
        Cont radii incidence radiusRead ->
          Cont centers radii totalBoundedRead ->
            PkgSig bundle incidence pkg ->
              PkgSig bundle radiusRead pkg ->
                PkgSig bundle totalBoundedRead pkg ->
                  UnaryHistory centers ∧ UnaryHistory radii ∧ UnaryHistory intervals ∧
                    UnaryHistory window ∧ UnaryHistory incidence ∧ UnaryHistory radiusRead ∧
                      UnaryHistory totalBoundedRead ∧ Cont centers radii intervals ∧
                        Cont intervals mesh window ∧ Cont window routes incidence ∧
                          Cont radii incidence radiusRead ∧
                            Cont centers radii totalBoundedRead ∧
                              PkgSig bundle endpoint pkg ∧ PkgSig bundle incidence pkg ∧
                                PkgSig bundle radiusRead pkg ∧
                                  PkgSig bundle totalBoundedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet windowRoutesIncidence radiiIncidenceRadius centersRadiiTotalBounded incidencePkg
    radiusPkg totalBoundedPkg
  obtain ⟨centersUnary, radiiUnary, intervalsUnary, _meshUnary, windowUnary,
    _transportUnary, routesUnary, _provenanceUnary, _nameCertUnary, _endpointUnary,
    centersRadiiIntervals, intervalsMeshWindow, _windowRoutesEndpoint, _nameCertEndpoint,
    endpointPkg⟩ := packet
  have incidenceUnary : UnaryHistory incidence :=
    unary_cont_closed windowUnary routesUnary windowRoutesIncidence
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed radiiUnary incidenceUnary radiiIncidenceRadius
  have totalBoundedUnary : UnaryHistory totalBoundedRead :=
    unary_cont_closed centersUnary radiiUnary centersRadiiTotalBounded
  exact
    ⟨centersUnary, radiiUnary, intervalsUnary, windowUnary, incidenceUnary, radiusUnary,
      totalBoundedUnary, centersRadiiIntervals, intervalsMeshWindow, windowRoutesIncidence,
      radiiIncidenceRadius, centersRadiiTotalBounded, endpointPkg, incidencePkg, radiusPkg,
      totalBoundedPkg⟩

end BEDC.Derived.DyadicCoverUp
