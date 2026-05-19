import BEDC.Derived.DyadicCoverUp

namespace BEDC.Derived.DyadicCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicCoverPacket_total_bounded_radius_ledger [AskSetup] [PackageSetup]
    {centers radii intervals mesh window transport routes provenance nameCert endpoint incidence
      radiusRead totalBoundedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicCoverPacket centers radii intervals mesh window transport routes provenance nameCert
        endpoint bundle pkg ->
      Cont window routes incidence ->
        Cont radii incidence radiusRead ->
          Cont centers radiusRead totalBoundedRead ->
            PkgSig bundle radiusRead pkg ->
              PkgSig bundle totalBoundedRead pkg ->
                UnaryHistory centers ∧
                  UnaryHistory radii ∧
                  UnaryHistory radiusRead ∧
                  UnaryHistory totalBoundedRead ∧
                  Cont window routes incidence ∧
                  Cont radii incidence radiusRead ∧
                  Cont centers radiusRead totalBoundedRead ∧
                  PkgSig bundle endpoint pkg ∧
                  PkgSig bundle radiusRead pkg ∧
                  PkgSig bundle totalBoundedRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg
  intro packet windowRoutesIncidence radiiIncidenceRadius centersRadiusTotal radiusPkg
    totalBoundedPkg
  obtain ⟨centersUnary, radiiUnary, _intervalsUnary, _meshUnary, windowUnary,
    _transportUnary, routesUnary, _provenanceUnary, _nameCertUnary, _endpointUnary,
    _centersRadiiIntervals, _intervalsMeshWindow, _windowRoutesEndpoint, _nameCertEndpoint,
    endpointPkg⟩ := packet
  have incidenceUnary : UnaryHistory incidence :=
    unary_cont_closed windowUnary routesUnary windowRoutesIncidence
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed radiiUnary incidenceUnary radiiIncidenceRadius
  have totalBoundedUnary : UnaryHistory totalBoundedRead :=
    unary_cont_closed centersUnary radiusReadUnary centersRadiusTotal
  exact
    ⟨centersUnary, radiiUnary, radiusReadUnary, totalBoundedUnary, windowRoutesIncidence,
      radiiIncidenceRadius, centersRadiusTotal, endpointPkg, radiusPkg, totalBoundedPkg⟩

end BEDC.Derived.DyadicCoverUp
