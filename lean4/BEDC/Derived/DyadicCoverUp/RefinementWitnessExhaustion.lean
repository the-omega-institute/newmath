import BEDC.Derived.DyadicCoverUp

namespace BEDC.Derived.DyadicCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicCoverPacket_refinement_witness_exhaustion [AskSetup] [PackageSetup]
    {centers radii intervals mesh window transport routes provenance nameCert endpoint centers'
      radii' intervals' refinedMesh refinedWindow transport' routes' provenance' nameCert'
      refinedEndpoint witnessRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicCoverPacket centers radii intervals mesh window transport routes provenance nameCert
        endpoint bundle pkg ->
      hsame centers centers' -> hsame radii radii' -> hsame intervals intervals' ->
        hsame transport transport' -> hsame routes routes' -> hsame provenance provenance' ->
          hsame nameCert nameCert' -> hsame endpoint refinedEndpoint ->
            Cont intervals' refinedMesh refinedWindow ->
              Cont refinedWindow routes' refinedEndpoint ->
                Cont refinedEndpoint routes' witnessRead ->
                  PkgSig bundle refinedEndpoint pkg ->
                    PkgSig bundle witnessRead pkg ->
                      DyadicCoverPacket centers' radii' intervals' refinedMesh refinedWindow
                          transport' routes' provenance' nameCert' refinedEndpoint bundle pkg ∧
                        UnaryHistory witnessRead ∧
                        Cont refinedEndpoint routes' witnessRead ∧
                        PkgSig bundle witnessRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg
  intro packet sameCenters sameRadii sameIntervals sameTransport sameRoutes sameProvenance
    sameNameCert sameEndpoint intervalsRefined refinedEndpointRow endpointRoutesWitness
    refinedPkg witnessPkg
  have refined :
      DyadicCoverPacket centers' radii' intervals' refinedMesh refinedWindow transport' routes'
          provenance' nameCert' refinedEndpoint bundle pkg ∧
        hsame endpoint refinedEndpoint :=
    DyadicCoverPacket_finite_refinement packet sameCenters sameRadii sameIntervals sameTransport
      sameRoutes sameProvenance sameNameCert sameEndpoint intervalsRefined refinedEndpointRow
      refinedPkg
  obtain ⟨_centersUnary, _radiiUnary, _intervalsUnary, _meshUnary, _windowUnary,
    _transportUnary, routesUnary, _provenanceUnary, _nameCertUnary, refinedEndpointUnary,
    _centersRadiiIntervals, _intervalsRefined, _refinedEndpointRow, _nameCertEndpoint,
    _endpointPkg⟩ := refined.left
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed refinedEndpointUnary routesUnary endpointRoutesWitness
  exact ⟨refined.left, witnessUnary, endpointRoutesWitness, witnessPkg⟩

end BEDC.Derived.DyadicCoverUp
