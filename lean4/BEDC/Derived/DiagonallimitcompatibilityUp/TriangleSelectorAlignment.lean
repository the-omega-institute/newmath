import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_triangle_selector_alignment [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector triangleSelector : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic selector ->
        Cont selector windows triangleSelector ->
          PkgSig bundle triangleSelector pkg ->
            UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory dyadic ∧
              UnaryHistory windows ∧ UnaryHistory selector ∧ UnaryHistory triangleSelector ∧
                Cont diagonal triangle sealRow ∧ Cont diagonal dyadic selector ∧
                  Cont selector windows triangleSelector ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle triangleSelector pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier diagonalDyadicSelector selectorWindowsTriangle triangleSelectorPkg
  obtain ⟨diagonalUnary, triangleUnary, _sealUnary, dyadicUnary, windowsUnary,
    _readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicSelector
  have triangleSelectorUnary : UnaryHistory triangleSelector :=
    unary_cont_closed selectorUnary windowsUnary selectorWindowsTriangle
  exact
    ⟨diagonalUnary, triangleUnary, dyadicUnary, windowsUnary, selectorUnary,
      triangleSelectorUnary, diagonalTriangleSeal, diagonalDyadicSelector,
      selectorWindowsTriangle, provenancePkg, triangleSelectorPkg⟩

theorem DiagonalLimitCompatibility_real_seal_exactness [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      sealRead realEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont sealRow readback sealRead ->
        Cont sealRead realSeal realEndpoint ->
          PkgSig bundle realEndpoint pkg ->
            UnaryHistory sealRow ∧ UnaryHistory readback ∧ UnaryHistory sealRead ∧
              UnaryHistory realSeal ∧ UnaryHistory realEndpoint ∧
                Cont sealRow readback sealRead ∧ Cont sealRead realSeal realEndpoint ∧
                  Cont route cert transport ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle realEndpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier sealRowReadbackSealRead sealReadRealSealEndpoint realEndpointPkg
  obtain ⟨_diagonalUnary, _triangleUnary, sealRowUnary, _dyadicUnary, _windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    routeCertTransport, provenancePkg⟩ := carrier
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed sealRowUnary readbackUnary sealRowReadbackSealRead
  have realEndpointUnary : UnaryHistory realEndpoint :=
    unary_cont_closed sealReadUnary realSealUnary sealReadRealSealEndpoint
  exact
    ⟨sealRowUnary, readbackUnary, sealReadUnary, realSealUnary, realEndpointUnary,
      sealRowReadbackSealRead, sealReadRealSealEndpoint, routeCertTransport, provenancePkg,
      realEndpointPkg⟩

theorem DiagonalLimitCompatibilityTriangleSelectorAlignment [AskSetup] [PackageSetup]
    {source selector triangle sealRow _transport route provenance _nameRow selectorRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source →
      UnaryHistory selector →
        UnaryHistory sealRow →
          UnaryHistory route →
            Cont source selector triangle →
              Cont triangle sealRow selectorRead →
                Cont selectorRead route sealRead →
                  PkgSig bundle provenance pkg →
                    PkgSig bundle sealRead pkg →
                      UnaryHistory triangle ∧ UnaryHistory selectorRead ∧
                        UnaryHistory sealRead ∧ Cont source selector triangle ∧
                          Cont triangle sealRow selectorRead ∧
                            Cont selectorRead route sealRead ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  intro sourceUnary selectorUnary sealUnary routeUnary sourceSelectorTriangle
    triangleSealSelector selectorRouteSeal provenancePkg sealPkg
  have triangleUnary : UnaryHistory triangle :=
    unary_cont_closed sourceUnary selectorUnary sourceSelectorTriangle
  have selectorReadUnary : UnaryHistory selectorRead :=
    unary_cont_closed triangleUnary sealUnary triangleSealSelector
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed selectorReadUnary routeUnary selectorRouteSeal
  exact
    ⟨triangleUnary, selectorReadUnary, sealReadUnary, sourceSelectorTriangle,
      triangleSealSelector, selectorRouteSeal, provenancePkg, sealPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
