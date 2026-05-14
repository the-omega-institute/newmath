import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_seal_source_synchronization [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      sealSource sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal triangle sealSource ->
        Cont sealSource dyadic sealRead ->
          PkgSig bundle sealRead pkg ->
            UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory dyadic ∧
              UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory sealSource ∧
                UnaryHistory sealRead ∧ Cont diagonal triangle sealSource ∧
                  Cont sealSource dyadic sealRead ∧ Cont dyadic windows readback ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier diagonalTriangleSource sourceDyadicRead sealReadPkg
  obtain ⟨diagonalUnary, triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have sealSourceUnary : UnaryHistory sealSource :=
    unary_cont_closed diagonalUnary triangleUnary diagonalTriangleSource
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed sealSourceUnary dyadicUnary sourceDyadicRead
  exact
    ⟨diagonalUnary, triangleUnary, dyadicUnary, windowsUnary, readbackUnary,
      sealSourceUnary, sealReadUnary, diagonalTriangleSource, sourceDyadicRead,
      dyadicWindowsReadback, provenancePkg, sealReadPkg⟩

theorem DiagonalLimitCompatibility_real_seal_factorization [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      sealSource sealRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal triangle sealSource ->
        Cont sealSource dyadic sealRead ->
          Cont readback realSeal endpoint ->
            PkgSig bundle sealRead pkg ->
              PkgSig bundle endpoint pkg ->
                UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory dyadic ∧
                  UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
                    UnaryHistory sealSource ∧ UnaryHistory sealRead ∧ UnaryHistory endpoint ∧
                      Cont diagonal triangle sealSource ∧ Cont sealSource dyadic sealRead ∧
                        Cont dyadic windows readback ∧ Cont readback realSeal endpoint ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg ∧
                            PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier diagonalTriangleSource sourceDyadicRead readbackEndpoint sealReadPkg
    endpointPkg
  obtain ⟨diagonalUnary, triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have sealSourceUnary : UnaryHistory sealSource :=
    unary_cont_closed diagonalUnary triangleUnary diagonalTriangleSource
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed sealSourceUnary dyadicUnary sourceDyadicRead
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed readbackUnary realSealUnary readbackEndpoint
  exact
    ⟨diagonalUnary, triangleUnary, dyadicUnary, windowsUnary, readbackUnary, realSealUnary,
      sealSourceUnary, sealReadUnary, endpointUnary, diagonalTriangleSource, sourceDyadicRead,
      dyadicWindowsReadback, readbackEndpoint, provenancePkg, sealReadPkg, endpointPkg⟩

theorem DiagonalLimitCompatibility_real_seal_consumer_scope [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      sealSource sealRead endpoint consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal triangle sealSource ->
        Cont sealSource dyadic sealRead ->
          Cont readback realSeal endpoint ->
            Cont sealRead endpoint consumer ->
              PkgSig bundle sealRead pkg ->
                PkgSig bundle endpoint pkg ->
                  PkgSig bundle consumer pkg ->
                    UnaryHistory sealSource ∧ UnaryHistory sealRead ∧ UnaryHistory endpoint ∧
                      UnaryHistory consumer ∧ Cont diagonal triangle sealSource ∧
                        Cont sealSource dyadic sealRead ∧ Cont readback realSeal endpoint ∧
                          Cont sealRead endpoint consumer ∧ PkgSig bundle provenance pkg ∧
                            PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier diagonalTriangleSource sourceDyadicRead readbackEndpoint sealReadEndpoint
    _sealReadPkg _endpointPkg consumerPkg
  obtain ⟨diagonalUnary, triangleUnary, _sealRowUnary, dyadicUnary, _windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have sealSourceUnary : UnaryHistory sealSource :=
    unary_cont_closed diagonalUnary triangleUnary diagonalTriangleSource
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed sealSourceUnary dyadicUnary sourceDyadicRead
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed readbackUnary realSealUnary readbackEndpoint
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed sealReadUnary endpointUnary sealReadEndpoint
  exact
    ⟨sealSourceUnary, sealReadUnary, endpointUnary, consumerUnary, diagonalTriangleSource,
      sourceDyadicRead, readbackEndpoint, sealReadEndpoint, provenancePkg, consumerPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
