import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp.CompletionConsumerNonescape

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCompletionConsumerNonescape
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      endpoint completion : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont readback realSeal endpoint →
        Cont endpoint cert completion →
          PkgSig bundle endpoint pkg →
            PkgSig bundle completion pkg →
              UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory dyadic ∧
                UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
                  UnaryHistory endpoint ∧ UnaryHistory completion ∧
                    Cont diagonal triangle sealRow ∧ Cont dyadic windows readback ∧
                      Cont readback realSeal endpoint ∧ Cont endpoint cert completion ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg ∧
                          PkgSig bundle completion pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier readbackRealSealEndpoint endpointCertCompletion endpointPkg completionPkg
  obtain ⟨diagonalUnary, triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    certUnary, diagonalTriangleSeal, dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealEndpoint
  have completionUnary : UnaryHistory completion :=
    unary_cont_closed endpointUnary certUnary endpointCertCompletion
  exact
    ⟨diagonalUnary, triangleUnary, dyadicUnary, windowsUnary, readbackUnary, realSealUnary,
      endpointUnary, completionUnary, diagonalTriangleSeal, dyadicWindowsReadback,
      readbackRealSealEndpoint, endpointCertCompletion, provenancePkg, endpointPkg,
      completionPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp.CompletionConsumerNonescape
