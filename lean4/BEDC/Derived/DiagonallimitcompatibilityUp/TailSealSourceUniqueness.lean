import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityTailSealSourceUniqueness [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      tailSource tailSource' tailRead tailRead' endpoint endpoint' terminal terminal' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal triangle tailSource ->
        Cont diagonal triangle tailSource' ->
          Cont tailSource dyadic tailRead ->
            Cont tailSource' dyadic tailRead' ->
              Cont readback realSeal endpoint ->
                Cont readback realSeal endpoint' ->
                  Cont tailRead endpoint terminal ->
                    Cont tailRead' endpoint' terminal' ->
                      PkgSig bundle terminal pkg ->
                        PkgSig bundle terminal' pkg ->
                          UnaryHistory tailSource ∧ UnaryHistory tailSource' ∧
                            UnaryHistory tailRead ∧ UnaryHistory tailRead' ∧
                              UnaryHistory endpoint ∧ UnaryHistory endpoint' ∧
                                UnaryHistory terminal ∧ UnaryHistory terminal' ∧
                                  hsame tailSource tailSource' ∧ hsame tailRead tailRead' ∧
                                    hsame endpoint endpoint' ∧ hsame terminal terminal' ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle terminal pkg ∧
                                          PkgSig bundle terminal' pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig UnaryHistory
  intro carrier diagonalTriangleTailSource diagonalTriangleTailSource'
    tailSourceDyadicTailRead tailSource'DyadicTailRead' readbackRealSealEndpoint
    readbackRealSealEndpoint' tailReadEndpointTerminal tailRead'Endpoint'Terminal'
    terminalPkg terminalPkg'
  obtain ⟨diagonalUnary, triangleUnary, _sealRowUnary, dyadicUnary, _windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have tailSourceUnary : UnaryHistory tailSource :=
    unary_cont_closed diagonalUnary triangleUnary diagonalTriangleTailSource
  have tailSourceUnary' : UnaryHistory tailSource' :=
    unary_cont_closed diagonalUnary triangleUnary diagonalTriangleTailSource'
  have tailSourceSame : hsame tailSource tailSource' :=
    cont_deterministic diagonalTriangleTailSource diagonalTriangleTailSource'
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed tailSourceUnary dyadicUnary tailSourceDyadicTailRead
  have tailReadUnary' : UnaryHistory tailRead' :=
    unary_cont_closed tailSourceUnary' dyadicUnary tailSource'DyadicTailRead'
  have tailReadSame : hsame tailRead tailRead' :=
    cont_respects_hsame tailSourceSame (hsame_refl dyadic) tailSourceDyadicTailRead
      tailSource'DyadicTailRead'
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealEndpoint
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealEndpoint'
  have endpointSame : hsame endpoint endpoint' :=
    cont_deterministic readbackRealSealEndpoint readbackRealSealEndpoint'
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed tailReadUnary endpointUnary tailReadEndpointTerminal
  have terminalUnary' : UnaryHistory terminal' :=
    unary_cont_closed tailReadUnary' endpointUnary' tailRead'Endpoint'Terminal'
  have terminalSame : hsame terminal terminal' :=
    cont_respects_hsame tailReadSame endpointSame tailReadEndpointTerminal
      tailRead'Endpoint'Terminal'
  exact
    ⟨tailSourceUnary, tailSourceUnary', tailReadUnary, tailReadUnary', endpointUnary,
      endpointUnary', terminalUnary, terminalUnary', tailSourceSame, tailReadSame,
      endpointSame, terminalSame, provenancePkg, terminalPkg, terminalPkg'⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
