import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_cauchy_tail_envelope_factorization [AskSetup]
    [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      envelopeStart envelopeWindow envelopeCompare envelopeAttach endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont readback realSeal envelopeStart ->
        Cont envelopeStart windows envelopeWindow ->
          Cont envelopeWindow dyadic envelopeCompare ->
            Cont envelopeCompare route envelopeAttach ->
              Cont envelopeAttach cert endpoint ->
                PkgSig bundle endpoint pkg ->
                  UnaryHistory readback ∧ UnaryHistory realSeal ∧
                    UnaryHistory envelopeStart ∧ UnaryHistory envelopeWindow ∧
                      UnaryHistory envelopeCompare ∧ UnaryHistory envelopeAttach ∧
                        UnaryHistory endpoint ∧ Cont readback realSeal envelopeStart ∧
                          Cont envelopeStart windows envelopeWindow ∧
                            Cont envelopeWindow dyadic envelopeCompare ∧
                              Cont envelopeCompare route envelopeAttach ∧
                                Cont envelopeAttach cert endpoint ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier readbackRealSealEnvelope envelopeStartWindowsEnvelope
    envelopeWindowDyadicCompare envelopeCompareRouteAttach envelopeAttachCertEndpoint
    endpointPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have envelopeStartUnary : UnaryHistory envelopeStart :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealEnvelope
  have envelopeWindowUnary : UnaryHistory envelopeWindow :=
    unary_cont_closed envelopeStartUnary windowsUnary envelopeStartWindowsEnvelope
  have envelopeCompareUnary : UnaryHistory envelopeCompare :=
    unary_cont_closed envelopeWindowUnary dyadicUnary envelopeWindowDyadicCompare
  have envelopeAttachUnary : UnaryHistory envelopeAttach :=
    unary_cont_closed envelopeCompareUnary routeUnary envelopeCompareRouteAttach
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed envelopeAttachUnary certUnary envelopeAttachCertEndpoint
  exact
    ⟨readbackUnary, realSealUnary, envelopeStartUnary, envelopeWindowUnary,
      envelopeCompareUnary, envelopeAttachUnary, endpointUnary, readbackRealSealEnvelope,
      envelopeStartWindowsEnvelope, envelopeWindowDyadicCompare, envelopeCompareRouteAttach,
      envelopeAttachCertEndpoint, provenancePkg, endpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
