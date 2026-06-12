import BEDC.Derived.LocatedMetricUp

namespace BEDC.Derived.LocatedMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedMetricCarrier_scoped_obligation_rows [AskSetup] [PackageSetup]
    {point metric located stream regseq real separated transport replay provenance name
      metricRead locatedRead regseqRead realRead separatedRead radiusRead zeroRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedMetricCarrier point metric located stream regseq real separated transport replay provenance
        name bundle pkg →
      Cont point metric metricRead →
        Cont metric located locatedRead →
          Cont located stream regseqRead →
            Cont regseq real realRead →
              Cont real separated separatedRead →
                Cont located transport radiusRead →
                  Cont separated transport zeroRead →
                    Cont real replay sealRead →
                      PkgSig bundle radiusRead pkg →
                        PkgSig bundle zeroRead pkg →
                          PkgSig bundle sealRead pkg →
                            UnaryHistory radiusRead ∧ UnaryHistory zeroRead ∧
                              UnaryHistory sealRead ∧ Cont located transport radiusRead ∧
                                Cont separated transport zeroRead ∧ Cont real replay sealRead ∧
                                  Cont transport replay provenance ∧
                                    PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier _pointMetricRead _metricLocatedRead _locatedStreamRead _regseqRealRead
    _realSeparatedRead locatedTransportRadius separatedTransportZero realReplaySeal
    _radiusPkg _zeroPkg _sealPkg
  obtain ⟨_pointUnary, _metricUnary, locatedUnary, _streamUnary, _regseqUnary, realUnary,
    separatedUnary, transportUnary, replayUnary, _provenanceUnary, _nameUnary,
    transportReplayProvenance, provenancePkg, _namePkg⟩ := carrier
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed locatedUnary transportUnary locatedTransportRadius
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed separatedUnary transportUnary separatedTransportZero
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed realUnary replayUnary realReplaySeal
  exact
    ⟨radiusUnary, zeroUnary, sealUnary, locatedTransportRadius, separatedTransportZero,
      realReplaySeal, transportReplayProvenance, provenancePkg⟩

end BEDC.Derived.LocatedMetricUp
