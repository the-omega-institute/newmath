import BEDC.Derived.LocatedCutUp

namespace BEDC.Derived.LocatedCutUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedCutCarrier_regular_cauchy_bridge_source [AskSetup] [PackageSetup]
    {lower upper window handoff sealRow transportRow route provenance localCert bridge : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
        bundle pkg ->
      UnaryHistory lower ->
        UnaryHistory upper ->
          UnaryHistory handoff ->
            UnaryHistory route ->
              UnaryHistory localCert ->
                Cont handoff provenance bridge ->
                  PkgSig bundle bridge pkg ->
                    ∃ witness : BHist,
                      UnaryHistory witness ∧ Cont lower upper witness ∧ hsame witness window ∧
                        Cont window handoff transportRow ∧ hsame handoff provenance ∧
                          UnaryHistory bridge ∧ Cont handoff provenance bridge ∧
                            PkgSig bundle bridge pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier lowerUnary upperUnary handoffUnary routeUnary localCertUnary bridgeRoute bridgePkg
  obtain ⟨witness, witnessRoute, witnessUnary, sameWitnessWindow, windowHandoffTransport,
    sameHandoffProvenance, _provenancePkg⟩ :=
    LocatedCutCarrier_interval_witness_extraction carrier lowerUnary upperUnary handoffUnary
      routeUnary localCertUnary
  have exhausted :=
    LocatedCutCarrier_dyadic_interval_exhaustion carrier lowerUnary upperUnary handoffUnary
      routeUnary localCertUnary
  obtain ⟨_lowerUnary, _upperUnary, _windowUnary, _transportUnary, provenanceUnary,
    _sealUnary, _lowerUpperWindow, _windowHandoffTransport, _transportRouteProvenance,
    _provenanceLocalCertSeal, _provenancePkg, _sameHandoffProvenance⟩ := exhausted
  have bridgeUnary : UnaryHistory bridge :=
    unary_cont_closed handoffUnary provenanceUnary bridgeRoute
  exact
    ⟨witness, witnessUnary, witnessRoute, sameWitnessWindow, windowHandoffTransport,
      sameHandoffProvenance, bridgeUnary, bridgeRoute, bridgePkg⟩

end BEDC.Derived.LocatedCutUp
