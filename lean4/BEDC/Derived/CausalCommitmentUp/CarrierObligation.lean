import BEDC.Derived.CausalCommitmentUp

namespace BEDC.Derived.CausalCommitmentUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CausalCommitmentCarrier_obligation [AskSetup] [PackageSetup]
    {observed regularity gap forward locality transport continuation provenance localCert
      routeRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CausalCommitmentForwardGapCarrier observed regularity gap forward locality transport
        continuation provenance localCert bundle pkg →
      Cont continuation localCert routeRead →
        Cont routeRead locality ledgerRead →
          PkgSig bundle ledgerRead pkg →
            UnaryHistory observed ∧ UnaryHistory regularity ∧ UnaryHistory gap ∧
              UnaryHistory forward ∧ UnaryHistory locality ∧ UnaryHistory routeRead ∧
                UnaryHistory ledgerRead ∧ Cont observed regularity gap ∧
                  Cont gap forward continuation ∧ Cont forward locality localCert ∧
                    Cont continuation localCert routeRead ∧ Cont routeRead locality ledgerRead ∧
                      PkgSig bundle localCert pkg ∧ PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont
  intro carrier continuationLocalCertRoute routeLocalityLedger ledgerPkg
  obtain ⟨baseCarrier, localityUnary, forwardLocalityLocalCert⟩ := carrier
  obtain ⟨observedUnary, regularityUnary, gapUnary, forwardUnary, _transportUnary,
    continuationUnary, _provenanceUnary, localCertUnary, observedRegularityGap,
    gapForwardContinuation, _transportContinuationProvenance, localCertPkg⟩ := baseCarrier
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed continuationUnary localCertUnary continuationLocalCertRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed routeReadUnary localityUnary routeLocalityLedger
  exact
    ⟨observedUnary, regularityUnary, gapUnary, forwardUnary, localityUnary, routeReadUnary,
      ledgerReadUnary, observedRegularityGap, gapForwardContinuation,
      forwardLocalityLocalCert, continuationLocalCertRoute, routeLocalityLedger, localCertPkg,
      ledgerPkg⟩

end BEDC.Derived.CausalCommitmentUp
