import BEDC.Derived.CausalCommitmentUp

namespace BEDC.Derived.CausalCommitmentUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem CausalCommitmentPublicForwardGapExport [AskSetup] [PackageSetup]
    {observed regularity gap forward locality transport continuation provenance localCert
      routeRead ledgerRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CausalCommitmentForwardGapCarrier observed regularity gap forward locality transport
        continuation provenance localCert bundle pkg ->
      Cont continuation localCert routeRead ->
        Cont routeRead locality ledgerRead ->
          Cont ledgerRead localCert publicRead ->
            PkgSig bundle publicRead pkg ->
              UnaryHistory observed ∧ UnaryHistory regularity ∧ UnaryHistory gap ∧
                UnaryHistory forward ∧ UnaryHistory locality ∧ UnaryHistory routeRead ∧
                  UnaryHistory ledgerRead ∧ UnaryHistory publicRead ∧
                    Cont observed regularity gap ∧ Cont gap forward continuation ∧
                      Cont forward locality localCert ∧
                        Cont continuation localCert routeRead ∧
                          Cont routeRead locality ledgerRead ∧
                            Cont ledgerRead localCert publicRead ∧
                              PkgSig bundle localCert pkg ∧
                                PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier continuationLocalCertRoute routeLocalityLedger ledgerLocalCertPublic
    publicPkg
  have baseCarrier :
      CausalCommitmentCarrier observed regularity gap forward transport continuation
        provenance localCert bundle pkg :=
    carrier.left
  have localityUnary : UnaryHistory locality :=
    carrier.right.left
  have forwardLocalityName : Cont forward locality localCert :=
    carrier.right.right
  obtain ⟨observedUnary, regularityUnary, gapUnary, forwardUnary, _transportUnary,
    continuationUnary, _provenanceUnary, localCertUnary, observedRegularityGap,
    gapForwardContinuation, _transportContinuationProvenance, localCertPkg⟩ := baseCarrier
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed continuationUnary localCertUnary continuationLocalCertRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed routeReadUnary localityUnary routeLocalityLedger
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed ledgerReadUnary localCertUnary ledgerLocalCertPublic
  exact
    ⟨observedUnary, regularityUnary, gapUnary, forwardUnary, localityUnary,
      routeReadUnary, ledgerReadUnary, publicReadUnary, observedRegularityGap,
      gapForwardContinuation, forwardLocalityName, continuationLocalCertRoute,
      routeLocalityLedger, ledgerLocalCertPublic, localCertPkg, publicPkg⟩

end BEDC.Derived.CausalCommitmentUp
