import BEDC.Derived.CausalCommitmentUp

namespace BEDC.Derived.CausalCommitmentUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem CausalCommitmentKernelRowExhaustion [AskSetup] [PackageSetup]
    {observed regularity gap forward locality transport continuation provenance localCert
      routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CausalCommitmentForwardGapCarrier observed regularity gap forward locality transport
        continuation provenance localCert bundle pkg ->
      Cont continuation localCert routeRead ->
        PkgSig bundle routeRead pkg ->
          UnaryHistory observed ∧ UnaryHistory regularity ∧ UnaryHistory gap ∧
            UnaryHistory forward ∧ UnaryHistory locality ∧ UnaryHistory transport ∧
              UnaryHistory continuation ∧ UnaryHistory provenance ∧ UnaryHistory localCert ∧
                UnaryHistory routeRead ∧ Cont observed regularity gap ∧
                  Cont gap forward continuation ∧ Cont forward locality localCert ∧
                    Cont continuation localCert routeRead ∧ PkgSig bundle localCert pkg ∧
                      PkgSig bundle routeRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier continuationLocalCertRoute routePkg
  have baseCarrier :
      CausalCommitmentCarrier observed regularity gap forward transport continuation
        provenance localCert bundle pkg :=
    carrier.left
  have localityUnary : UnaryHistory locality :=
    carrier.right.left
  have forwardLocalityName : Cont forward locality localCert :=
    carrier.right.right
  obtain ⟨observedUnary, regularityUnary, gapUnary, forwardUnary, transportUnary,
    continuationUnary, provenanceUnary, localCertUnary, observedRegularityGap,
    gapForwardContinuation, _transportContinuationProvenance, localCertPkg⟩ := baseCarrier
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed continuationUnary localCertUnary continuationLocalCertRoute
  exact
    ⟨observedUnary, regularityUnary, gapUnary, forwardUnary, localityUnary, transportUnary,
      continuationUnary, provenanceUnary, localCertUnary, routeReadUnary,
      observedRegularityGap, gapForwardContinuation, forwardLocalityName,
      continuationLocalCertRoute, localCertPkg, routePkg⟩

end BEDC.Derived.CausalCommitmentUp
