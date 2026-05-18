import BEDC.Derived.CausalCommitmentUp

namespace BEDC.Derived.CausalCommitmentUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem CausalCommitmentObserverLocalityHandoff [AskSetup] [PackageSetup]
    {observed regularity gap forward locality transport continuation provenance localCert
      observerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CausalCommitmentForwardGapCarrier observed regularity gap forward locality transport
        continuation provenance localCert bundle pkg ->
      Cont locality localCert observerRead ->
        PkgSig bundle observerRead pkg ->
          UnaryHistory observed ∧ UnaryHistory regularity ∧ UnaryHistory gap ∧
            UnaryHistory forward ∧ UnaryHistory locality ∧ UnaryHistory observerRead ∧
              Cont observed regularity gap ∧ Cont gap forward continuation ∧
                Cont forward locality localCert ∧ Cont locality localCert observerRead ∧
                  PkgSig bundle observerRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier localityLocalCertObserver observerPkg
  have baseCarrier :
      CausalCommitmentCarrier observed regularity gap forward transport continuation
        provenance localCert bundle pkg :=
    carrier.left
  have localityUnary : UnaryHistory locality :=
    carrier.right.left
  have forwardLocalityLocalCert : Cont forward locality localCert :=
    carrier.right.right
  obtain ⟨observedUnary, regularityUnary, gapUnary, forwardUnary, _transportUnary,
    _continuationUnary, _provenanceUnary, localCertUnary, observedRegularityGap,
    gapForwardContinuation, _transportContinuationProvenance, _localCertPkg⟩ := baseCarrier
  have observerReadUnary : UnaryHistory observerRead :=
    unary_cont_closed localityUnary localCertUnary localityLocalCertObserver
  exact
    ⟨observedUnary, regularityUnary, gapUnary, forwardUnary, localityUnary,
      observerReadUnary, observedRegularityGap, gapForwardContinuation,
      forwardLocalityLocalCert, localityLocalCertObserver, observerPkg⟩

end BEDC.Derived.CausalCommitmentUp
