import BEDC.Derived.CausalCommitmentUp

namespace BEDC.Derived.CausalCommitmentUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CausalCommitmentForwardGapObserverRoute [AskSetup] [PackageSetup]
    {observed regularity gap forward locality transport continuation provenance localCert
      observerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CausalCommitmentForwardGapCarrier observed regularity gap forward locality transport
        continuation provenance localCert bundle pkg ->
      Cont localCert locality observerRead ->
        PkgSig bundle observerRead pkg ->
          UnaryHistory observed ∧ UnaryHistory regularity ∧ UnaryHistory gap ∧
            UnaryHistory forward ∧ UnaryHistory locality ∧ UnaryHistory observerRead ∧
              Cont observed regularity gap ∧ Cont gap forward continuation ∧
                Cont forward locality localCert ∧ Cont localCert locality observerRead ∧
                  PkgSig bundle localCert pkg ∧ PkgSig bundle observerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier localCertLocalityObserver observerPkg
  have baseCarrier :
      CausalCommitmentCarrier observed regularity gap forward transport continuation
        provenance localCert bundle pkg :=
    carrier.left
  have localityUnary : UnaryHistory locality :=
    carrier.right.left
  have forwardLocalityLocalCert : Cont forward locality localCert :=
    carrier.right.right
  obtain
    ⟨observedUnary, regularityUnary, gapUnary, forwardUnary, _transportUnary,
      _continuationUnary, _provenanceUnary, localCertUnary, observedRegularityGap,
      gapForwardContinuation, _transportContinuationProvenance, localCertPkg⟩ :=
      baseCarrier
  have observerReadUnary : UnaryHistory observerRead :=
    unary_cont_closed localCertUnary localityUnary localCertLocalityObserver
  exact
    ⟨observedUnary, regularityUnary, gapUnary, forwardUnary, localityUnary,
      observerReadUnary, observedRegularityGap, gapForwardContinuation,
      forwardLocalityLocalCert, localCertLocalityObserver, localCertPkg, observerPkg⟩

end BEDC.Derived.CausalCommitmentUp
