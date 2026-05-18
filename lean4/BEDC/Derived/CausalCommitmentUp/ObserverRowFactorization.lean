import BEDC.Derived.CausalCommitmentUp

namespace BEDC.Derived.CausalCommitmentUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem CausalCommitmentObserverRowFactorization [AskSetup] [PackageSetup]
    {observed regularity gap forward locality transport continuation provenance localCert
      observerRead factorRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CausalCommitmentForwardGapCarrier observed regularity gap forward locality transport
        continuation provenance localCert bundle pkg ->
      Cont localCert locality observerRead ->
        Cont observerRead forward factorRead ->
          PkgSig bundle factorRead pkg ->
            UnaryHistory observed ∧ UnaryHistory regularity ∧ UnaryHistory gap ∧
              UnaryHistory forward ∧ UnaryHistory locality ∧ UnaryHistory localCert ∧
                UnaryHistory observerRead ∧ UnaryHistory factorRead ∧
                  Cont observed regularity gap ∧ Cont gap forward continuation ∧
                    Cont forward locality localCert ∧
                      Cont localCert locality observerRead ∧
                        Cont observerRead forward factorRead ∧
                          PkgSig bundle localCert pkg ∧ PkgSig bundle factorRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier localCertLocalityObserver observerForwardFactor factorReadPkg
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
    gapForwardContinuation, _transportContinuationProvenance, localCertPkg⟩ := baseCarrier
  have observerReadUnary : UnaryHistory observerRead :=
    unary_cont_closed localCertUnary localityUnary localCertLocalityObserver
  have factorReadUnary : UnaryHistory factorRead :=
    unary_cont_closed observerReadUnary forwardUnary observerForwardFactor
  exact
    ⟨observedUnary, regularityUnary, gapUnary, forwardUnary, localityUnary,
      localCertUnary, observerReadUnary, factorReadUnary, observedRegularityGap,
      gapForwardContinuation, forwardLocalityLocalCert, localCertLocalityObserver,
      observerForwardFactor, localCertPkg, factorReadPkg⟩

end BEDC.Derived.CausalCommitmentUp
