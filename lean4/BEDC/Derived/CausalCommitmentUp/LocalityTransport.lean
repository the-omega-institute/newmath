import BEDC.Derived.CausalCommitmentUp

namespace BEDC.Derived.CausalCommitmentUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem CausalCommitmentLocalityTransport [AskSetup] [PackageSetup]
    {observed regularity gap forward locality transport continuation provenance localCert
      localityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CausalCommitmentForwardGapCarrier observed regularity gap forward locality transport
        continuation provenance localCert bundle pkg ->
      Cont locality continuation localityRead ->
      PkgSig bundle localityRead pkg ->
        UnaryHistory observed ∧ UnaryHistory regularity ∧ UnaryHistory gap ∧
          UnaryHistory forward ∧ UnaryHistory locality ∧ UnaryHistory continuation ∧
            UnaryHistory localityRead ∧ Cont observed regularity gap ∧
              Cont gap forward continuation ∧ Cont forward locality localCert ∧
                Cont locality continuation localityRead ∧ PkgSig bundle localCert pkg ∧
                  PkgSig bundle localityRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier localityContinuationRead localityReadPkg
  have baseCarrier :
      CausalCommitmentCarrier observed regularity gap forward transport continuation
        provenance localCert bundle pkg :=
    carrier.left
  have localityUnary : UnaryHistory locality :=
    carrier.right.left
  have forwardLocalityLocalCert : Cont forward locality localCert :=
    carrier.right.right
  obtain ⟨observedUnary, regularityUnary, gapUnary, forwardUnary, _transportUnary,
    continuationUnary, _provenanceUnary, _localCertUnary, observedRegularityGap,
    gapForwardContinuation, _transportContinuationProvenance, localCertPkg⟩ := baseCarrier
  have localityReadUnary : UnaryHistory localityRead :=
    unary_cont_closed localityUnary continuationUnary localityContinuationRead
  exact
    ⟨observedUnary, regularityUnary, gapUnary, forwardUnary, localityUnary,
      continuationUnary, localityReadUnary, observedRegularityGap, gapForwardContinuation,
      forwardLocalityLocalCert, localityContinuationRead, localCertPkg, localityReadPkg⟩

end BEDC.Derived.CausalCommitmentUp
