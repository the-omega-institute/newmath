import BEDC.Derived.CausalCommitmentUp

namespace BEDC.Derived.CausalCommitmentUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem CausalCommitmentLocalityConsumerExactness [AskSetup] [PackageSetup]
    {observed regularity gap forward locality transport continuation provenance localCert
      localityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CausalCommitmentForwardGapCarrier observed regularity gap forward locality transport
        continuation provenance localCert bundle pkg ->
      Cont locality localCert localityRead ->
        PkgSig bundle localityRead pkg ->
          UnaryHistory observed ∧ UnaryHistory regularity ∧ UnaryHistory gap ∧
            UnaryHistory forward ∧ UnaryHistory locality ∧ UnaryHistory localCert ∧
              UnaryHistory localityRead ∧ Cont observed regularity gap ∧
                Cont gap forward continuation ∧ Cont forward locality localCert ∧
                  Cont locality localCert localityRead ∧ PkgSig bundle localCert pkg ∧
                    PkgSig bundle localityRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier localityLocalCertRead localityReadPkg
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
  have localityReadUnary : UnaryHistory localityRead :=
    unary_cont_closed localityUnary localCertUnary localityLocalCertRead
  exact
    ⟨observedUnary, regularityUnary, gapUnary, forwardUnary, localityUnary,
      localCertUnary, localityReadUnary, observedRegularityGap, gapForwardContinuation,
      forwardLocalityLocalCert, localityLocalCertRead, localCertPkg, localityReadPkg⟩

theorem CausalCommitmentNameCertLedger [AskSetup] [PackageSetup]
    {observed regularity gap forward locality transport continuation provenance localCert
      ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CausalCommitmentForwardGapCarrier observed regularity gap forward locality transport
        continuation provenance localCert bundle pkg ->
      Cont locality localCert ledgerRead ->
        PkgSig bundle ledgerRead pkg ->
          SemanticNameCert
            (fun row : BHist =>
              CausalCommitmentForwardGapCarrier observed regularity gap forward locality
                transport continuation provenance localCert bundle pkg ∧ hsame row localCert)
            (fun row : BHist =>
              Cont observed regularity gap ∧ Cont gap forward continuation ∧
                Cont forward locality localCert ∧ Cont locality localCert ledgerRead ∧
                  hsame row localCert)
            (fun row : BHist =>
              PkgSig bundle localCert pkg ∧ PkgSig bundle ledgerRead pkg ∧
                hsame row localCert)
            hsame := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier localityLocalCertLedger ledgerReadPkg
  have carrierWitness := carrier
  have baseCarrier :
      CausalCommitmentCarrier observed regularity gap forward transport continuation
        provenance localCert bundle pkg :=
    carrier.left
  have forwardLocalityLocalCert : Cont forward locality localCert :=
    carrier.right.right
  obtain ⟨_observedUnary, _regularityUnary, _gapUnary, _forwardUnary, _transportUnary,
    _continuationUnary, _provenanceUnary, _localCertUnary, observedRegularityGap,
    gapForwardContinuation, _transportContinuationProvenance, localCertPkg⟩ := baseCarrier
  constructor
  · constructor
    · exact Exists.intro localCert ⟨carrierWitness, hsame_refl localCert⟩
    · intro row _source
      exact hsame_refl row
    · intro _row _row' sameRows
      exact hsame_symm sameRows
    · intro _row _row' _row'' sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro _row _row' sameRows source
      exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
  · intro _row source
    exact
      ⟨observedRegularityGap, gapForwardContinuation, forwardLocalityLocalCert,
        localityLocalCertLedger, source.right⟩
  · intro _row source
    exact ⟨localCertPkg, ledgerReadPkg, source.right⟩

end BEDC.Derived.CausalCommitmentUp
