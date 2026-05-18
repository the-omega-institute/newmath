import BEDC.Derived.CausalCommitmentUp

namespace BEDC.Derived.CausalCommitmentUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig

theorem CausalCommitmentCarrier_ledger_exactness [AskSetup] [PackageSetup]
    {observed regularity gap forward locality transport continuation provenance localCert
      routeRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CausalCommitmentForwardGapCarrier observed regularity gap forward locality transport
        continuation provenance localCert bundle pkg ->
      Cont continuation localCert routeRead ->
        Cont routeRead locality ledgerRead ->
          PkgSig bundle ledgerRead pkg ->
            SemanticNameCert
              (fun row : BHist =>
                CausalCommitmentForwardGapCarrier observed regularity gap forward locality
                  transport continuation provenance localCert bundle pkg ∧ hsame row ledgerRead)
              (fun row : BHist =>
                Cont observed regularity gap ∧ Cont gap forward continuation ∧
                  Cont forward locality localCert ∧ Cont continuation localCert routeRead ∧
                    Cont routeRead locality ledgerRead ∧ hsame row ledgerRead)
              (fun row : BHist =>
                PkgSig bundle localCert pkg ∧ PkgSig bundle ledgerRead pkg ∧
                  hsame row ledgerRead)
              hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier continuationLocalCertRoute routeLocalityLedger ledgerReadPkg
  have carrierWitness :
      CausalCommitmentForwardGapCarrier observed regularity gap forward locality transport
        continuation provenance localCert bundle pkg :=
    carrier
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
    · exact Exists.intro ledgerRead ⟨carrierWitness, hsame_refl ledgerRead⟩
    · intro row _source
      exact hsame_refl row
    · intro _row _other sameRows
      exact hsame_symm sameRows
    · intro _row _middle _other sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro _row _other sameRows source
      exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
  · intro _row source
    exact
      ⟨observedRegularityGap, gapForwardContinuation, forwardLocalityLocalCert,
        continuationLocalCertRoute, routeLocalityLedger, source.right⟩
  · intro _row source
    exact ⟨localCertPkg, ledgerReadPkg, source.right⟩

end BEDC.Derived.CausalCommitmentUp
