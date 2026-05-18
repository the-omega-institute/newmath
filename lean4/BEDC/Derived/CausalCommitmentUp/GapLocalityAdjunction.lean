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

theorem CausalCommitmentGapLocalityAdjunction [AskSetup] [PackageSetup]
    {observed regularity gap forward locality transport continuation provenance localCert
      observerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CausalCommitmentForwardGapCarrier observed regularity gap forward locality transport
        continuation provenance localCert bundle pkg ->
      Cont continuation localCert observerRead ->
        PkgSig bundle observerRead pkg ->
          SemanticNameCert
            (fun row : BHist =>
              CausalCommitmentForwardGapCarrier observed regularity gap forward locality
                transport continuation provenance localCert bundle pkg ∧ hsame row gap)
            (fun row : BHist =>
              Cont observed regularity gap ∧ Cont gap forward continuation ∧
                Cont forward locality localCert ∧ hsame row gap)
            (fun row : BHist =>
              PkgSig bundle localCert pkg ∧ PkgSig bundle observerRead pkg ∧ hsame row gap)
            hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier _continuationLocalObserver observerReadPkg
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
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro gap ⟨carrierWitness, hsame_refl gap⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨observedRegularityGap, gapForwardContinuation, forwardLocalityLocalCert,
          source.right⟩
    ledger_sound := by
      intro _row source
      exact ⟨localCertPkg, observerReadPkg, source.right⟩
  }

end BEDC.Derived.CausalCommitmentUp
