import BEDC.Derived.CausalCommitmentUp

namespace BEDC.Derived.CausalCommitmentUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem CausalCommitmentObservedRegularityNonchoice [AskSetup] [PackageSetup]
    {observed regularity gap forward locality transport continuation provenance
      localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CausalCommitmentForwardGapCarrier observed regularity gap forward locality transport
        continuation provenance localCert bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          CausalCommitmentForwardGapCarrier observed regularity gap forward locality
            transport continuation provenance localCert bundle pkg ∧ hsame row observed)
        (fun row : BHist =>
          hsame row observed ∧ Cont observed regularity gap ∧
            Cont gap forward continuation ∧ Cont forward locality localCert)
        (fun row : BHist => hsame row observed ∧ PkgSig bundle localCert pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame
  intro carrier
  have carrierWitness := carrier
  have baseCarrier :
      CausalCommitmentCarrier observed regularity gap forward transport continuation
        provenance localCert bundle pkg :=
    carrier.left
  have forwardLocalityName : Cont forward locality localCert :=
    carrier.right.right
  obtain ⟨_observedUnary, _regularityUnary, _gapUnary, _forwardUnary, _transportUnary,
    _continuationUnary, _provenanceUnary, _localCertUnary, observedRegularityGap,
    gapForwardContinuation, _transportContinuationProvenance, localCertPkg⟩ := baseCarrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro observed (And.intro carrierWitness (hsame_refl observed))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        exact And.intro sourceRow.left
          (hsame_trans (hsame_symm sameRows) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, observedRegularityGap, gapForwardContinuation,
          forwardLocalityName⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, localCertPkg⟩
  }

end BEDC.Derived.CausalCommitmentUp
