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

theorem CausalCommitmentForwardGapNameCertExport [AskSetup] [PackageSetup]
    {observed regularity gap forward locality transport continuation provenance localCert
      observerRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CausalCommitmentForwardGapCarrier observed regularity gap forward locality transport
        continuation provenance localCert bundle pkg ->
      Cont continuation localCert observerRead ->
        Cont observerRead locality ledgerRead ->
          PkgSig bundle ledgerRead pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  CausalCommitmentForwardGapCarrier observed regularity gap forward locality
                    transport continuation provenance localCert bundle pkg ∧
                    hsame row localCert)
                (fun row : BHist =>
                  Cont observed regularity gap ∧ Cont gap forward continuation ∧
                    Cont forward locality localCert ∧
                      Cont continuation localCert observerRead ∧
                        Cont observerRead locality ledgerRead ∧ hsame row localCert)
                (fun row : BHist =>
                  PkgSig bundle localCert pkg ∧ PkgSig bundle ledgerRead pkg ∧
                    hsame row localCert)
                hsame ∧
              UnaryHistory observerRead ∧ UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier continuationLocalCertObserver observerLocalityLedger ledgerReadPkg
  have carrierWitness :
      CausalCommitmentForwardGapCarrier observed regularity gap forward locality transport
        continuation provenance localCert bundle pkg :=
    carrier
  have baseCarrier :
      CausalCommitmentCarrier observed regularity gap forward transport continuation
        provenance localCert bundle pkg :=
    carrier.left
  have localityUnary : UnaryHistory locality :=
    carrier.right.left
  have forwardLocalityLocalCert : Cont forward locality localCert :=
    carrier.right.right
  obtain ⟨_observedUnary, _regularityUnary, _gapUnary, _forwardUnary, _transportUnary,
    continuationUnary, _provenanceUnary, localCertUnary, observedRegularityGap,
    gapForwardContinuation, _transportContinuationProvenance, localCertPkg⟩ := baseCarrier
  have observerReadUnary : UnaryHistory observerRead :=
    unary_cont_closed continuationUnary localCertUnary continuationLocalCertObserver
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed observerReadUnary localityUnary observerLocalityLedger
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            CausalCommitmentForwardGapCarrier observed regularity gap forward locality
              transport continuation provenance localCert bundle pkg ∧ hsame row localCert)
          (fun row : BHist =>
            Cont observed regularity gap ∧ Cont gap forward continuation ∧
              Cont forward locality localCert ∧ Cont continuation localCert observerRead ∧
                Cont observerRead locality ledgerRead ∧ hsame row localCert)
          (fun row : BHist =>
            PkgSig bundle localCert pkg ∧ PkgSig bundle ledgerRead pkg ∧
              hsame row localCert)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localCert ⟨carrierWitness, hsame_refl localCert⟩
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
          continuationLocalCertObserver, observerLocalityLedger, source.right⟩
    ledger_sound := by
      intro _row source
      exact ⟨localCertPkg, ledgerReadPkg, source.right⟩
  }
  exact ⟨cert, observerReadUnary, ledgerReadUnary⟩

theorem CausalCommitmentStandardBridgeSurface [AskSetup] [PackageSetup]
    {observed regularity gap forward locality transport continuation provenance localCert
      observerRead ledgerRead bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CausalCommitmentForwardGapCarrier observed regularity gap forward locality transport
        continuation provenance localCert bundle pkg →
      Cont continuation localCert observerRead →
        Cont observerRead locality ledgerRead →
          Cont ledgerRead provenance bridgeRead →
            PkgSig bundle bridgeRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row observed ∨ hsame row regularity ∨ hsame row gap ∨
                      hsame row forward ∨ hsame row locality ∨ hsame row ledgerRead ∨
                        hsame row bridgeRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont observed regularity gap ∧
                      Cont gap forward continuation ∧ Cont forward locality localCert ∧
                        Cont continuation localCert observerRead ∧
                          Cont observerRead locality ledgerRead ∧
                            Cont ledgerRead provenance bridgeRead ∧
                              PkgSig bundle bridgeRead pkg)
                  hsame ∧ UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier continuationLocalCertObserver observerLocalityLedger ledgerProvenanceBridge
    bridgePkg
  have baseCarrier :
      CausalCommitmentCarrier observed regularity gap forward transport continuation provenance
        localCert bundle pkg :=
    carrier.left
  have localityUnary : UnaryHistory locality :=
    carrier.right.left
  have forwardLocalityLocalCert : Cont forward locality localCert :=
    carrier.right.right
  obtain ⟨observedUnary, regularityUnary, gapUnary, forwardUnary, _transportUnary,
    continuationUnary, provenanceUnary, localCertUnary, observedRegularityGap,
    gapForwardContinuation, _transportContinuationProvenance, _localCertPkg⟩ := baseCarrier
  have observerUnary : UnaryHistory observerRead :=
    unary_cont_closed continuationUnary localCertUnary continuationLocalCertObserver
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed observerUnary localityUnary observerLocalityLedger
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed ledgerUnary provenanceUnary ledgerProvenanceBridge
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row observed ∨ hsame row regularity ∨ hsame row gap ∨
              hsame row forward ∨ hsame row locality ∨ hsame row ledgerRead ∨
                hsame row bridgeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont observed regularity gap ∧
              Cont gap forward continuation ∧ Cont forward locality localCert ∧
                Cont continuation localCert observerRead ∧
                  Cont observerRead locality ledgerRead ∧
                    Cont ledgerRead provenance bridgeRead ∧ PkgSig bundle bridgeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bridgeRead ⟨hsame_refl bridgeRead, bridgeUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, observedRegularityGap, gapForwardContinuation,
          forwardLocalityLocalCert, continuationLocalCertObserver, observerLocalityLedger,
            ledgerProvenanceBridge, bridgePkg⟩
  }
  exact ⟨cert, bridgeUnary⟩

end BEDC.Derived.CausalCommitmentUp
