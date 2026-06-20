import BEDC.Derived.MetacicNormalizationAuditUp

namespace BEDC.Derived.MetacicNormalizationAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicNormalizationAuditPublicCandidateConfluenceRefusal [AskSetup] [PackageSetup]
    {kernel normalizer frontier sn confluence audit ledger transport replay provenance localName
      publicRead confluenceRead refusedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicNormalizationAuditUp kernel normalizer frontier sn confluence audit ledger transport
        replay provenance localName bundle pkg ->
      Cont audit replay publicRead ->
        Cont confluence ledger confluenceRead ->
          Cont publicRead confluenceRead refusedRead ->
            PkgSig bundle refusedRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row refusedRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                  (fun row : BHist =>
                    hsame row frontier ∨ hsame row sn ∨ hsame row audit ∨
                      hsame row confluence ∨ hsame row ledger ∨ hsame row publicRead ∨
                        hsame row confluenceRead ∨ hsame row refusedRead)
                  (fun row : BHist =>
                    hsame row refusedRead ∧ Cont audit replay publicRead ∧
                      Cont confluence ledger confluenceRead ∧
                        Cont publicRead confluenceRead refusedRead ∧
                          PkgSig bundle provenance pkg)
                  hsame ∧ UnaryHistory publicRead ∧ UnaryHistory confluenceRead ∧
                UnaryHistory refusedRead := by
  -- BEDC touchpoint anchor: MetacicNormalizationAuditUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier auditReplayPublic confluenceLedgerRead publicConfluenceRefused refusedPkg
  obtain ⟨_kernelUnary, _normalizerUnary, _frontierUnary, _snUnary, confluenceUnary,
    auditUnary, ledgerUnary, _transportUnary, replayUnary, _provenanceUnary,
    _localNameUnary, _kernelNormalizerFrontier, _frontierSnAudit, _confluenceAuditLedger,
    _transportReplaySame, provenancePkg, _localNamePkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed auditUnary replayUnary auditReplayPublic
  have confluenceReadUnary : UnaryHistory confluenceRead :=
    unary_cont_closed confluenceUnary ledgerUnary confluenceLedgerRead
  have refusedUnary : UnaryHistory refusedRead :=
    unary_cont_closed publicUnary confluenceReadUnary publicConfluenceRefused
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row refusedRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row frontier ∨ hsame row sn ∨ hsame row audit ∨
              hsame row confluence ∨ hsame row ledger ∨ hsame row publicRead ∨
                hsame row confluenceRead ∨ hsame row refusedRead)
          (fun row : BHist =>
            hsame row refusedRead ∧ Cont audit replay publicRead ∧
              Cont confluence ledger confluenceRead ∧
                Cont publicRead confluenceRead refusedRead ∧
                  PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refusedRead
        ⟨hsame_refl refusedRead, refusedUnary, refusedPkg⟩
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
        intro _row _other sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr sourceRow.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.left, auditReplayPublic, confluenceLedgerRead, publicConfluenceRefused,
          provenancePkg⟩
  }
  exact ⟨cert, publicUnary, confluenceReadUnary, refusedUnary⟩

end BEDC.Derived.MetacicNormalizationAuditUp
