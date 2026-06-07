import BEDC.Derived.MetacicNormalizationAuditUp

namespace BEDC.Derived.MetacicNormalizationAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicNormalizationAuditCandidateFrontierRefusal [AskSetup] [PackageSetup]
    {kernel normalizer frontier sn confluence audit ledger transport replay provenance localName
      closedRead refusalRead named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicNormalizationAuditUp kernel normalizer frontier sn confluence audit ledger transport
        replay provenance localName bundle pkg ->
      Cont frontier sn audit ->
        Cont audit replay closedRead ->
          Cont closedRead localName refusalRead ->
            Cont refusalRead provenance named ->
              PkgSig bundle named pkg ->
                SemanticNameCert
                  (fun row : BHist => hsame row named ∧ UnaryHistory row ∧
                    PkgSig bundle row pkg)
                  (fun row : BHist =>
                    hsame row frontier ∨ hsame row sn ∨ hsame row audit ∨
                      hsame row closedRead ∨ hsame row refusalRead ∨
                        hsame row localName ∨ hsame row provenance ∨ hsame row named)
                  (fun row : BHist =>
                    hsame row named ∧ Cont frontier sn audit ∧
                      Cont audit replay closedRead ∧ Cont closedRead localName refusalRead ∧
                        PkgSig bundle provenance pkg)
                  hsame ∧ UnaryHistory audit ∧ UnaryHistory closedRead ∧
                    UnaryHistory refusalRead ∧ UnaryHistory named := by
  -- BEDC touchpoint anchor: MetacicNormalizationAuditUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier frontierSnAudit auditReplayClosed closedLocalRefusal refusalProvenanceNamed
    namedPkg
  obtain ⟨_kernelUnary, _normalizerUnary, frontierUnary, snUnary, _confluenceUnary,
    _auditUnary, _ledgerUnary, _transportUnary, replayUnary, provenanceUnary,
    localNameUnary, _kernelNormalizerFrontier, _frontierSnAudit, _confluenceAuditLedger,
    _transportReplaySame, provenancePkg, _localNamePkg⟩ := carrier
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed frontierUnary snUnary frontierSnAudit
  have closedUnary : UnaryHistory closedRead :=
    unary_cont_closed auditUnary replayUnary auditReplayClosed
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed closedUnary localNameUnary closedLocalRefusal
  have namedUnary : UnaryHistory named :=
    unary_cont_closed refusalUnary provenanceUnary refusalProvenanceNamed
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row named ∧ UnaryHistory row ∧
          PkgSig bundle row pkg)
        (fun row : BHist =>
          hsame row frontier ∨ hsame row sn ∨ hsame row audit ∨ hsame row closedRead ∨
            hsame row refusalRead ∨ hsame row localName ∨ hsame row provenance ∨
              hsame row named)
        (fun row : BHist =>
          hsame row named ∧ Cont frontier sn audit ∧ Cont audit replay closedRead ∧
            Cont closedRead localName refusalRead ∧ PkgSig bundle provenance pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro named
        ⟨hsame_refl named, namedUnary, namedPkg⟩
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
      exact ⟨sourceRow.left, frontierSnAudit, auditReplayClosed, closedLocalRefusal,
        provenancePkg⟩
  }
  exact ⟨cert, auditUnary, closedUnary, refusalUnary, namedUnary⟩

end BEDC.Derived.MetacicNormalizationAuditUp
