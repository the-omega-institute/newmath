import BEDC.Derived.MetacicNormalizationAuditUp

namespace BEDC.Derived.MetacicNormalizationAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicNormalizationAuditResidualSubstitutionCompatibility [AskSetup] [PackageSetup]
    {kernel normalizer frontier sn confluence audit ledger transport replay provenance localName
      residualRead spentFuel substitutionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicNormalizationAuditUp kernel normalizer frontier sn confluence audit ledger transport
        replay provenance localName bundle pkg →
      Cont audit replay residualRead →
        Cont residualRead sn spentFuel →
          Cont spentFuel frontier substitutionRead →
            PkgSig bundle substitutionRead pkg →
              SemanticNameCert
                (fun row : BHist => hsame row substitutionRead ∧ UnaryHistory row ∧
                  PkgSig bundle row pkg)
                (fun row : BHist =>
                  hsame row frontier ∨ hsame row sn ∨ hsame row audit ∨
                    hsame row replay ∨ hsame row residualRead ∨ hsame row spentFuel ∨
                      hsame row substitutionRead ∨ hsame row provenance)
                (fun row : BHist =>
                  hsame row substitutionRead ∧ Cont audit replay residualRead ∧
                    Cont residualRead sn spentFuel ∧
                      Cont spentFuel frontier substitutionRead ∧
                        PkgSig bundle provenance pkg)
                hsame ∧ UnaryHistory residualRead ∧ UnaryHistory spentFuel ∧
                  UnaryHistory substitutionRead := by
  -- BEDC touchpoint anchor: MetacicNormalizationAuditUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier auditReplayResidual residualSnSpent spentFrontierSubstitution substitutionPkg
  obtain ⟨_kernelUnary, _normalizerUnary, frontierUnary, snUnary, _confluenceUnary,
    auditUnary, _ledgerUnary, _transportUnary, replayUnary, provenanceUnary,
    _localNameUnary, _kernelNormalizerFrontier, _frontierSnAudit, _confluenceAuditLedger,
    _transportReplaySame, provenancePkg, _localNamePkg⟩ := carrier
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed auditUnary replayUnary auditReplayResidual
  have spentUnary : UnaryHistory spentFuel :=
    unary_cont_closed residualUnary snUnary residualSnSpent
  have substitutionUnary : UnaryHistory substitutionRead :=
    unary_cont_closed spentUnary frontierUnary spentFrontierSubstitution
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row substitutionRead ∧ UnaryHistory row ∧
          PkgSig bundle row pkg)
        (fun row : BHist =>
          hsame row frontier ∨ hsame row sn ∨ hsame row audit ∨ hsame row replay ∨
            hsame row residualRead ∨ hsame row spentFuel ∨
              hsame row substitutionRead ∨ hsame row provenance)
        (fun row : BHist =>
          hsame row substitutionRead ∧ Cont audit replay residualRead ∧
            Cont residualRead sn spentFuel ∧ Cont spentFuel frontier substitutionRead ∧
              PkgSig bundle provenance pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro substitutionRead
        ⟨hsame_refl substitutionRead, substitutionUnary, substitutionPkg⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sourceRow.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.left, auditReplayResidual, residualSnSpent, spentFrontierSubstitution,
          provenancePkg⟩
  }
  exact ⟨cert, residualUnary, spentUnary, substitutionUnary⟩

end BEDC.Derived.MetacicNormalizationAuditUp
