import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier
import BEDC.FKernel.NameCert

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorHiddenGeneratorExclusion [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert branchRead auditRead outputRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg →
      Cont branch continuation branchRead →
        Cont audit boundary auditRead →
          Cont output audit outputRead →
            PkgSig bundle outputRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row outputRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row signature ∨ hsame row eliminator ∨ hsame row motive ∨
                      hsame row branch ∨ hsame row descent ∨ hsame row output ∨
                        hsame row audit ∨ hsame row outputRead)
                  (fun row : BHist => hsame row outputRead ∧ PkgSig bundle outputRead pkg)
                  hsame ∧
                UnaryHistory branchRead ∧ UnaryHistory auditRead ∧ UnaryHistory outputRead ∧
                  Cont signature eliminator motive ∧ Cont motive branch descent ∧
                    Cont descent output audit ∧ hsame transport (append audit continuation) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier branchContinuationRead auditBoundaryRead outputAuditRead outputReadPkg
  obtain ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, branchUnary, _descentUnary,
    outputUnary, auditUnary, _transportUnary, continuationUnary, _provenanceUnary,
    boundaryUnary, _localCertUnary, signatureEliminatorMotive, motiveBranchDescent,
    descentOutputAudit, transportAuditContinuation, _provenancePkg⟩ := carrier
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed branchUnary continuationUnary branchContinuationRead
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed auditUnary boundaryUnary auditBoundaryRead
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed outputUnary auditUnary outputAuditRead
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row outputRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row signature ∨ hsame row eliminator ∨ hsame row motive ∨
            hsame row branch ∨ hsame row descent ∨ hsame row output ∨ hsame row audit ∨
              hsame row outputRead)
        (fun row : BHist => hsame row outputRead ∧ PkgSig bundle outputRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro outputRead (And.intro (hsame_refl outputRead) outputReadUnary)
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
        intro row row' sameRows sourceRow
        exact
          And.intro
            (hsame_trans (hsame_symm sameRows) sourceRow.left)
            (unary_transport sourceRow.right sameRows)
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact And.intro sourceRow.left outputReadPkg
  }
  exact
    ⟨cert, branchReadUnary, auditReadUnary, outputReadUnary, signatureEliminatorMotive,
      motiveBranchDescent, descentOutputAudit, transportAuditContinuation⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
