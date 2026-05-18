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

theorem AuthorizedGeneratorRecursorRegSeqRatRealSealOutputExhaustion [AskSetup]
    [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert regseqRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg ->
      Cont output audit regseqRead ->
        Cont regseqRead continuation realRead ->
          PkgSig bundle boundary pkg ->
            PkgSig bundle realRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row output ∨ hsame row regseqRead ∨ hsame row realRead ∨
                      hsame row boundary)
                  (fun row : BHist =>
                    PkgSig bundle realRead pkg ∧ PkgSig bundle boundary pkg ∧
                      hsame row realRead)
                  hsame ∧
                UnaryHistory regseqRead ∧ UnaryHistory realRead ∧
                  hsame transport (append audit continuation) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro carrier outputAuditRegSeq regseqContinuationReal boundaryPkg realPkg
  rcases carrier with
    ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
      outputUnary, auditUnary, _transportUnary, continuationUnary, _provenanceUnary,
      _boundaryUnary, _localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, transportAuditContinuation, _provenancePkg⟩
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed outputUnary auditUnary outputAuditRegSeq
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regseqUnary continuationUnary regseqContinuationReal
  have sourceReal :
      (fun row : BHist => hsame row realRead ∧ UnaryHistory row) realRead := by
    exact ⟨hsame_refl realRead, realUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row output ∨ hsame row regseqRead ∨ hsame row realRead ∨
              hsame row boundary)
          (fun row : BHist =>
            PkgSig bundle realRead pkg ∧ PkgSig bundle boundary pkg ∧ hsame row realRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro realRead sourceReal
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
        exact Or.inr (Or.inr (Or.inl source.left))
      ledger_sound := by
        intro _row source
        exact ⟨realPkg, boundaryPkg, source.left⟩
    }
  exact ⟨cert, regseqUnary, realUnary, transportAuditContinuation⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
