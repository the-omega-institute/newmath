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

theorem AuthorizedGeneratorRecursorRealOutputFactorizationLock [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert outputRead auditRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg ->
      Cont output audit outputRead ->
        Cont outputRead continuation auditRead ->
          Cont auditRead localCert realRead ->
            PkgSig bundle realRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row output ∨ hsame row audit ∨ hsame row outputRead ∨
                      hsame row auditRead ∨ hsame row realRead)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle realRead pkg ∧
                      hsame row realRead)
                  hsame ∧
                UnaryHistory output ∧ UnaryHistory audit ∧ UnaryHistory outputRead ∧
                  UnaryHistory auditRead ∧ UnaryHistory realRead ∧
                    hsame transport (append audit continuation) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier outputAuditOutputRead outputContinuationAuditRead auditLocalRealRead realPkg
  rcases carrier with
    ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
      outputUnary, auditUnary, _transportUnary, continuationUnary, _provenanceUnary,
      _boundaryUnary, localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, transportAuditContinuation, provenancePkg⟩
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed outputUnary auditUnary outputAuditOutputRead
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed outputReadUnary continuationUnary outputContinuationAuditRead
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed auditReadUnary localCertUnary auditLocalRealRead
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row output ∨ hsame row audit ∨ hsame row outputRead ∨
            hsame row auditRead ∨ hsame row realRead)
        (fun row : BHist =>
          PkgSig bundle provenance pkg ∧ PkgSig bundle realRead pkg ∧ hsame row realRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro realRead ⟨hsame_refl realRead, realReadUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, realPkg, source.left⟩
    }
  exact
    ⟨cert, outputUnary, auditUnary, outputReadUnary, auditReadUnary, realReadUnary,
      transportAuditContinuation⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
