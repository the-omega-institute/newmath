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

theorem AuthorizedGeneratorRecursorLedgerProvenanceClosure [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert outputRead provenanceRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg ->
      Cont output audit outputRead ->
        Cont outputRead provenance provenanceRead ->
          Cont provenanceRead boundary boundaryRead ->
            PkgSig bundle boundaryRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch
                      descent output audit transport continuation provenance boundary
                      localCert bundle pkg ∧ hsame row boundaryRead)
                  (fun row : BHist =>
                    hsame row outputRead ∨ hsame row provenanceRead ∨
                      hsame row boundaryRead)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle boundaryRead pkg ∧
                      hsame row boundaryRead)
                  hsame ∧
                UnaryHistory outputRead ∧ UnaryHistory provenanceRead ∧
                  UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier outputAuditRead outputProvenanceRead provenanceBoundaryRead boundaryPkg
  have carrierPacket :
      AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output
        audit transport continuation provenance boundary localCert bundle pkg :=
    carrier
  obtain ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
    outputUnary, auditUnary, _transportUnary, _continuationUnary, provenanceUnary,
    boundaryUnary, _localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
    _descentOutputAudit, _transportSame, provenancePkg⟩ := carrier
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed outputUnary auditUnary outputAuditRead
  have provenanceReadUnary : UnaryHistory provenanceRead :=
    unary_cont_closed outputReadUnary provenanceUnary outputProvenanceRead
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed provenanceReadUnary boundaryUnary provenanceBoundaryRead
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent
              output audit transport continuation provenance boundary localCert bundle pkg ∧
              hsame row boundaryRead)
          (fun row : BHist =>
            hsame row outputRead ∨ hsame row provenanceRead ∨ hsame row boundaryRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle boundaryRead pkg ∧
              hsame row boundaryRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro boundaryRead ⟨carrierPacket, hsame_refl boundaryRead⟩
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
        exact Or.inr (Or.inr source.right)
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, boundaryPkg, source.right⟩
    }
  exact ⟨cert, outputReadUnary, provenanceReadUnary, boundaryReadUnary⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
