import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorCarrier_route_authorization [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg ->
      Cont continuation provenance publicRead ->
        PkgSig bundle publicRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent
                    output audit transport continuation provenance boundary localCert bundle pkg ∧
                  hsame row publicRead)
              (fun row : BHist =>
                hsame row signature ∨ hsame row eliminator ∨ hsame row motive ∨
                  hsame row branch ∨ hsame row descent ∨ hsame row output ∨
                    hsame row audit ∨ hsame row publicRead)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg ∧
                  hsame row publicRead)
              hsame ∧
            UnaryHistory publicRead ∧
            Cont continuation provenance publicRead ∧
            PkgSig bundle provenance pkg ∧
            PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier continuationProvenancePublic publicPkg
  have carrierPacket :
      AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg :=
    carrier
  obtain ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary,
    _descentUnary, _outputUnary, _auditUnary, _transportUnary, continuationUnary,
    provenanceUnary, _boundaryUnary, _localCertUnary, _signatureEliminatorMotive,
    _motiveBranchDescent, _descentOutputAudit, _transportSameAuditContinuation,
    provenancePkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed continuationUnary provenanceUnary continuationProvenancePublic
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output
                audit transport continuation provenance boundary localCert bundle pkg ∧
              hsame row publicRead)
          (fun row : BHist =>
            hsame row signature ∨ hsame row eliminator ∨ hsame row motive ∨
              hsame row branch ∨ hsame row descent ∨ hsame row output ∨
                hsame row audit ∨ hsame row publicRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg ∧
              hsame row publicRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro publicRead
          ⟨carrierPacket, hsame_refl publicRead⟩
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
          exact ⟨sourceRow.left, hsame_trans (hsame_symm sameRows) sourceRow.right⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.right))))))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨provenancePkg, publicPkg, sourceRow.right⟩
    }
  exact ⟨cert, publicUnary, continuationProvenancePublic, provenancePkg, publicPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
