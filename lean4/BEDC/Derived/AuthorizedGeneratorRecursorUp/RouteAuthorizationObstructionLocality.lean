import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRouteAuthorizationObstructionLocality [AskSetup]
    [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert publicRead obstructionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg →
      Cont continuation provenance publicRead →
        Cont publicRead localCert obstructionRead →
          PkgSig bundle obstructionRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row obstructionRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row signature ∨ hsame row eliminator ∨ hsame row motive ∨
                    hsame row branch ∨ hsame row descent ∨ hsame row output ∨
                      hsame row audit ∨ hsame row publicRead ∨ hsame row obstructionRead)
                (fun row : BHist => hsame row obstructionRead ∧ PkgSig bundle obstructionRead pkg)
                hsame ∧
              UnaryHistory publicRead ∧ UnaryHistory obstructionRead ∧
                Cont continuation provenance publicRead ∧
                  Cont publicRead localCert obstructionRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle obstructionRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier continuationProvenancePublic publicLocalObstruction obstructionPkg
  obtain
    ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
      _outputUnary, _auditUnary, _transportUnary, continuationUnary, provenanceUnary,
      _boundaryUnary, localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, _transportSameAuditContinuation, provenancePkg⟩ :=
      carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed continuationUnary provenanceUnary continuationProvenancePublic
  have obstructionUnary : UnaryHistory obstructionRead :=
    unary_cont_closed publicUnary localCertUnary publicLocalObstruction
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row obstructionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row signature ∨ hsame row eliminator ∨ hsame row motive ∨
              hsame row branch ∨ hsame row descent ∨ hsame row output ∨
                hsame row audit ∨ hsame row publicRead ∨ hsame row obstructionRead)
          (fun row : BHist => hsame row obstructionRead ∧ PkgSig bundle obstructionRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro obstructionRead
          ⟨hsame_refl obstructionRead, obstructionUnary⟩
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
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left)))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, obstructionPkg⟩
    }
  exact
    ⟨cert, publicUnary, obstructionUnary, continuationProvenancePublic, publicLocalObstruction,
      provenancePkg, obstructionPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
