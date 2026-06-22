import BEDC.Derived.UniformHomeomorphismUp.NameCertObligations

namespace BEDC.Derived.UniformHomeomorphismUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformHomeomorphismPublicExport [AskSetup] [PackageSetup]
    {source target forward inverse forwardUC inverseUC forwardMod inverseMod compatibility
      replay provenance localName publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformHomeomorphismCarrier source target forward inverse forwardUC inverseUC forwardMod
        inverseMod compatibility replay provenance localName bundle pkg ->
      Cont compatibility localName publicRead ->
        PkgSig bundle publicRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row source ∨ hsame row target ∨ hsame row forward ∨
                  hsame row inverse ∨ hsame row forwardUC ∨ hsame row inverseUC ∨
                    hsame row forwardMod ∨ hsame row inverseMod ∨
                      hsame row compatibility ∨ hsame row replay ∨
                        hsame row provenance ∨ hsame row localName ∨
                          hsame row publicRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont compatibility localName publicRead ∧
                  PkgSig bundle publicRead pkg)
              hsame ∧
            UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier publicRoute publicPkg
  obtain ⟨_sourceUnary, _targetUnary, _forwardUnary, _inverseUnary, _forwardUCUnary,
    _inverseUCUnary, _forwardModUnary, _inverseModUnary, compatibilityUnary, _replayUnary,
    _provenanceUnary, localNameUnary, _provenancePkg, _localNamePkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed compatibilityUnary localNameUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row target ∨ hsame row forward ∨
              hsame row inverse ∨ hsame row forwardUC ∨ hsame row inverseUC ∨
                hsame row forwardMod ∨ hsame row inverseMod ∨ hsame row compatibility ∨
                  hsame row replay ∨ hsame row provenance ∨ hsame row localName ∨
                    hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont compatibility localName publicRead ∧
              PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, publicRoute, publicPkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.UniformHomeomorphismUp
