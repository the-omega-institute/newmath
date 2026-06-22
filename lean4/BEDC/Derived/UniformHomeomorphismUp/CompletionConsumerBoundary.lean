import BEDC.Derived.UniformHomeomorphismUp.NameCertObligations

namespace BEDC.Derived.UniformHomeomorphismUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformHomeomorphismCompletionConsumerBoundary [AskSetup] [PackageSetup]
    {source target forward inverse forwardUC inverseUC forwardMod inverseMod compatibility replay
      provenance localName completionRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformHomeomorphismCarrier source target forward inverse forwardUC inverseUC forwardMod
      inverseMod compatibility replay provenance localName bundle pkg ->
      Cont compatibility replay completionRead ->
        Cont completionRead localName consumerRead ->
          PkgSig bundle consumerRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row compatibility ∨ hsame row replay ∨ hsame row completionRead ∨
                    hsame row localName ∨ hsame row consumerRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont compatibility replay completionRead ∧
                    Cont completionRead localName consumerRead ∧
                      PkgSig bundle consumerRead pkg)
                hsame ∧
              UnaryHistory completionRead ∧ UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier completionRoute consumerRoute consumerPkg
  obtain ⟨_sourceUnary, _targetUnary, _forwardUnary, _inverseUnary, _forwardUCUnary,
    _inverseUCUnary, _forwardModUnary, _inverseModUnary, compatibilityUnary, replayUnary,
    _provenanceUnary, localNameUnary, _provenancePkg, _localNamePkg⟩ := carrier
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed compatibilityUnary replayUnary completionRoute
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed completionReadUnary localNameUnary consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compatibility ∨ hsame row replay ∨ hsame row completionRead ∨
              hsame row localName ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont compatibility replay completionRead ∧
              Cont completionRead localName consumerRead ∧ PkgSig bundle consumerRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerReadUnary⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, completionRoute, consumerRoute, consumerPkg⟩
    }
  exact ⟨cert, completionReadUnary, consumerReadUnary⟩

end BEDC.Derived.UniformHomeomorphismUp
