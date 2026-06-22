import BEDC.Derived.UniformHomeomorphismUp.NameCertObligations

namespace BEDC.Derived.UniformHomeomorphismUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformHomeomorphismClassifierBidirectionality [AskSetup] [PackageSetup]
    {source target forward inverse forwardUC inverseUC forwardMod inverseMod compatibility replay
      provenance localName forwardRead inverseRead compatibilityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformHomeomorphismCarrier source target forward inverse forwardUC inverseUC forwardMod
      inverseMod compatibility replay provenance localName bundle pkg ->
      Cont forward forwardUC forwardRead ->
        Cont inverse inverseUC inverseRead ->
          Cont forwardRead inverseRead compatibilityRead ->
            PkgSig bundle compatibilityRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row forward ∨ hsame row inverse ∨ hsame row forwardUC ∨
                        hsame row inverseUC ∨ hsame row forwardRead ∨
                          hsame row inverseRead ∨ hsame row compatibilityRead) ∧
                      UnaryHistory row)
                  (fun row : BHist =>
                    hsame row forward ∨ hsame row inverse ∨ hsame row forwardUC ∨
                      hsame row inverseUC ∨ hsame row forwardRead ∨
                        hsame row inverseRead ∨ hsame row compatibilityRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont forward forwardUC forwardRead ∧
                      Cont inverse inverseUC inverseRead ∧
                        Cont forwardRead inverseRead compatibilityRead ∧
                          PkgSig bundle compatibilityRead pkg)
                  hsame ∧
                UnaryHistory forwardRead ∧ UnaryHistory inverseRead ∧
                  UnaryHistory compatibilityRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier forwardRoute inverseRoute compatibilityRoute compatibilityPkg
  obtain ⟨_sourceUnary, _targetUnary, forwardUnary, inverseUnary, forwardUCUnary,
    inverseUCUnary, _forwardModUnary, _inverseModUnary, _compatibilityUnary,
    _replayUnary, _provenanceUnary, _localNameUnary, _provenancePkg, _localNamePkg⟩ :=
    carrier
  have forwardReadUnary : UnaryHistory forwardRead :=
    unary_cont_closed forwardUnary forwardUCUnary forwardRoute
  have inverseReadUnary : UnaryHistory inverseRead :=
    unary_cont_closed inverseUnary inverseUCUnary inverseRoute
  have compatibilityReadUnary : UnaryHistory compatibilityRead :=
    unary_cont_closed forwardReadUnary inverseReadUnary compatibilityRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row forward ∨ hsame row inverse ∨ hsame row forwardUC ∨
                hsame row inverseUC ∨ hsame row forwardRead ∨ hsame row inverseRead ∨
                  hsame row compatibilityRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row forward ∨ hsame row inverse ∨ hsame row forwardUC ∨
              hsame row inverseUC ∨ hsame row forwardRead ∨ hsame row inverseRead ∨
                hsame row compatibilityRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont forward forwardUC forwardRead ∧
              Cont inverse inverseUC inverseRead ∧
                Cont forwardRead inverseRead compatibilityRead ∧
                  PkgSig bundle compatibilityRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro compatibilityRead
            ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (hsame_refl compatibilityRead)))))),
              compatibilityReadUnary⟩
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
          constructor
          · cases source.left with
            | inl sameForward =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameForward)
            | inr rest =>
                cases rest with
                | inl sameInverse =>
                    exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameInverse))
                | inr rest =>
                    cases rest with
                    | inl sameForwardUC =>
                        exact Or.inr (Or.inr
                          (Or.inl (hsame_trans (hsame_symm sameRows) sameForwardUC)))
                    | inr rest =>
                        cases rest with
                        | inl sameInverseUC =>
                            exact Or.inr (Or.inr (Or.inr
                              (Or.inl (hsame_trans (hsame_symm sameRows) sameInverseUC))))
                        | inr rest =>
                            cases rest with
                            | inl sameForwardRead =>
                                exact Or.inr (Or.inr (Or.inr (Or.inr
                                  (Or.inl
                                    (hsame_trans (hsame_symm sameRows) sameForwardRead)))))
                            | inr rest =>
                                cases rest with
                                | inl sameInverseRead =>
                                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                      (Or.inl
                                        (hsame_trans
                                          (hsame_symm sameRows) sameInverseRead))))))
                                | inr sameCompatibilityRead =>
                                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                      (Or.inr
                                        (hsame_trans
                                          (hsame_symm sameRows) sameCompatibilityRead))))))
          · exact unary_transport source.right sameRows
      }
      pattern_sound := by
        intro _row source
        exact source.left
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, forwardRoute, inverseRoute, compatibilityRoute,
            compatibilityPkg⟩
    }
  exact ⟨cert, forwardReadUnary, inverseReadUnary, compatibilityReadUnary⟩

end BEDC.Derived.UniformHomeomorphismUp
