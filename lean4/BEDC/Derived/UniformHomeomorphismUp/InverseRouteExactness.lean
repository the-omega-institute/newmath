import BEDC.Derived.UniformHomeomorphismUp.NameCertObligations

namespace BEDC.Derived.UniformHomeomorphismUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformHomeomorphismCarrier_inverse_route_exactness [AskSetup] [PackageSetup]
    {source target forward inverse forwardUC inverseUC forwardMod inverseMod compatibility replay
      provenance localName forwardRead inverseRead compatibilityRead exactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformHomeomorphismCarrier source target forward inverse forwardUC inverseUC forwardMod
      inverseMod compatibility replay provenance localName bundle pkg ->
      Cont forward forwardUC forwardRead ->
        Cont inverse inverseUC inverseRead ->
          Cont forwardRead inverseRead compatibilityRead ->
            Cont compatibilityRead compatibility exactRead ->
              PkgSig bundle exactRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row exactRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row forward ∨ hsame row inverse ∨ hsame row forwardUC ∨
                        hsame row inverseUC ∨ hsame row forwardRead ∨
                          hsame row inverseRead ∨ hsame row compatibilityRead ∨
                            hsame row exactRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont forward forwardUC forwardRead ∧
                        Cont inverse inverseUC inverseRead ∧
                          Cont forwardRead inverseRead compatibilityRead ∧
                            Cont compatibilityRead compatibility exactRead ∧
                              PkgSig bundle exactRead pkg)
                    hsame ∧
                  UnaryHistory exactRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier forwardRoute inverseRoute compatibilityReadRoute exactRoute exactPkg
  obtain ⟨_sourceUnary, _targetUnary, forwardUnary, inverseUnary, forwardUCUnary,
    inverseUCUnary, _forwardModUnary, _inverseModUnary, compatibilityUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _provenancePkg, _localNamePkg⟩ := carrier
  have forwardReadUnary : UnaryHistory forwardRead :=
    unary_cont_closed forwardUnary forwardUCUnary forwardRoute
  have inverseReadUnary : UnaryHistory inverseRead :=
    unary_cont_closed inverseUnary inverseUCUnary inverseRoute
  have compatibilityReadUnary : UnaryHistory compatibilityRead :=
    unary_cont_closed forwardReadUnary inverseReadUnary compatibilityReadRoute
  have exactReadUnary : UnaryHistory exactRead :=
    unary_cont_closed compatibilityReadUnary compatibilityUnary exactRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exactRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row forward ∨ hsame row inverse ∨ hsame row forwardUC ∨
              hsame row inverseUC ∨ hsame row forwardRead ∨ hsame row inverseRead ∨
                hsame row compatibilityRead ∨ hsame row exactRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont forward forwardUC forwardRead ∧
              Cont inverse inverseUC inverseRead ∧
                Cont forwardRead inverseRead compatibilityRead ∧
                  Cont compatibilityRead compatibility exactRead ∧ PkgSig bundle exactRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro exactRead ⟨hsame_refl exactRead, exactReadUnary⟩
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
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, forwardRoute, inverseRoute, compatibilityReadRoute, exactRoute,
          exactPkg⟩
  }
  exact ⟨cert, exactReadUnary⟩

end BEDC.Derived.UniformHomeomorphismUp
