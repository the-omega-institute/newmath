import BEDC.Derived.UniformHomeomorphismUp.CompletionConsumerBoundary
import BEDC.Derived.UniformHomeomorphismUp.NameCertObligations

namespace BEDC.Derived.UniformHomeomorphismUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformHomeomorphismScopedRoute [AskSetup] [PackageSetup]
    {source target forward inverse forwardUC inverseUC forwardMod inverseMod compatibility replay
      provenance localName scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformHomeomorphismCarrier source target forward inverse forwardUC inverseUC forwardMod
      inverseMod compatibility replay provenance localName bundle pkg →
      Cont compatibility replay scopedRead →
        PkgSig bundle scopedRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row source ∨ hsame row target ∨ hsame row forward ∨
                  hsame row inverse ∨ hsame row forwardUC ∨ hsame row inverseUC ∨
                    hsame row forwardMod ∨ hsame row inverseMod ∨
                      hsame row compatibility ∨ hsame row replay ∨
                        hsame row provenance ∨ hsame row localName ∨ hsame row scopedRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont compatibility replay scopedRead ∧
                  PkgSig bundle scopedRead pkg)
              hsame ∧
            UnaryHistory scopedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame
  intro carrier scopedRoute scopedPkg
  obtain ⟨_sourceUnary, _targetUnary, _forwardUnary, _inverseUnary, _forwardUCUnary,
    _inverseUCUnary, _forwardModUnary, _inverseModUnary, compatibilityUnary, replayUnary,
    _provenanceUnary, _localNameUnary, _provenancePkg, _localNamePkg⟩ := carrier
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed compatibilityUnary replayUnary scopedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row target ∨ hsame row forward ∨
              hsame row inverse ∨ hsame row forwardUC ∨ hsame row inverseUC ∨
                hsame row forwardMod ∨ hsame row inverseMod ∨
                  hsame row compatibility ∨ hsame row replay ∨
                    hsame row provenance ∨ hsame row localName ∨ hsame row scopedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont compatibility replay scopedRead ∧
              PkgSig bundle scopedRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro scopedRead ⟨hsame_refl scopedRead, scopedUnary⟩
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
        exact ⟨source.right, scopedRoute, scopedPkg⟩
    }
  exact ⟨cert, scopedUnary⟩

end BEDC.Derived.UniformHomeomorphismUp
