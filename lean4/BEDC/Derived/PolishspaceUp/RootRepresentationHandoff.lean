import BEDC.Derived.PolishspaceUp.CompletionDensityHandoff
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpaceRootRepresentationHandoff [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger transport replay provenance localName
      representedRead nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.PolishSpaceUp.PolishSpaceCarrier metric complete separable stream readback
        ledger transport replay provenance localName bundle pkg →
      Cont complete separable representedRead →
        Cont representedRead stream nameRead →
          PkgSig bundle nameRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row nameRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row complete ∨ hsame row separable ∨ hsame row stream ∨
                    hsame row readback ∨ hsame row representedRead ∨ hsame row nameRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle nameRead pkg)
                hsame ∧
              UnaryHistory representedRead ∧ UnaryHistory nameRead := by
  -- BEDC touchpoint anchor: PolishSpaceCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier representedRoute nameRoute namePkg
  obtain ⟨_metricUnary, completeUnary, separableUnary, streamUnary, _readbackUnary,
    _ledgerUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _metricCompleteLedger, _ledgerStreamReadback, _transportReplayProvenance,
    provenancePkg, _localNamePkg⟩ := carrier
  have representedUnary : UnaryHistory representedRead :=
    unary_cont_closed completeUnary separableUnary representedRoute
  have nameUnary : UnaryHistory nameRead :=
    unary_cont_closed representedUnary streamUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row nameRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row complete ∨ hsame row separable ∨ hsame row stream ∨
              hsame row readback ∨ hsame row representedRead ∨ hsame row nameRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle nameRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro nameRead ⟨hsame_refl nameRead, nameUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, namePkg⟩
  }
  exact ⟨cert, representedUnary, nameUnary⟩

end BEDC.Derived.PolishspaceUp
