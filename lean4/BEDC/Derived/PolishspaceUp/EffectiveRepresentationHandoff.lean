import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpaceEffectiveRepresentationHandoff [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger transport replay represented computable
      provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory metric →
      UnaryHistory complete →
        UnaryHistory separable →
          UnaryHistory stream →
            UnaryHistory readback →
              UnaryHistory ledger →
                UnaryHistory transport →
                  Cont metric complete represented →
                    Cont separable stream replay →
                      Cont replay readback computable →
                        PkgSig bundle provenance pkg →
                          PkgSig bundle localName pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row computable ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row metric ∨ hsame row complete ∨
                                    hsame row separable ∨ hsame row stream ∨
                                      hsame row readback ∨ hsame row computable)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                    PkgSig bundle localName pkg)
                                hsame ∧
                              UnaryHistory represented ∧ UnaryHistory replay ∧
                                UnaryHistory computable := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro metricUnary completeUnary separableUnary streamUnary readbackUnary _ledgerUnary
    _transportUnary representedRoute replayRoute computableRoute provenancePkg localNamePkg
  have representedUnary : UnaryHistory represented :=
    unary_cont_closed metricUnary completeUnary representedRoute
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed separableUnary streamUnary replayRoute
  have computableUnary : UnaryHistory computable :=
    unary_cont_closed replayUnary readbackUnary computableRoute
  have sourceComputable :
      (fun row : BHist => hsame row computable ∧ UnaryHistory row) computable := by
    exact ⟨hsame_refl computable, computableUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row computable ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
              hsame row stream ∨ hsame row readback ∨ hsame row computable)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro computable sourceComputable
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
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, representedUnary, replayUnary, computableUnary⟩

end BEDC.Derived.PolishspaceUp
