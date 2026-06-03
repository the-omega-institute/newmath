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

theorem PolishSpaceL10CompleteSeparableConsumerPackage [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger transport replay provenance localName
      completionRead denseRead supportRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory metric ->
      UnaryHistory complete ->
        UnaryHistory separable ->
          UnaryHistory stream ->
            UnaryHistory readback ->
              UnaryHistory ledger ->
                UnaryHistory transport ->
                  Cont complete stream completionRead ->
                    Cont separable stream denseRead ->
                      Cont ledger transport replay ->
                        Cont replay readback supportRead ->
                          Cont completionRead denseRead consumerRead ->
                            PkgSig bundle provenance pkg ->
                              PkgSig bundle localName pkg ->
                                SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row consumerRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row complete ∨ hsame row separable ∨
                                        hsame row stream ∨ hsame row readback ∨
                                          hsame row supportRead ∨ hsame row consumerRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                        PkgSig bundle localName pkg)
                                    hsame ∧
                                  UnaryHistory completionRead ∧ UnaryHistory denseRead ∧
                                    UnaryHistory supportRead ∧
                                      UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro _metricUnary completeUnary separableUnary streamUnary readbackUnary ledgerUnary
    transportUnary completionRoute denseRoute replayRoute supportRoute consumerRoute
    provenancePkg localNamePkg
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed completeUnary streamUnary completionRoute
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed separableUnary streamUnary denseRoute
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed ledgerUnary transportUnary replayRoute
  have supportUnary : UnaryHistory supportRead :=
    unary_cont_closed replayUnary readbackUnary supportRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed completionUnary denseUnary consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row complete ∨ hsame row separable ∨ hsame row stream ∨
              hsame row readback ∨ hsame row supportRead ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerUnary⟩
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
  exact ⟨cert, completionUnary, denseUnary, supportUnary, consumerUnary⟩

end BEDC.Derived.PolishspaceUp
