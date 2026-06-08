import BEDC.Derived.PolishspaceUp.CompleteSeparableObligationSurface

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpacePointwiseDensityHandoff [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger transport route provenance localName
      denseRead streamWindow pointRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory metric ->
      UnaryHistory complete ->
        UnaryHistory separable ->
          UnaryHistory stream ->
            UnaryHistory readback ->
              UnaryHistory ledger ->
                UnaryHistory transport ->
                  Cont metric separable denseRead ->
                    Cont denseRead stream streamWindow ->
                      Cont streamWindow readback pointRead ->
                        Cont metric complete completionRead ->
                          Cont ledger transport route ->
                            PkgSig bundle provenance pkg ->
                              PkgSig bundle localName pkg ->
                                SemanticNameCert
                                    (fun row : BHist => hsame row pointRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row metric ∨ hsame row separable ∨
                                        hsame row stream ∨ hsame row readback ∨
                                          hsame row denseRead ∨ hsame row streamWindow ∨
                                            hsame row pointRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont metric separable denseRead ∧
                                        Cont denseRead stream streamWindow ∧
                                          Cont streamWindow readback pointRead ∧
                                            Cont metric complete completionRead ∧
                                              PkgSig bundle provenance pkg ∧
                                                PkgSig bundle localName pkg)
                                    hsame ∧
                                  UnaryHistory denseRead ∧ UnaryHistory streamWindow ∧
                                    UnaryHistory pointRead ∧ UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro metricUnary completeUnary separableUnary streamUnary readbackUnary _ledgerUnary
    _transportUnary metricSeparableDense denseStreamWindow windowReadbackPoint
    metricCompleteCompletion _ledgerTransportRoute provenancePkg localNamePkg
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed metricUnary separableUnary metricSeparableDense
  have windowUnary : UnaryHistory streamWindow :=
    unary_cont_closed denseUnary streamUnary denseStreamWindow
  have pointUnary : UnaryHistory pointRead :=
    unary_cont_closed windowUnary readbackUnary windowReadbackPoint
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed metricUnary completeUnary metricCompleteCompletion
  have sourcePoint :
      (fun row : BHist => hsame row pointRead ∧ UnaryHistory row) pointRead := by
    exact ⟨hsame_refl pointRead, pointUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row pointRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row separable ∨ hsame row stream ∨
              hsame row readback ∨ hsame row denseRead ∨ hsame row streamWindow ∨
                hsame row pointRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont metric separable denseRead ∧
              Cont denseRead stream streamWindow ∧ Cont streamWindow readback pointRead ∧
                Cont metric complete completionRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro pointRead sourcePoint
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, metricSeparableDense, denseStreamWindow, windowReadbackPoint,
          metricCompleteCompletion, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, denseUnary, windowUnary, pointUnary, completionUnary⟩

end BEDC.Derived.PolishspaceUp
