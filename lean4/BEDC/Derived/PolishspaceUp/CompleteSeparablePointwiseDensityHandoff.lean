import BEDC.Derived.PolishspaceUp.CompleteSeparableObligationScope

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpaceCompleteSeparablePointwiseDensityHandoff [AskSetup] [PackageSetup]
    {M K D S R W H C G N denseRead streamWindow readbackRead completionRead
      handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.PolishSpaceUp.PolishSpaceCarrier M K D S R W H C G N bundle pkg ->
      Cont M D denseRead ->
        Cont denseRead S streamWindow ->
          Cont streamWindow R readbackRead ->
            Cont readbackRead K completionRead ->
              Cont completionRead N handoffRead ->
                PkgSig bundle G pkg ->
                  PkgSig bundle handoffRead pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row M ∨ hsame row K ∨ hsame row D ∨ hsame row S ∨
                            hsame row R ∨ hsame row W ∨ hsame row handoffRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont M D denseRead ∧
                            Cont denseRead S streamWindow ∧
                              Cont streamWindow R readbackRead ∧
                                Cont readbackRead K completionRead ∧
                                  Cont completionRead N handoffRead ∧
                                    PkgSig bundle G pkg ∧ PkgSig bundle handoffRead pkg)
                        hsame ∧
                      UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: PolishSpaceCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier denseRoute streamRoute readbackRoute completionRoute handoffRoute provenancePkg
    handoffPkg
  obtain ⟨MUnary, KUnary, DUnary, SUnary, RUnary, _WUnary, _HUnary, _CUnary,
    _GUnary, NUnary, _metricCompleteLedger, _ledgerStreamReadback,
    _transportReplayProvenance, _carrierPkg, _localPkg⟩ := carrier
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed MUnary DUnary denseRoute
  have streamUnary : UnaryHistory streamWindow :=
    unary_cont_closed denseUnary SUnary streamRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed streamUnary RUnary readbackRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed readbackUnary KUnary completionRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed completionUnary NUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row K ∨ hsame row D ∨ hsame row S ∨ hsame row R ∨
              hsame row W ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M D denseRead ∧ Cont denseRead S streamWindow ∧
              Cont streamWindow R readbackRead ∧ Cont readbackRead K completionRead ∧
                Cont completionRead N handoffRead ∧ PkgSig bundle G pkg ∧
                  PkgSig bundle handoffRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffUnary⟩
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
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, denseRoute, streamRoute, readbackRoute, completionRoute,
          handoffRoute, provenancePkg, handoffPkg⟩
  }
  exact ⟨cert, handoffUnary⟩

end BEDC.Derived.PolishspaceUp
