import BEDC.Derived.PolishspaceUp.CompletionDensityHandoff

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpaceCompleteSeparableObligationFrontier [AskSetup] [PackageSetup]
    {M K D S R W H C G N completionRead denseRead streamWindow readbackRead
      frontierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.PolishSpaceUp.PolishSpaceCarrier M K D S R W H C G N bundle pkg ->
      Cont M K completionRead ->
        Cont M D denseRead ->
          Cont denseRead S streamWindow ->
            Cont streamWindow R readbackRead ->
              Cont readbackRead W frontierRead ->
                PkgSig bundle G pkg ->
                  PkgSig bundle N pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row M ∨ hsame row K ∨ hsame row D ∨ hsame row S ∨
                            hsame row R ∨ hsame row W ∨ hsame row H ∨ hsame row C ∨
                              hsame row G ∨ hsame row N ∨ hsame row frontierRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont denseRead S streamWindow ∧
                            Cont streamWindow R readbackRead ∧
                              Cont readbackRead W frontierRead ∧ PkgSig bundle G pkg ∧
                                PkgSig bundle N pkg)
                        hsame ∧
                      UnaryHistory completionRead ∧ UnaryHistory denseRead ∧
                        UnaryHistory streamWindow ∧ UnaryHistory readbackRead ∧
                          UnaryHistory frontierRead := by
  -- BEDC touchpoint anchor: PolishSpaceCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier completionRoute denseRoute streamRoute readbackRoute frontierRoute
    provenancePkg localNamePkg
  obtain ⟨MUnary, KUnary, DUnary, SUnary, RUnary, WUnary, _HUnary, _CUnary,
    _GUnary, _NUnary, _metricCompleteLedger, _ledgerStreamReadback,
    _transportReplayProvenance, _carrierPkg, _localPkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed MUnary KUnary completionRoute
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed MUnary DUnary denseRoute
  have streamUnary : UnaryHistory streamWindow :=
    unary_cont_closed denseUnary SUnary streamRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed streamUnary RUnary readbackRoute
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed readbackUnary WUnary frontierRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row K ∨ hsame row D ∨ hsame row S ∨ hsame row R ∨
              hsame row W ∨ hsame row H ∨ hsame row C ∨ hsame row G ∨ hsame row N ∨
                hsame row frontierRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont denseRead S streamWindow ∧
              Cont streamWindow R readbackRead ∧ Cont readbackRead W frontierRead ∧
                PkgSig bundle G pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro frontierRead ⟨hsame_refl frontierRead, frontierUnary⟩
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
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, streamRoute, readbackRoute, frontierRoute, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, completionUnary, denseUnary, streamUnary, readbackUnary, frontierUnary⟩

end BEDC.Derived.PolishspaceUp
