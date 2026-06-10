import BEDC.Derived.PolishspaceUp.CompletionDensityHandoff

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpaceEffectiveRepresentationSeparableReadback [AskSetup] [PackageSetup]
    {M K D S R W H C G N denseWindow readbackWindow effectiveRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.PolishSpaceUp.PolishSpaceCarrier M K D S R W H C G N bundle pkg ->
      Cont D S denseWindow ->
        Cont denseWindow R readbackWindow ->
          Cont readbackWindow N effectiveRead ->
            PkgSig bundle G pkg ->
              PkgSig bundle N pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row effectiveRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row M ∨ hsame row K ∨ hsame row D ∨ hsame row S ∨
                        hsame row R ∨ hsame row W ∨ hsame row N ∨
                          hsame row denseWindow ∨ hsame row readbackWindow ∨
                            hsame row effectiveRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont D S denseWindow ∧
                        Cont denseWindow R readbackWindow ∧
                          Cont readbackWindow N effectiveRead ∧ PkgSig bundle G pkg ∧
                            PkgSig bundle N pkg)
                    hsame ∧
                  UnaryHistory denseWindow ∧ UnaryHistory readbackWindow ∧
                    UnaryHistory effectiveRead := by
  -- BEDC touchpoint anchor: PolishSpaceCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier denseRoute readbackRoute effectiveRoute provenancePkg localNamePkg
  obtain ⟨_MUnary, _KUnary, DUnary, SUnary, RUnary, _WUnary, _HUnary, _CUnary,
    _GUnary, NUnary, _metricCompleteLedger, _ledgerStreamReadback,
    _transportReplayProvenance, _carrierPkg, _localPkg⟩ := carrier
  have denseUnary : UnaryHistory denseWindow :=
    unary_cont_closed DUnary SUnary denseRoute
  have readbackUnary : UnaryHistory readbackWindow :=
    unary_cont_closed denseUnary RUnary readbackRoute
  have effectiveUnary : UnaryHistory effectiveRead :=
    unary_cont_closed readbackUnary NUnary effectiveRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row effectiveRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row K ∨ hsame row D ∨ hsame row S ∨ hsame row R ∨
              hsame row W ∨ hsame row N ∨ hsame row denseWindow ∨
                hsame row readbackWindow ∨ hsame row effectiveRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D S denseWindow ∧
              Cont denseWindow R readbackWindow ∧ Cont readbackWindow N effectiveRead ∧
                PkgSig bundle G pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro effectiveRead ⟨hsame_refl effectiveRead, effectiveUnary⟩
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
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, denseRoute, readbackRoute, effectiveRoute, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, denseUnary, readbackUnary, effectiveUnary⟩

end BEDC.Derived.PolishspaceUp
