import BEDC.Derived.PolishspaceUp.CompletionDensityHandoff

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpaceEffectiveRepresentedSourceBoundary [AskSetup] [PackageSetup]
    {M K D S R W H C G N denseRead streamWindow representedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.PolishSpaceUp.PolishSpaceCarrier M K D S R W H C G N bundle pkg ->
      Cont M D denseRead ->
        Cont denseRead S streamWindow ->
          Cont streamWindow R representedRead ->
            PkgSig bundle G pkg ->
              PkgSig bundle N pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row representedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row M ∨ hsame row D ∨ hsame row S ∨ hsame row R ∨
                        hsame row W ∨ hsame row G ∨ hsame row N ∨ hsame row denseRead ∨
                          hsame row streamWindow ∨ hsame row representedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont M D denseRead ∧ Cont denseRead S streamWindow ∧
                        Cont streamWindow R representedRead ∧ PkgSig bundle G pkg ∧
                          PkgSig bundle N pkg)
                    hsame ∧
                  UnaryHistory denseRead ∧ UnaryHistory streamWindow ∧
                    UnaryHistory representedRead := by
  -- BEDC touchpoint anchor: PolishSpaceCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier denseRoute streamRoute representedRoute provenancePkg localNamePkg
  obtain ⟨MUnary, _KUnary, DUnary, SUnary, RUnary, _WUnary, _HUnary, _CUnary,
    _GUnary, _NUnary, _metricCompleteLedger, _ledgerStreamReadback,
    _transportReplayProvenance, _carrierPkg, _localPkg⟩ := carrier
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed MUnary DUnary denseRoute
  have streamUnary : UnaryHistory streamWindow :=
    unary_cont_closed denseUnary SUnary streamRoute
  have representedUnary : UnaryHistory representedRead :=
    unary_cont_closed streamUnary RUnary representedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row representedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row D ∨ hsame row S ∨ hsame row R ∨ hsame row W ∨
              hsame row G ∨ hsame row N ∨ hsame row denseRead ∨ hsame row streamWindow ∨
                hsame row representedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M D denseRead ∧ Cont denseRead S streamWindow ∧
              Cont streamWindow R representedRead ∧ PkgSig bundle G pkg ∧
                PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro representedRead ⟨hsame_refl representedRead, representedUnary⟩
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
      exact ⟨source.right, denseRoute, streamRoute, representedRoute, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, denseUnary, streamUnary, representedUnary⟩

end BEDC.Derived.PolishspaceUp
