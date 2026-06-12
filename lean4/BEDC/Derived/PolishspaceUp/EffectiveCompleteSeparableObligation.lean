import BEDC.Derived.PolishspaceUp.CompletionDensityHandoff

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpaceEffectiveCompleteSeparableObligation [AskSetup] [PackageSetup]
    {M K D S R W H C G N completionRead denseRead completeSeparableRead publicRead
      effectiveRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.PolishSpaceUp.PolishSpaceCarrier M K D S R W H C G N bundle pkg ->
      Cont M K completionRead ->
        Cont M D denseRead ->
          Cont completionRead denseRead completeSeparableRead ->
            Cont completeSeparableRead W publicRead ->
              Cont publicRead N effectiveRead ->
                PkgSig bundle G pkg ->
                  PkgSig bundle N pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row effectiveRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row M ∨ hsame row K ∨ hsame row D ∨ hsame row W ∨
                            hsame row G ∨ hsame row N ∨ hsame row completionRead ∨
                              hsame row denseRead ∨ hsame row completeSeparableRead ∨
                                hsame row publicRead ∨ hsame row effectiveRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont M K completionRead ∧
                            Cont M D denseRead ∧
                              Cont completionRead denseRead completeSeparableRead ∧
                                Cont completeSeparableRead W publicRead ∧
                                  Cont publicRead N effectiveRead ∧ PkgSig bundle G pkg ∧
                                    PkgSig bundle N pkg)
                        hsame ∧
                      UnaryHistory completionRead ∧ UnaryHistory denseRead ∧
                        UnaryHistory completeSeparableRead ∧ UnaryHistory publicRead ∧
                          UnaryHistory effectiveRead := by
  -- BEDC touchpoint anchor: PolishSpaceCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier completionRoute denseRoute completeSeparableRoute publicRoute effectiveRoute
    provenancePkg localNamePkg
  obtain ⟨MUnary, KUnary, DUnary, _SUnary, _RUnary, WUnary, _HUnary, _CUnary,
    _GUnary, NUnary, _metricCompleteLedger, _ledgerStreamReadback,
    _transportReplayProvenance, _carrierPkg, _localPkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed MUnary KUnary completionRoute
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed MUnary DUnary denseRoute
  have completeSeparableUnary : UnaryHistory completeSeparableRead :=
    unary_cont_closed completionUnary denseUnary completeSeparableRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed completeSeparableUnary WUnary publicRoute
  have effectiveUnary : UnaryHistory effectiveRead :=
    unary_cont_closed publicUnary NUnary effectiveRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row effectiveRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row K ∨ hsame row D ∨ hsame row W ∨ hsame row G ∨
              hsame row N ∨ hsame row completionRead ∨ hsame row denseRead ∨
                hsame row completeSeparableRead ∨ hsame row publicRead ∨
                  hsame row effectiveRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M K completionRead ∧ Cont M D denseRead ∧
              Cont completionRead denseRead completeSeparableRead ∧
                Cont completeSeparableRead W publicRead ∧ Cont publicRead N effectiveRead ∧
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
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, completionRoute, denseRoute, completeSeparableRoute, publicRoute,
          effectiveRoute, provenancePkg, localNamePkg⟩
  }
  exact
    ⟨cert, completionUnary, denseUnary, completeSeparableUnary, publicUnary,
      effectiveUnary⟩

end BEDC.Derived.PolishspaceUp
