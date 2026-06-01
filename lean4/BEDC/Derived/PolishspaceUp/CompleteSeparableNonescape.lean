import BEDC.Derived.PolishspaceUp.CompletionDensityHandoff

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.PolishSpaceUp

theorem PolishSpaceCompleteSeparableNonescape [AskSetup] [PackageSetup]
    {M K D S R W H C G N completeRead separableRead synthesisRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolishSpaceCarrier M K D S R W H C G N bundle pkg →
      Cont K D completeRead →
        Cont S R separableRead →
          Cont completeRead separableRead synthesisRead →
            Cont synthesisRead W boundaryRead →
              PkgSig bundle boundaryRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row M ∨ hsame row K ∨ hsame row D ∨ hsame row S ∨
                        hsame row R ∨ hsame row W ∨ hsame row H ∨ hsame row C ∨
                          hsame row G ∨ hsame row N ∨ hsame row completeRead ∨
                            hsame row separableRead ∨ hsame row synthesisRead ∨
                              hsame row boundaryRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle G pkg ∧
                        PkgSig bundle boundaryRead pkg)
                    hsame ∧
                  UnaryHistory completeRead ∧ UnaryHistory separableRead ∧
                    UnaryHistory synthesisRead ∧ UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier completeRoute separableRoute synthesisRoute boundaryRoute boundaryPkg
  obtain ⟨_mUnary, kUnary, dUnary, sUnary, rUnary, wUnary, _hUnary, _cUnary,
    _gUnary, _nUnary, _metricCompleteLedger, _ledgerStreamReadback,
    _transportReplayProvenance, provenancePkg, _localPkg⟩ := carrier
  have completeUnary : UnaryHistory completeRead :=
    unary_cont_closed kUnary dUnary completeRoute
  have separableUnary : UnaryHistory separableRead :=
    unary_cont_closed sUnary rUnary separableRoute
  have synthesisUnary : UnaryHistory synthesisRead :=
    unary_cont_closed completeUnary separableUnary synthesisRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed synthesisUnary wUnary boundaryRoute
  have sourceBoundary :
      (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row) boundaryRead := by
    exact ⟨hsame_refl boundaryRead, boundaryUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row K ∨ hsame row D ∨ hsame row S ∨
              hsame row R ∨ hsame row W ∨ hsame row H ∨ hsame row C ∨
                hsame row G ∨ hsame row N ∨ hsame row completeRead ∨
                  hsame row separableRead ∨ hsame row synthesisRead ∨
                    hsame row boundaryRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle G pkg ∧ PkgSig bundle boundaryRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundaryRead sourceBoundary
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, boundaryPkg⟩
  }
  exact ⟨cert, completeUnary, separableUnary, synthesisUnary, boundaryUnary⟩

end BEDC.Derived.PolishspaceUp
