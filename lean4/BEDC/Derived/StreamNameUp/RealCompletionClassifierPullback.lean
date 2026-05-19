import BEDC.Derived.StreamNameUp.RealCompletionFourObjectExitRoute
import BEDC.FKernel.NameCert

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem StreamNameRealCompletionClassifierPullback
    {stream dyadic regseq real support exit terminalA terminalB : BHist}
    {bundle : ProbeBundle BHist} :
    UnaryHistory stream ->
      UnaryHistory dyadic ->
        UnaryHistory regseq ->
          UnaryHistory real ->
            Cont stream dyadic support ->
              Cont regseq real exit ->
                Cont support exit terminalA ->
                  Cont support exit terminalB ->
                    InBundle stream bundle ->
                      InBundle dyadic bundle ->
                        InBundle regseq bundle ->
                          InBundle real bundle ->
                            SemanticNameCert
                                (fun row : BHist => hsame row terminalA ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row stream ∨ hsame row dyadic ∨ hsame row regseq ∨
                                    hsame row real ∨ hsame row terminalA ∨
                                      hsame row terminalB)
                                (fun row : BHist =>
                                  hsame row terminalA ∧ InBundle stream bundle ∧
                                    InBundle dyadic bundle ∧ InBundle regseq bundle ∧
                                      InBundle real bundle)
                                hsame ∧
                              hsame terminalA terminalB ∧ UnaryHistory support ∧
                                UnaryHistory exit ∧ UnaryHistory terminalA ∧
                                  UnaryHistory terminalB ∧ Cont stream dyadic support ∧
                                    Cont regseq real exit ∧ Cont support exit terminalA ∧
                                      Cont support exit terminalB := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont InBundle hsame SemanticNameCert UnaryHistory
  intro streamUnary dyadicUnary regseqUnary realUnary supportRoute exitRoute terminalRouteA
    terminalRouteB streamMember dyadicMember regseqMember realMember
  have terminalPackage :=
    StreamNameRealCompletionFourObjectTerminalPullback streamUnary dyadicUnary regseqUnary
      realUnary supportRoute exitRoute terminalRouteA terminalRouteB streamMember dyadicMember
      regseqMember realMember
  obtain ⟨supportUnary, exitUnary, terminalAUnary, terminalBUnary, terminalSame,
    supportRouteOut, exitRouteOut, terminalRouteAOut, terminalRouteBOut, _streamMemberOut,
    _dyadicMemberOut, _regseqMemberOut, _realMemberOut⟩ := terminalPackage
  have terminalSource : hsame terminalA terminalA ∧ UnaryHistory terminalA :=
    ⟨hsame_refl terminalA, terminalAUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminalA ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stream ∨ hsame row dyadic ∨ hsame row regseq ∨ hsame row real ∨
              hsame row terminalA ∨ hsame row terminalB)
          (fun row : BHist =>
            hsame row terminalA ∧ InBundle stream bundle ∧ InBundle dyadic bundle ∧
              InBundle regseq bundle ∧ InBundle real bundle)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro terminalA terminalSource
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, streamMember, dyadicMember, regseqMember, realMember⟩
  }
  exact
    ⟨cert, terminalSame, supportUnary, exitUnary, terminalAUnary, terminalBUnary,
      supportRouteOut, exitRouteOut, terminalRouteAOut, terminalRouteBOut⟩

end BEDC.Derived.StreamNameUp
