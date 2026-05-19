import BEDC.Derived.StreamNameUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem StreamNameRealCompletionExitAxisSeparation
    {stream dyadic regseq real support exit terminal : BHist} {bundle : ProbeBundle BHist} :
    UnaryHistory stream ->
      UnaryHistory dyadic ->
        UnaryHistory regseq ->
          UnaryHistory real ->
            Cont stream dyadic support ->
              Cont regseq real exit ->
                Cont support exit terminal ->
                  InBundle stream bundle ->
                    InBundle dyadic bundle ->
                      InBundle regseq bundle ->
                        InBundle real bundle ->
                          SemanticNameCert
                              (fun row : BHist => hsame row terminal ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row terminal ∧ Cont stream dyadic support ∧
                                  Cont regseq real exit)
                              (fun row : BHist =>
                                hsame row terminal ∧ Cont support exit terminal)
                              hsame ∧
                            UnaryHistory support ∧ UnaryHistory exit ∧
                              UnaryHistory terminal ∧ Cont stream dyadic support ∧
                                Cont regseq real exit ∧ Cont support exit terminal ∧
                                  InBundle stream bundle ∧ InBundle dyadic bundle ∧
                                    InBundle regseq bundle ∧ InBundle real bundle := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont InBundle hsame SemanticNameCert UnaryHistory
  intro streamUnary dyadicUnary regseqUnary realUnary supportRoute exitRoute terminalRoute
    streamMember dyadicMember regseqMember realMember
  have supportUnary : UnaryHistory support :=
    unary_cont_closed streamUnary dyadicUnary supportRoute
  have exitUnary : UnaryHistory exit :=
    unary_cont_closed regseqUnary realUnary exitRoute
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed supportUnary exitUnary terminalRoute
  have sourceAtTerminal : hsame terminal terminal ∧ UnaryHistory terminal :=
    ⟨hsame_refl terminal, terminalUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row terminal ∧ Cont stream dyadic support ∧ Cont regseq real exit)
          (fun row : BHist => hsame row terminal ∧ Cont support exit terminal)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro terminal sourceAtTerminal
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
      exact ⟨source.left, supportRoute, exitRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, terminalRoute⟩
  }
  exact
    ⟨cert, supportUnary, exitUnary, terminalUnary, supportRoute, exitRoute, terminalRoute,
      streamMember, dyadicMember, regseqMember, realMember⟩

end BEDC.Derived.StreamNameUp
