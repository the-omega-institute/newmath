import BEDC.Derived.NormalFormConsistencySealUp
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.NormalFormConsistencySealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem NormalFormConsistencySealCriticalPairObligation
    {T F N K X H C P L typedFalse normalTheorem criticalPairRead replayRead namedRead :
      BHist} :
    UnaryHistory T →
      UnaryHistory F →
        UnaryHistory N →
          UnaryHistory K →
            UnaryHistory X →
              UnaryHistory H →
                UnaryHistory C →
                  UnaryHistory P →
                    UnaryHistory L →
                      Cont T F typedFalse →
                        Cont N K normalTheorem →
                          Cont normalTheorem X criticalPairRead →
                            Cont criticalPairRead C replayRead →
                              Cont replayRead L namedRead →
                                SemanticNameCert
                                      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row T ∨ hsame row F ∨ hsame row N ∨
                                          hsame row K ∨ hsame row X ∨
                                            hsame row criticalPairRead ∨ hsame row namedRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont normalTheorem X criticalPairRead)
                                      hsame ∧
                                    UnaryHistory criticalPairRead ∧
                                      UnaryHistory replayRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro tUnary fUnary nUnary kUnary xUnary _hUnary cUnary _pUnary lUnary typedFalseRoute
    normalTheoremRoute criticalPairRoute replayRoute nameRoute
  have typedFalseUnary : UnaryHistory typedFalse :=
    unary_cont_closed tUnary fUnary typedFalseRoute
  have normalTheoremUnary : UnaryHistory normalTheorem :=
    unary_cont_closed nUnary kUnary normalTheoremRoute
  have criticalPairUnary : UnaryHistory criticalPairRead :=
    unary_cont_closed normalTheoremUnary xUnary criticalPairRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed criticalPairUnary cUnary replayRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed replayReadUnary lUnary nameRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row T ∨ hsame row F ∨ hsame row N ∨ hsame row K ∨
            hsame row X ∨ hsame row criticalPairRead ∨ hsame row namedRead)
        (fun row : BHist => UnaryHistory row ∧ Cont normalTheorem X criticalPairRead)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro namedRead (And.intro (hsame_refl namedRead) namedReadUnary)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row col same
        exact hsame_symm same
      equiv_trans := by
        intro row col next sameRowCol sameColNext
        exact hsame_trans sameRowCol sameColNext
      carrier_respects_equiv := by
        intro row col same source
        exact And.intro (hsame_trans (hsame_symm same) source.left)
          (unary_transport source.right same)
    }
    pattern_sound := by
      intro row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro row source
      exact And.intro source.right criticalPairRoute
  }
  exact And.intro cert (And.intro criticalPairUnary (And.intro replayReadUnary namedReadUnary))

end BEDC.Derived.NormalFormConsistencySealUp
