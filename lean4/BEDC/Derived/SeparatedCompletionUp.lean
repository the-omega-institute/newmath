import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.SeparatedCompletionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem SeparatedCompletionCarrier_semantic_name_certificate
    (M D C Z U H R T P N : BHist) :
    SemanticNameCert
      (fun row : BHist =>
        hsame row M ∨ hsame row D ∨ hsame row C ∨ hsame row Z ∨ hsame row U ∨
          hsame row H ∨ hsame row R ∨ hsame row T ∨ hsame row P ∨ hsame row N)
      (fun row : BHist =>
        hsame row M ∨ hsame row D ∨ hsame row C ∨ hsame row Z ∨ hsame row U ∨
          hsame row H ∨ hsame row R ∨ hsame row T ∨ hsame row P ∨ hsame row N)
      (fun row : BHist =>
        hsame row M ∨ hsame row D ∨ hsame row C ∨ hsame row Z ∨ hsame row U ∨
          hsame row H ∨ hsame row R ∨ hsame row T ∨ hsame row P ∨ hsame row N)
      hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert
  exact {
    core := {
      carrier_inhabited := Exists.intro M (Or.inl (hsame_refl M))
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
        intro row other sameRows source
        cases source with
        | inl sameM =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameM)
        | inr rest =>
            cases rest with
            | inl sameD =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameD))
            | inr rest =>
                cases rest with
                | inl sameC =>
                    exact Or.inr (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameC)))
                | inr rest =>
                    cases rest with
                    | inl sameZ =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameZ))))
                    | inr rest =>
                        cases rest with
                        | inl sameU =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inl (hsame_trans (hsame_symm sameRows) sameU)))))
                        | inr rest =>
                            cases rest with
                            | inl sameH =>
                                exact
                                  Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inl
                                              (hsame_trans (hsame_symm sameRows) sameH))))))
                            | inr rest =>
                                cases rest with
                                | inl sameR =>
                                    exact
                                      Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inl
                                                    (hsame_trans
                                                      (hsame_symm sameRows) sameR)))))))
                                | inr rest =>
                                    cases rest with
                                    | inl sameT =>
                                        exact
                                          Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inl
                                                          (hsame_trans
                                                            (hsame_symm sameRows) sameT))))))))
                                    | inr rest =>
                                        cases rest with
                                        | inl sameP =>
                                            exact
                                              Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr
                                                          (Or.inr
                                                            (Or.inr
                                                              (Or.inl
                                                                (hsame_trans
                                                                  (hsame_symm sameRows)
                                                                  sameP)))))))))
                                        | inr sameN =>
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
                                                                (hsame_trans
                                                                  (hsame_symm sameRows)
                                                                  sameN)))))))))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem SeparatedCompletionCarrier_separated_limit_handoff
    {source dense handoff classifier unique : BHist} :
    UnaryHistory source →
      UnaryHistory dense →
        UnaryHistory classifier →
          Cont source dense handoff →
            Cont handoff classifier unique →
              UnaryHistory handoff ∧ UnaryHistory unique ∧
                Cont source dense handoff ∧ Cont handoff classifier unique := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro sourceUnary denseUnary classifierUnary sourceDenseHandoff handoffClassifierUnique
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed sourceUnary denseUnary sourceDenseHandoff
  exact
    ⟨handoffUnary,
      unary_cont_closed handoffUnary classifierUnary handoffClassifierUnique,
      sourceDenseHandoff,
      handoffClassifierUnique⟩

end BEDC.Derived.SeparatedCompletionUp
