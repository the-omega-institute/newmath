import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyNetLimitUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CauchyNetLimitCarrier_semantic_name_certificate
    (K W R D A H C P N : BHist) :
    SemanticNameCert
      (fun row : BHist =>
        hsame row K ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨ hsame row A ∨
          hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
      (fun row : BHist =>
        hsame row K ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨ hsame row A ∨
          hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
      (fun row : BHist =>
        hsame row K ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨ hsame row A ∨
          hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
      hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert
  exact {
    core := {
      carrier_inhabited := Exists.intro K (Or.inl (hsame_refl K))
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
        | inl sameK =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameK)
        | inr rest =>
            cases rest with
            | inl sameW =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameW))
            | inr rest =>
                cases rest with
                | inl sameR =>
                    exact Or.inr (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameR)))
                | inr rest =>
                    cases rest with
                    | inl sameD =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameD))))
                    | inr rest =>
                        cases rest with
                        | inl sameA =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inl (hsame_trans (hsame_symm sameRows) sameA)))))
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
                                | inl sameC =>
                                    exact
                                      Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inl
                                                    (hsame_trans
                                                      (hsame_symm sameRows) sameC)))))))
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
                                                        (Or.inl
                                                          (hsame_trans
                                                            (hsame_symm sameRows) sameP))))))))
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
                                                          (hsame_trans
                                                            (hsame_symm sameRows) sameN))))))))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem CauchyNetLimitCarrier_real_seal_handoff
    {K W R D A H C P N windowRead readbackRead toleranceRead sealRead namedRead : BHist} :
    Cont K W windowRead ->
      Cont windowRead R readbackRead ->
        Cont readbackRead D toleranceRead ->
          Cont toleranceRead A sealRead ->
            Cont sealRead H namedRead ->
              UnaryHistory K ->
                UnaryHistory W ->
                  UnaryHistory R ->
                    UnaryHistory D ->
                      UnaryHistory A ->
                        UnaryHistory H ->
                          UnaryHistory windowRead ∧ UnaryHistory readbackRead ∧
                            UnaryHistory toleranceRead ∧ UnaryHistory sealRead ∧
                              UnaryHistory namedRead ∧ Cont K W windowRead ∧
                                Cont windowRead R readbackRead ∧
                                  Cont readbackRead D toleranceRead ∧
                                    Cont toleranceRead A sealRead ∧
                                      Cont sealRead H namedRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro windowRoute readbackRoute toleranceRoute sealRoute namedRoute
  intro kUnary wUnary rUnary dUnary aUnary hUnary
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed kUnary wUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary rUnary readbackRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed readbackUnary dUnary toleranceRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceUnary aUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary hUnary namedRoute
  exact
    ⟨windowUnary, readbackUnary, toleranceUnary, sealUnary, namedUnary, windowRoute,
      readbackRoute, toleranceRoute, sealRoute, namedRoute⟩

theorem CauchyNetLimitCarrier_directed_window_obligations
    {K W R D windowRead readbackRead toleranceRead : BHist} :
    Cont K W windowRead →
      Cont windowRead R readbackRead →
        Cont readbackRead D toleranceRead →
          UnaryHistory K →
            UnaryHistory W →
              UnaryHistory R →
                UnaryHistory D →
                  UnaryHistory windowRead ∧ UnaryHistory readbackRead ∧
                    UnaryHistory toleranceRead ∧ Cont K W windowRead ∧
                      Cont windowRead R readbackRead ∧ Cont readbackRead D toleranceRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro windowRoute readbackRoute toleranceRoute kUnary wUnary rUnary dUnary
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed kUnary wUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary rUnary readbackRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed readbackUnary dUnary toleranceRoute
  exact
    ⟨windowUnary, readbackUnary, toleranceUnary, windowRoute, readbackRoute, toleranceRoute⟩

end BEDC.Derived.CauchyNetLimitUp
