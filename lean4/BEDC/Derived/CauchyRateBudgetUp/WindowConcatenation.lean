import BEDC.Derived.CauchyRateBudgetUp.NameCertObligations

namespace BEDC.Derived.CauchyRateBudgetUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CauchyRateBudgetWindowConcatenation
    {R0 W0 Q0 D0 E0 H0 C0 P0 N0 R1 W1 Q1 D1 E1 H1 C1 P1 N1 firstWindow
      firstReadback firstTolerance secondWindow secondReadback secondTolerance joinedBudget
      joinedSeal : BHist} :
    CauchyRateBudgetCarrier R0 W0 Q0 D0 E0 H0 C0 P0 N0 →
      CauchyRateBudgetCarrier R1 W1 Q1 D1 E1 H1 C1 P1 N1 →
        Cont R0 W0 firstWindow →
          Cont firstWindow Q0 firstReadback →
            Cont firstReadback D0 firstTolerance →
              Cont R1 W1 secondWindow →
                Cont secondWindow Q1 secondReadback →
                  Cont secondReadback D1 secondTolerance →
                    Cont firstTolerance secondTolerance joinedBudget →
                      Cont joinedBudget E1 joinedSeal →
                        SemanticNameCert
                            (fun row : BHist => hsame row joinedSeal ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row R0 ∨ hsame row W0 ∨ hsame row Q0 ∨
                                hsame row D0 ∨ hsame row R1 ∨ hsame row W1 ∨
                                  hsame row Q1 ∨ hsame row D1 ∨
                                    hsame row joinedBudget ∨ hsame row joinedSeal)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont R0 W0 firstWindow ∧
                                Cont firstWindow Q0 firstReadback ∧
                                  Cont firstReadback D0 firstTolerance ∧
                                    Cont R1 W1 secondWindow ∧
                                      Cont secondWindow Q1 secondReadback ∧
                                        Cont secondReadback D1 secondTolerance ∧
                                          Cont firstTolerance secondTolerance joinedBudget ∧
                                            Cont joinedBudget E1 joinedSeal)
                            hsame ∧
                          UnaryHistory firstWindow ∧ UnaryHistory firstReadback ∧
                            UnaryHistory firstTolerance ∧ UnaryHistory secondWindow ∧
                              UnaryHistory secondReadback ∧ UnaryHistory secondTolerance ∧
                                UnaryHistory joinedBudget ∧ UnaryHistory joinedSeal := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro firstCarrier secondCarrier firstWindowRoute firstReadbackRoute firstToleranceRoute
    secondWindowRoute secondReadbackRoute secondToleranceRoute joinedBudgetRoute joinedSealRoute
  obtain ⟨r0Unary, w0Unary, q0Unary, d0Unary, _e0Unary, _h0Unary, _c0Unary, _p0Unary,
    _n0Unary⟩ := firstCarrier
  obtain ⟨r1Unary, w1Unary, q1Unary, d1Unary, e1Unary, _h1Unary, _c1Unary, _p1Unary,
    _n1Unary⟩ := secondCarrier
  have firstWindowUnary : UnaryHistory firstWindow :=
    unary_cont_closed r0Unary w0Unary firstWindowRoute
  have firstReadbackUnary : UnaryHistory firstReadback :=
    unary_cont_closed firstWindowUnary q0Unary firstReadbackRoute
  have firstToleranceUnary : UnaryHistory firstTolerance :=
    unary_cont_closed firstReadbackUnary d0Unary firstToleranceRoute
  have secondWindowUnary : UnaryHistory secondWindow :=
    unary_cont_closed r1Unary w1Unary secondWindowRoute
  have secondReadbackUnary : UnaryHistory secondReadback :=
    unary_cont_closed secondWindowUnary q1Unary secondReadbackRoute
  have secondToleranceUnary : UnaryHistory secondTolerance :=
    unary_cont_closed secondReadbackUnary d1Unary secondToleranceRoute
  have joinedBudgetUnary : UnaryHistory joinedBudget :=
    unary_cont_closed firstToleranceUnary secondToleranceUnary joinedBudgetRoute
  have joinedSealUnary : UnaryHistory joinedSeal :=
    unary_cont_closed joinedBudgetUnary e1Unary joinedSealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row joinedSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R0 ∨ hsame row W0 ∨ hsame row Q0 ∨ hsame row D0 ∨
              hsame row R1 ∨ hsame row W1 ∨ hsame row Q1 ∨ hsame row D1 ∨
                hsame row joinedBudget ∨ hsame row joinedSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R0 W0 firstWindow ∧
              Cont firstWindow Q0 firstReadback ∧ Cont firstReadback D0 firstTolerance ∧
                Cont R1 W1 secondWindow ∧ Cont secondWindow Q1 secondReadback ∧
                  Cont secondReadback D1 secondTolerance ∧
                    Cont firstTolerance secondTolerance joinedBudget ∧
                      Cont joinedBudget E1 joinedSeal)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro joinedSeal ⟨hsame_refl joinedSeal, joinedSealUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, firstWindowRoute, firstReadbackRoute, firstToleranceRoute,
          secondWindowRoute, secondReadbackRoute, secondToleranceRoute, joinedBudgetRoute,
          joinedSealRoute⟩
  }
  exact
    ⟨cert, firstWindowUnary, firstReadbackUnary, firstToleranceUnary, secondWindowUnary,
      secondReadbackUnary, secondToleranceUnary, joinedBudgetUnary, joinedSealUnary⟩

theorem CauchyRateBudgetWindowConcatenation_namecert_scoped_route
    {R0 W0 Q0 D0 E0 H0 C0 P0 N0 R1 W1 Q1 D1 E1 H1 C1 P1 N1 firstWindow
      firstReadback firstTolerance secondWindow secondReadback secondTolerance joinedBudget
      joinedSeal : BHist} :
    CauchyRateBudgetCarrier R0 W0 Q0 D0 E0 H0 C0 P0 N0 →
      CauchyRateBudgetCarrier R1 W1 Q1 D1 E1 H1 C1 P1 N1 →
        Cont R0 W0 firstWindow →
          Cont firstWindow Q0 firstReadback →
            Cont firstReadback D0 firstTolerance →
              Cont R1 W1 secondWindow →
                Cont secondWindow Q1 secondReadback →
                  Cont secondReadback D1 secondTolerance →
                    Cont firstTolerance secondTolerance joinedBudget →
                      Cont joinedBudget E1 joinedSeal →
                        (SemanticNameCert
                              (fun row : BHist =>
                                hsame row R0 ∨ hsame row W0 ∨ hsame row Q0 ∨
                                  hsame row D0 ∨ hsame row E0 ∨ hsame row H0 ∨
                                    hsame row C0 ∨ hsame row P0 ∨ hsame row N0)
                              (fun row : BHist =>
                                hsame row R0 ∨ hsame row W0 ∨ hsame row Q0 ∨
                                  hsame row D0 ∨ hsame row E0 ∨ hsame row H0 ∨
                                    hsame row C0 ∨ hsame row P0 ∨ hsame row N0)
                              (fun row : BHist =>
                                hsame row R0 ∨ hsame row W0 ∨ hsame row Q0 ∨
                                  hsame row D0 ∨ hsame row E0 ∨ hsame row H0 ∨
                                    hsame row C0 ∨ hsame row P0 ∨ hsame row N0)
                              hsame ∧
                            cauchyRateBudgetFields
                                (CauchyRateBudgetUp.mk R0 W0 Q0 D0 E0 H0 C0 P0 N0) =
                              [R0, W0, Q0, D0, E0, H0, C0, P0, N0]) ∧
                          (SemanticNameCert
                              (fun row : BHist =>
                                hsame row R1 ∨ hsame row W1 ∨ hsame row Q1 ∨
                                  hsame row D1 ∨ hsame row E1 ∨ hsame row H1 ∨
                                    hsame row C1 ∨ hsame row P1 ∨ hsame row N1)
                              (fun row : BHist =>
                                hsame row R1 ∨ hsame row W1 ∨ hsame row Q1 ∨
                                  hsame row D1 ∨ hsame row E1 ∨ hsame row H1 ∨
                                    hsame row C1 ∨ hsame row P1 ∨ hsame row N1)
                              (fun row : BHist =>
                                hsame row R1 ∨ hsame row W1 ∨ hsame row Q1 ∨
                                  hsame row D1 ∨ hsame row E1 ∨ hsame row H1 ∨
                                    hsame row C1 ∨ hsame row P1 ∨ hsame row N1)
                              hsame ∧
                            cauchyRateBudgetFields
                                (CauchyRateBudgetUp.mk R1 W1 Q1 D1 E1 H1 C1 P1 N1) =
                              [R1, W1, Q1, D1, E1, H1, C1, P1, N1]) ∧
                            SemanticNameCert
                                (fun row : BHist => hsame row joinedSeal ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row R0 ∨ hsame row W0 ∨ hsame row Q0 ∨
                                    hsame row D0 ∨ hsame row R1 ∨ hsame row W1 ∨
                                      hsame row Q1 ∨ hsame row D1 ∨
                                        hsame row joinedBudget ∨ hsame row joinedSeal)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont R0 W0 firstWindow ∧
                                    Cont firstWindow Q0 firstReadback ∧
                                      Cont firstReadback D0 firstTolerance ∧
                                        Cont R1 W1 secondWindow ∧
                                          Cont secondWindow Q1 secondReadback ∧
                                            Cont secondReadback D1 secondTolerance ∧
                                              Cont firstTolerance secondTolerance joinedBudget ∧
                                                Cont joinedBudget E1 joinedSeal)
                                hsame ∧
                              UnaryHistory joinedBudget ∧ UnaryHistory joinedSeal := by
  intro firstCarrier secondCarrier firstWindowRoute firstReadbackRoute firstToleranceRoute
    secondWindowRoute secondReadbackRoute secondToleranceRoute joinedBudgetRoute joinedSealRoute
  have firstObligations :=
    BEDC.Derived.CauchyRateBudgetUp.CauchyRateBudgetCarrier_namecert_obligations
      R0 W0 Q0 D0 E0 H0 C0 P0 N0
  have secondObligations :=
    BEDC.Derived.CauchyRateBudgetUp.CauchyRateBudgetCarrier_namecert_obligations
      R1 W1 Q1 D1 E1 H1 C1 P1 N1
  have joined :=
    CauchyRateBudgetWindowConcatenation
      firstCarrier secondCarrier firstWindowRoute firstReadbackRoute firstToleranceRoute
      secondWindowRoute secondReadbackRoute secondToleranceRoute joinedBudgetRoute joinedSealRoute
  exact
    ⟨firstObligations, secondObligations, joined.left,
      joined.right.right.right.right.right.right.right⟩

end BEDC.Derived.CauchyRateBudgetUp
