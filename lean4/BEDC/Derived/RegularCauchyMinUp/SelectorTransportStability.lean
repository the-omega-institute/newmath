import BEDC.Derived.RegularCauchyMinUp.SelectorLedger

namespace BEDC.Derived.RegularCauchyMinUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem RegularCauchyMinCarrier_selector_transport_stability
    {A B W DA DB J S R E H C P N selectedRead readbackRead sealRead transportRead
      replayRead : BHist} :
    UnaryHistory A →
      UnaryHistory B →
        UnaryHistory W →
          UnaryHistory DA →
            UnaryHistory DB →
              UnaryHistory S →
                UnaryHistory R →
                  UnaryHistory E →
                    UnaryHistory H →
                      UnaryHistory C →
                        Cont A W selectedRead →
                          Cont selectedRead DA S →
                            Cont S R readbackRead →
                              Cont readbackRead E sealRead →
                                Cont sealRead H transportRead →
                                  Cont transportRead C replayRead →
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row replayRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row A ∨ hsame row B ∨ hsame row W ∨
                                            hsame row DA ∨ hsame row DB ∨ hsame row J ∨
                                              hsame row S ∨ hsame row R ∨ hsame row E ∨
                                                hsame row H ∨ hsame row C ∨ hsame row P ∨
                                                  hsame row N ∨ hsame row replayRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ Cont A W selectedRead ∧
                                            Cont selectedRead DA S ∧
                                              Cont S R readbackRead ∧
                                                Cont readbackRead E sealRead ∧
                                                  Cont sealRead H transportRead ∧
                                                    Cont transportRead C replayRead)
                                        hsame ∧
                                      UnaryHistory selectedRead ∧
                                        UnaryHistory readbackRead ∧
                                          UnaryHistory sealRead ∧
                                            UnaryHistory transportRead ∧
                                              UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro aUnary _bUnary wUnary daUnary _dbUnary sUnary rUnary eUnary hUnary cUnary
    selectedRoute selectedCommit readbackRoute sealRoute transportRoute replayRoute
  have selectedUnary : UnaryHistory selectedRead :=
    unary_cont_closed aUnary wUnary selectedRoute
  have selectedSurfaceUnary : UnaryHistory S :=
    sUnary
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed selectedSurfaceUnary rUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed sealUnary hUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary cUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row B ∨ hsame row W ∨ hsame row DA ∨ hsame row DB ∨
              hsame row J ∨ hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A W selectedRead ∧ Cont selectedRead DA S ∧
              Cont S R readbackRead ∧ Cont readbackRead E sealRead ∧
                Cont sealRead H transportRead ∧ Cont transportRead C replayRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead ⟨hsame_refl replayRead, replayUnary⟩
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
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr source.left))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, selectedRoute, selectedCommit, readbackRoute, sealRoute,
          transportRoute, replayRoute⟩
  }
  exact ⟨cert, selectedUnary, readbackUnary, sealUnary, transportUnary, replayUnary⟩

end BEDC.Derived.RegularCauchyMinUp
