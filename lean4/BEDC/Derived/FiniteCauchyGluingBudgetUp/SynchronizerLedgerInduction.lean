import BEDC.Derived.FiniteCauchyGluingBudgetUp.TasteGate

namespace BEDC.Derived.FiniteCauchyGluingBudgetUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem FiniteCauchyGluingBudgetCarrier_synchronizer_ledger_induction
    {G L S U V N T K D R H _C _P publicRead : BHist} :
    UnaryHistory G →
      UnaryHistory L →
        UnaryHistory S →
          UnaryHistory U →
            UnaryHistory V →
              UnaryHistory N →
                hsame H (append G L) →
                  Cont G L T →
                    Cont T S K →
                      Cont K U D →
                        Cont D V R →
                          Cont R N publicRead →
                            hsame publicRead
                                (append (append (append (append (append G L) S) U) V) N) ∧
                              UnaryHistory T ∧
                                UnaryHistory K ∧
                                  UnaryHistory D ∧
                                    UnaryHistory R ∧
                                      UnaryHistory publicRead ∧ hsame H (append G L) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro unaryG unaryL unaryS unaryU unaryV unaryN sameH routeGL routeTS routeKU routeDV routeRN
  have unaryT : UnaryHistory T :=
    unary_cont_closed unaryG unaryL routeGL
  have unaryK : UnaryHistory K :=
    unary_cont_closed unaryT unaryS routeTS
  have unaryD : UnaryHistory D :=
    unary_cont_closed unaryK unaryU routeKU
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryD unaryV routeDV
  have unaryPublic : UnaryHistory publicRead :=
    unary_cont_closed unaryR unaryN routeRN
  have publicExact :
      hsame publicRead (append (append (append (append (append G L) S) U) V) N) := by
    cases routeGL
    cases routeTS
    cases routeKU
    cases routeDV
    cases routeRN
    rfl
  exact ⟨publicExact, unaryT, unaryK, unaryD, unaryR, unaryPublic, sameH⟩

end BEDC.Derived.FiniteCauchyGluingBudgetUp
