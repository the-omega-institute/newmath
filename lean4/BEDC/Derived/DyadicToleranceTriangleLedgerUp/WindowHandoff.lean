import BEDC.Derived.DyadicToleranceTriangleLedgerUp.TasteGate
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.DyadicToleranceTriangleLedgerUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DyadicToleranceTriangleLedger_window_handoff
    {Dm Dn Im In Em En M Q T H C P N endpoint realRead : BHist} :
    DyadicToleranceTriangleLedgerUp →
      UnaryHistory Q →
        UnaryHistory C →
          UnaryHistory P →
            Cont Q C endpoint →
              Cont endpoint P realRead →
                UnaryHistory endpoint ∧
                  UnaryHistory realRead ∧
                    Cont Q C endpoint ∧
                      Cont endpoint P realRead ∧
                        List.Mem (dyadicToleranceTriangleLedgerEncodeBHist Q)
                          (dyadicToleranceTriangleLedgerToEventFlow
                            (DyadicToleranceTriangleLedgerUp.mk
                              Dm Dn Im In Em En M Q T H C P N)) := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory BMark
  intro _carrier unaryQ unaryC unaryP endpointRoute realRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed unaryQ unaryC endpointRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed endpointUnary unaryP realRoute
  exact
    ⟨endpointUnary, realUnary, endpointRoute, realRoute, by
      simp only [dyadicToleranceTriangleLedgerToEventFlow]
      exact
        List.Mem.tail _ <|
          List.Mem.tail _ <|
            List.Mem.tail _ <|
              List.Mem.tail _ <|
                List.Mem.tail _ <|
                  List.Mem.tail _ <|
                    List.Mem.tail _ <|
                      List.Mem.tail _ <|
                        List.Mem.head _⟩

end BEDC.Derived.DyadicToleranceTriangleLedgerUp
