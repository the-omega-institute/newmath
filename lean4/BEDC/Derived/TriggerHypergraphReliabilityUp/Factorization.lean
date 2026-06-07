import BEDC.Derived.TriggerHypergraphReliabilityUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.TriggerHypergraphReliabilityUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem TriggerHypergraphReliabilityFactorization
    {B E R L W D A _H _C _P N edgeRead budgetRead tagRead windowRead toleranceRead
      algebraRead namedRead : BHist} :
    UnaryHistory B →
      UnaryHistory E →
        UnaryHistory R →
          UnaryHistory L →
            UnaryHistory W →
              UnaryHistory D →
                UnaryHistory A →
                  UnaryHistory N →
                    Cont B E edgeRead →
                      Cont edgeRead R budgetRead →
                        Cont budgetRead L tagRead →
                          Cont tagRead W windowRead →
                            Cont windowRead D toleranceRead →
                              Cont toleranceRead A algebraRead →
                                Cont algebraRead N namedRead →
                                  UnaryHistory edgeRead ∧ UnaryHistory budgetRead ∧
                                    UnaryHistory tagRead ∧ UnaryHistory windowRead ∧
                                      UnaryHistory toleranceRead ∧ UnaryHistory algebraRead ∧
                                        UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro unaryB unaryE unaryR unaryL unaryW unaryD unaryA unaryN edgeRoute budgetRoute
    tagRoute windowRoute toleranceRoute algebraRoute namedRoute
  have edgeUnary : UnaryHistory edgeRead :=
    unary_cont_closed unaryB unaryE edgeRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed edgeUnary unaryR budgetRoute
  have tagUnary : UnaryHistory tagRead :=
    unary_cont_closed budgetUnary unaryL tagRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed tagUnary unaryW windowRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed windowUnary unaryD toleranceRoute
  have algebraUnary : UnaryHistory algebraRead :=
    unary_cont_closed toleranceUnary unaryA algebraRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed algebraUnary unaryN namedRoute
  exact
    ⟨edgeUnary, budgetUnary, tagUnary, windowUnary, toleranceUnary, algebraUnary,
      namedUnary⟩

end BEDC.Derived.TriggerHypergraphReliabilityUp
