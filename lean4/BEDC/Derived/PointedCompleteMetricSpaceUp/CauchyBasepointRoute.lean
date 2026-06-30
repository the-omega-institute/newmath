import BEDC.Derived.PointedCompleteMetricSpaceUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.PointedCompleteMetricSpaceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem PointedCompleteMetricSpaceCauchyBasepointRoute
    {M B Q S R E L H C P0 N cauchyRead streamRead ratRead realRead completionRead
      localRead : BHist} :
    UnaryHistory M ->
      UnaryHistory B ->
        UnaryHistory Q ->
          UnaryHistory S ->
            UnaryHistory R ->
              UnaryHistory E ->
                UnaryHistory L ->
                  UnaryHistory H ->
                    UnaryHistory C ->
                      Cont B Q cauchyRead ->
                        Cont cauchyRead S streamRead ->
                          Cont streamRead R ratRead ->
                            Cont ratRead E realRead ->
                              Cont realRead L completionRead ->
                                Cont H C localRead ->
                                  UnaryHistory cauchyRead ∧
                                    UnaryHistory streamRead ∧
                                      UnaryHistory ratRead ∧
                                        UnaryHistory realRead ∧
                                          UnaryHistory completionRead ∧
                                            UnaryHistory localRead ∧
                                              pointedCompleteMetricSpaceFields
                                                  (PointedCompleteMetricSpaceUp.mk
                                                    M B Q S R E L H C P0 N) =
                                                [M, B, Q, S, R, E, L, H, C, P0, N] := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory PointedCompleteMetricSpaceUp
  intro _mUnary bUnary qUnary sUnary rUnary eUnary lUnary hUnary cUnary cauchyRoute
    streamRoute ratRoute realRoute completionRoute localRoute
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed bUnary qUnary cauchyRoute
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed cauchyUnary sUnary streamRoute
  have ratUnary : UnaryHistory ratRead :=
    unary_cont_closed streamUnary rUnary ratRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed ratUnary eUnary realRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed realUnary lUnary completionRoute
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed hUnary cUnary localRoute
  exact
    ⟨cauchyUnary, streamUnary, ratUnary, realUnary, completionUnary, localUnary, rfl⟩

end BEDC.Derived.PointedCompleteMetricSpaceUp
