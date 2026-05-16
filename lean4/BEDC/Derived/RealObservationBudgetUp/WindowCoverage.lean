import BEDC.Derived.RealObservationBudgetUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealObservationBudgetUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RealObservationBudgetWindowCoverage
    {E W D R S H C P N windowRead dyadicRead : BHist} :
    RealObservationBudgetUp →
      UnaryHistory E →
        UnaryHistory W →
          UnaryHistory D →
            Cont E W windowRead →
              Cont windowRead D dyadicRead →
                UnaryHistory windowRead ∧ UnaryHistory dyadicRead ∧
                  Cont E W windowRead ∧ Cont windowRead D dyadicRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory BEDC.Derived.RealObservationBudgetUp
  intro packet unaryE unaryW unaryD windowRoute dyadicRoute
  cases packet with
  | mk E₀ W₀ D₀ R₀ S₀ H₀ C₀ P₀ N₀ =>
      have windowUnary : UnaryHistory windowRead :=
        unary_cont_closed unaryE unaryW windowRoute
      have dyadicUnary : UnaryHistory dyadicRead :=
        unary_cont_closed windowUnary unaryD dyadicRoute
      exact ⟨windowUnary, dyadicUnary, windowRoute, dyadicRoute⟩

end BEDC.Derived.RealObservationBudgetUp
