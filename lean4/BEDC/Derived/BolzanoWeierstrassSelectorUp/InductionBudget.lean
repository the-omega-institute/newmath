import BEDC.Derived.BolzanoWeierstrassSelectorUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.BolzanoWeierstrassSelectorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def BolzanoWeierstrassSelectorInductionBudget (B M Q W : BHist) : Prop :=
  UnaryHistory B ∧ UnaryHistory M ∧ UnaryHistory Q ∧ UnaryHistory W ∧
    ∃ selectedRead : BHist, Cont B M selectedRead ∧ Cont selectedRead Q W

theorem BolzanoWeierstrassSelectorInductionBudget_selected_window_route
    {B M Q W selectedRead : BHist} :
    Cont B M selectedRead ->
      Cont selectedRead Q W ->
        UnaryHistory B ->
          UnaryHistory M ->
            UnaryHistory Q ->
              BolzanoWeierstrassSelectorInductionBudget B M Q W ∧
                UnaryHistory selectedRead ∧ UnaryHistory W ∧ Cont B M selectedRead ∧
                  Cont selectedRead Q W := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro selectedRoute windowRoute unaryB unaryM unaryQ
  have selectedUnary : UnaryHistory selectedRead :=
    unary_cont_closed unaryB unaryM selectedRoute
  have windowUnary : UnaryHistory W :=
    unary_cont_closed selectedUnary unaryQ windowRoute
  exact
    ⟨⟨unaryB, unaryM, unaryQ, windowUnary, selectedRead, selectedRoute, windowRoute⟩,
      selectedUnary, windowUnary, selectedRoute, windowRoute⟩

end BEDC.Derived.BolzanoWeierstrassSelectorUp
