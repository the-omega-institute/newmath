import BEDC.Derived.FinitePrefixLimitStabilityUp.TasteGate

namespace BEDC.Derived.FinitePrefixLimitStabilityUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Meta.TasteGate

theorem FinitePrefixLimitStabilityCarrier_budget_window_lock
    {B W R D E H C P N BW WR : BHist} :
    UnaryHistory B → UnaryHistory W → UnaryHistory R → Cont B W BW →
      Cont BW R WR →
        FieldFaithful.fields (FinitePrefixLimitStabilityUp.packet B W R D E H C P N) =
            [B, W, R, D, E, H, C, P, N] ∧
          UnaryHistory BW ∧ UnaryHistory WR := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory FieldFaithful
  intro unaryB unaryW unaryR budgetWindow windowReadback
  have budgetWindowUnary : UnaryHistory BW :=
    unary_cont_closed unaryB unaryW budgetWindow
  have windowReadbackUnary : UnaryHistory WR :=
    unary_cont_closed budgetWindowUnary unaryR windowReadback
  exact ⟨rfl, budgetWindowUnary, windowReadbackUnary⟩

end BEDC.Derived.FinitePrefixLimitStabilityUp
