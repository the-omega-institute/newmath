import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem SheafBHistPointGermLedger_section_scope
    {point openHist sectionHist germ : BHist} :
    SheafBHistPointGermLedger point openHist sectionHist germ ->
      UnaryHistory sectionHist ->
        UnaryHistory point ∧ UnaryHistory openHist ∧ UnaryHistory sectionHist ∧
          UnaryHistory germ ∧ Cont openHist sectionHist germ := by
  intro ledger sectionUnary
  have germUnary : UnaryHistory germ :=
    unary_cont_closed ledger.right.left sectionUnary ledger.right.right
  exact And.intro ledger.left
    (And.intro ledger.right.left
      (And.intro sectionUnary
        (And.intro germUnary ledger.right.right)))

end BEDC.Derived.SheafUp
