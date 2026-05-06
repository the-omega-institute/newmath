import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def SheafBHistPointGermLedger
    (point openHist sectionHist germ : BHist) : Prop :=
  UnaryHistory point ∧ UnaryHistory openHist ∧ Cont openHist sectionHist germ

theorem SheafBHistPointGermLedger_restriction_readback
    {point openHist sectionHist germ restrictedOpen restrictedGerm : BHist} :
    SheafBHistPointGermLedger point openHist sectionHist germ ->
      hsame openHist restrictedOpen ->
        Cont restrictedOpen sectionHist restrictedGerm ->
          SheafBHistPointGermLedger point restrictedOpen sectionHist restrictedGerm ∧
            hsame germ restrictedGerm := by
  intro ledger sameOpen restrictedRow
  cases sameOpen
  have restrictedOpenUnary : UnaryHistory openHist := ledger.right.left
  have sameGerm : hsame germ restrictedGerm :=
    cont_deterministic ledger.right.right restrictedRow
  exact And.intro
    (And.intro ledger.left (And.intro restrictedOpenUnary restrictedRow))
    sameGerm

end BEDC.Derived.SheafUp
