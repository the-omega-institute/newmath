import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def SheafRootStalkFreeGermSource
    (point openHist sectionHist germ common route : BHist) : Prop :=
  SheafBHistPointGermLedger point openHist sectionHist germ ∧
    UnaryHistory common ∧ hsame common openHist ∧ Cont common sectionHist route ∧
      hsame route germ

end BEDC.Derived.SheafUp
