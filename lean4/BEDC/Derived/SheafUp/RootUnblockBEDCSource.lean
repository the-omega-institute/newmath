import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def SheafRootUnblockBEDCSource
    (ambient member overlap route germ sectionHist restrictedGerm : BHist) : Prop :=
  SheafBHistCoverNerveLedger ambient member overlap route germ ∧
    SheafBHistPointGermLedger ambient member sectionHist restrictedGerm ∧
      hsame overlap member ∧ Cont member sectionHist restrictedGerm

theorem SheafRootUnblockBEDCSource_rows
    {ambient member overlap route germ sectionHist restrictedGerm : BHist} :
    SheafRootUnblockBEDCSource ambient member overlap route germ sectionHist restrictedGerm ->
      SheafBHistCoverNerveLedger ambient member overlap route germ ∧
        SheafBHistPointGermLedger ambient member sectionHist restrictedGerm ∧
          UnaryHistory member ∧ hsame overlap member ∧
            Cont member sectionHist restrictedGerm := by
  intro source
  exact And.intro source.left
    (And.intro source.right.left
      (And.intro source.left.right.left
        (And.intro source.right.right.left source.right.right.right)))

end BEDC.Derived.SheafUp
