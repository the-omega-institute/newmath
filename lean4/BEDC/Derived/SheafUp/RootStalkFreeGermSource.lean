import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

inductive SheafRootStalkFreeGermSource : BHist -> BHist -> BHist -> BHist -> BHist -> Prop where
  | row {point openHist sectionHist germ source : BHist} :
      SheafBHistPointGermLedger point openHist sectionHist germ ->
        Cont point germ source ->
          SheafRootStalkFreeGermSource point openHist sectionHist germ source

theorem SheafRootStalkFreeGermSource_point_germ_readback
    {point openHist sectionHist germ source : BHist} :
    SheafRootStalkFreeGermSource point openHist sectionHist germ source ->
      SheafBHistPointGermLedger point openHist sectionHist germ ∧
        UnaryHistory point ∧ UnaryHistory openHist ∧ Cont point germ source := by
  intro sourceRow
  cases sourceRow with
  | row ledger pointGerm =>
      exact And.intro ledger
        (And.intro ledger.left
          (And.intro ledger.right.left pointGerm))

end BEDC.Derived.SheafUp
