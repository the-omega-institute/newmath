import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def SheafRootExportSurface
    (ambient member overlap route germ point openHist sectionHist endpoint : BHist) :
    Prop :=
  SheafBHistCoverNerveLedger ambient member overlap route germ ∧
    SheafBHistPointGermLedger point openHist sectionHist endpoint ∧
      Cont overlap route germ ∧ Cont openHist sectionHist endpoint

theorem SheafRootExportSurface_carrier_rows
    {ambient member overlap route germ point openHist sectionHist endpoint : BHist} :
    SheafRootExportSurface ambient member overlap route germ point openHist sectionHist
        endpoint ->
      UnaryHistory ambient ∧ UnaryHistory member ∧ UnaryHistory overlap ∧
        UnaryHistory point ∧ UnaryHistory openHist ∧ Cont overlap route germ ∧
          Cont openHist sectionHist endpoint := by
  intro surface
  exact And.intro surface.left.left
    (And.intro surface.left.right.left
      (And.intro surface.left.right.right.left
        (And.intro surface.right.left.left
          (And.intro surface.right.left.right.left
            (And.intro surface.right.right.left surface.right.right.right)))))

end BEDC.Derived.SheafUp
