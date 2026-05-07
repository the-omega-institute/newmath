import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def SheafIdentityCoverRootPackage
    (point openHist sectionHist germ overlap route : BHist) : Prop :=
  SheafBHistPointGermLedger point openHist sectionHist germ ∧
    SheafBHistCoverNerveLedger openHist openHist overlap route germ ∧
      hsame overlap openHist ∧ hsame route BHist.Empty

theorem SheafIdentityCoverRootPackage_rows
    {point openHist sectionHist germ overlap route : BHist} :
    SheafIdentityCoverRootPackage point openHist sectionHist germ overlap route ->
      SheafBHistPointGermLedger point openHist sectionHist germ ∧
        SheafBHistCoverNerveLedger openHist openHist overlap route germ ∧
          hsame overlap openHist ∧ hsame route BHist.Empty ∧
            UnaryHistory point ∧ UnaryHistory openHist ∧ UnaryHistory overlap ∧
              Cont openHist sectionHist germ ∧ Cont overlap route germ := by
  intro package
  exact And.intro package.left
    (And.intro package.right.left
      (And.intro package.right.right.left
        (And.intro package.right.right.right
          (And.intro package.left.left
            (And.intro package.left.right.left
              (And.intro package.right.left.right.right.left
                (And.intro package.left.right.right
                  package.right.left.right.right.right.right)))))))

end BEDC.Derived.SheafUp
