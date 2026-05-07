import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def SheafRootExportBHistClosureSurface
    (root ambient member overlap route germ point openHist sectionHist : BHist) : Prop :=
  UnaryHistory root ∧ UnaryHistory ambient ∧ UnaryHistory member ∧ UnaryHistory overlap ∧
    Cont overlap route germ ∧ Cont openHist sectionHist germ ∧
      SheafConsumerAccessTrace root [ambient, member, overlap] ∧
        SheafBHistCoverNerveLedger ambient member overlap route germ ∧
          SheafBHistPointGermLedger point openHist sectionHist germ

theorem SheafRootExportBHistClosureSurface_rows
    {root ambient member overlap route germ point openHist sectionHist : BHist} :
    SheafRootExportBHistClosureSurface root ambient member overlap route germ point openHist
        sectionHist ->
      UnaryHistory root ∧ UnaryHistory ambient ∧ UnaryHistory member ∧
        UnaryHistory overlap ∧ UnaryHistory point ∧ UnaryHistory openHist ∧
          Cont overlap route germ ∧ Cont openHist sectionHist germ ∧
            SheafConsumerAccessTrace root [ambient, member, overlap] ∧
              SheafBHistCoverNerveLedger ambient member overlap route germ ∧
                SheafBHistPointGermLedger point openHist sectionHist germ := by
  intro surface
  have traceRows : SheafConsumerAccessTrace root [ambient, member, overlap] :=
    surface.right.right.right.right.right.right.left
  have coverLedger : SheafBHistCoverNerveLedger ambient member overlap route germ :=
    surface.right.right.right.right.right.right.right.left
  have pointLedger : SheafBHistPointGermLedger point openHist sectionHist germ :=
    surface.right.right.right.right.right.right.right.right
  exact And.intro surface.left
    (And.intro surface.right.left
      (And.intro surface.right.right.left
        (And.intro surface.right.right.right.left
          (And.intro pointLedger.left
            (And.intro pointLedger.right.left
              (And.intro surface.right.right.right.right.left
                (And.intro surface.right.right.right.right.right.left
                  (And.intro traceRows
                    (And.intro coverLedger pointLedger)))))))))

end BEDC.Derived.SheafUp
