import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem SheafRootExport_carrier_scope
    {root ambient member overlap route germ point openHist sectionHist rootTail openTail : BHist}
    {trace : List BHist} :
    SheafConsumerAccessTrace root trace ->
      SheafBHistCoverNerveLedger ambient member overlap route germ ->
        SheafBHistPointGermLedger point openHist sectionHist germ ->
          UnaryHistory root ∧ UnaryHistory ambient ∧ UnaryHistory member ∧
            UnaryHistory overlap ∧ UnaryHistory point ∧ UnaryHistory openHist ∧
              Cont overlap route germ ∧ Cont openHist sectionHist germ ∧
                (hsame root (BHist.e0 rootTail) -> False) ∧
                  (hsame openHist (BHist.e0 openTail) -> False) := by
  intro traceRows coverLedger pointLedger
  have rootUnary : UnaryHistory root := traceRows.left
  have ambientUnary : UnaryHistory ambient := coverLedger.left
  have memberUnary : UnaryHistory member := coverLedger.right.left
  have overlapUnary : UnaryHistory overlap := coverLedger.right.right.left
  have coverRow : Cont overlap route germ := coverLedger.right.right.right.right
  have pointUnary : UnaryHistory point := pointLedger.left
  have openUnary : UnaryHistory openHist := pointLedger.right.left
  have pointRow : Cont openHist sectionHist germ := pointLedger.right.right
  have rootNotZero : hsame root (BHist.e0 rootTail) -> False := by
    intro sameRoot
    exact unary_no_zero_extension (unary_transport rootUnary sameRoot)
  have openNotZero : hsame openHist (BHist.e0 openTail) -> False := by
    intro sameOpen
    exact unary_no_zero_extension (unary_transport openUnary sameOpen)
  exact And.intro rootUnary
    (And.intro ambientUnary
      (And.intro memberUnary
        (And.intro overlapUnary
          (And.intro pointUnary
            (And.intro openUnary
              (And.intro coverRow
                (And.intro pointRow
                  (And.intro rootNotZero openNotZero))))))))

end BEDC.Derived.SheafUp
