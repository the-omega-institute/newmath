import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem SheafBHistPointGermComparison_reflexive {point openHist sect germ : BHist} :
    SheafBHistPointGermLedger point openHist sect germ ->
      SheafBHistPointGermComparison point openHist sect germ openHist sect germ
          openHist ∧
        Cont openHist sect germ ∧ UnaryHistory openHist := by
  intro ledger
  have comparison :
      SheafBHistPointGermComparison point openHist sect germ openHist sect germ
        openHist :=
    And.intro ledger.left
      (And.intro ledger.right.left
        (And.intro ledger.right.left
          (And.intro ledger.right.left
            (And.intro (hsame_refl openHist)
              (And.intro (hsame_refl openHist)
                (And.intro ledger.right.right
                  (And.intro ledger.right.right (hsame_refl germ))))))))
  exact And.intro comparison (And.intro ledger.right.right ledger.right.left)

end BEDC.Derived.SheafUp
