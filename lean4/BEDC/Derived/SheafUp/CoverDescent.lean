import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem SheafRootCoverDescent_carrier_exactness
    {ambient member overlap route germ : BHist} :
    SheafBHistCoverNerveLedger ambient member overlap route germ ->
      SheafRootFaceRead member overlap .coverMembership ∧
        SheafRootFaceRead overlap germ .restrictionRoute ∧
          UnaryHistory ambient ∧ UnaryHistory member ∧ UnaryHistory overlap := by
  intro ledger
  exact And.intro
    (SheafRootFaceRead.coverMembership (hsame_symm ledger.right.right.right.left))
    (And.intro
      (SheafRootFaceRead.restrictionRoute ledger.right.right.right.right)
      (And.intro ledger.left
        (And.intro ledger.right.left ledger.right.right.left)))

end BEDC.Derived.SheafUp
