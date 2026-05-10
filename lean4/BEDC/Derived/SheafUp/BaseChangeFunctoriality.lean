import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

def SheafComposableBaseChangeSquares
    (first second composite cover pulledFirst pulledSecond route : BHist) : Prop :=
  SheafBHistCoverNerveLedger first cover pulledFirst route composite ∧
    SheafBHistCoverNerveLedger second pulledFirst pulledSecond route composite ∧
      Cont first second composite ∧ Cont pulledFirst pulledSecond composite

theorem SheafComposableBaseChangeSquares_rows
    {first second composite cover pulledFirst pulledSecond route : BHist} :
    SheafComposableBaseChangeSquares first second composite cover pulledFirst pulledSecond route ->
      SheafBHistCoverNerveLedger first cover pulledFirst route composite ∧
        SheafBHistCoverNerveLedger second pulledFirst pulledSecond route composite ∧
          Cont first second composite ∧ Cont pulledFirst pulledSecond composite := by
  intro squares
  exact squares

end BEDC.Derived.SheafUp
