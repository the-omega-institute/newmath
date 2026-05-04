import BEDC.Derived.PrimeUp

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem NatDivides_cont_closed {d x y z : BHist} :
    NatDivides d x → NatDivides d y → Cont x y z → NatDivides d z := by
  intro dividesX dividesY continuation
  cases dividesX with
  | intro qx qxData =>
      cases qxData with
      | intro qxUnary qxMul =>
          cases dividesY with
          | intro qy qyData =>
              cases qyData with
              | intro qyUnary qyMul =>
                  exact Exists.intro (append qx qy)
                    (And.intro (unary_append_closed qxUnary qyUnary)
                      (NatMul_append_cont qxMul qyMul continuation))

end BEDC.Derived.PrimeUp
