import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive AlgebraicExpressionLedgerUp : Type where
  | mk : (e o a u s h c p n : BHist) → AlgebraicExpressionLedgerUp
  deriving DecidableEq

end BEDC.Derived
