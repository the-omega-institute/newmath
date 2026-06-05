import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RegularExpressionUp : Type where
  | mk (Sigma E L U C K H T P N : BHist) : RegularExpressionUp
  deriving DecidableEq

end BEDC.Derived
