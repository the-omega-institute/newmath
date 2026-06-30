import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive BishopNestedClosedSetPrincipleUp : Type where
  | mk : (f i d q r a h c p n : BHist) -> BishopNestedClosedSetPrincipleUp
  deriving DecidableEq

end BEDC.Derived
