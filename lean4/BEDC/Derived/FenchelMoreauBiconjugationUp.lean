import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive FenchelMoreauBiconjugationUp : Type where
  | mk (F V K D E L S H C P N : BHist) : FenchelMoreauBiconjugationUp
  deriving DecidableEq

end BEDC.Derived
