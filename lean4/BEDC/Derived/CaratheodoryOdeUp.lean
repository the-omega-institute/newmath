import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CaratheodoryOdeUp : Type where
  | mk (O T S M A R E H C P N : BHist) : CaratheodoryOdeUp

end BEDC.Derived
