import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CousinLemmaUp : Type where
  | mk (I G T M W R E H C P N : BHist) : CousinLemmaUp
  deriving DecidableEq

end BEDC.Derived
