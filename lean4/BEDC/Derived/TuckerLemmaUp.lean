import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive TuckerLemmaUp : Type where
  | mk (T B L E H C P N : BHist) : TuckerLemmaUp

end BEDC.Derived
