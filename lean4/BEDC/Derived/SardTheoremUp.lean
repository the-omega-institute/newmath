import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive SardTheoremUp : Type where
  | mk (M J R V E H C P N : BHist) : SardTheoremUp

end BEDC.Derived
