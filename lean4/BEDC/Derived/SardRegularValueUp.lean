import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive SardRegularValueUp : Type where
  | mk (M F D J V E H C P N : BHist) : SardRegularValueUp

end BEDC.Derived
