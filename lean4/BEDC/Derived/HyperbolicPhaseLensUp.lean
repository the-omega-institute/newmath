import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive HyperbolicPhaseLensUp : Type where
  | mk (B U V D R W H C P N : BHist) : HyperbolicPhaseLensUp

end BEDC.Derived
