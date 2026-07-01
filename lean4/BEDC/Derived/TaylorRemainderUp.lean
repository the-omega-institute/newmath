import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive TaylorRemainderUp : Type where
  | mk (D P W E Q S H C G N : BHist) : TaylorRemainderUp
  deriving DecidableEq

end BEDC.Derived
