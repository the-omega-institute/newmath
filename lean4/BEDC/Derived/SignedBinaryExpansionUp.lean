import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive SignedBinaryExpansionUp : Type where
  | mk (Q B U D W E Y R L H C P N : BHist) : SignedBinaryExpansionUp
  deriving DecidableEq

end BEDC.Derived
