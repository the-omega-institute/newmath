import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive SignedDigitRedundancyUp : Type where
  | mk (S B U D W Q R E H C P N : BHist) : SignedDigitRedundancyUp
  deriving DecidableEq

end BEDC.Derived
