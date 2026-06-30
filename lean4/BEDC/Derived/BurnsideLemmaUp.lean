import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive BurnsideLemmaUp : Type where
  | mk (G X A L F O K H C P N : BHist) : BurnsideLemmaUp
  deriving DecidableEq

end BEDC.Derived
