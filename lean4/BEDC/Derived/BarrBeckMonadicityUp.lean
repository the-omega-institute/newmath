import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive BarrBeckMonadicityUp : Type where
  | mk (A C D F U T E K X Q H R P N : BHist) : BarrBeckMonadicityUp
  deriving DecidableEq

end BEDC.Derived
