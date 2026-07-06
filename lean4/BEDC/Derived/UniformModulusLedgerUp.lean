import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive UniformModulusLedgerUp : Type where
  | mk (K F R B T U H C P N : BHist) : UniformModulusLedgerUp
  deriving DecidableEq

end BEDC.Derived
