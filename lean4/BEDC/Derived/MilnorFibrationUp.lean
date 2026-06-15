import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive MilnorFibrationUp : Type where
  | mk (X U S F B E H L T R P N : BHist) : MilnorFibrationUp
  deriving DecidableEq

end BEDC.Derived
