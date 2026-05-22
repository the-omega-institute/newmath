import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CompleteArchimedeanFieldUp : Type where
  | mk (R O A D W Q K H C P N : BHist) : CompleteArchimedeanFieldUp
  deriving DecidableEq

end BEDC.Derived
