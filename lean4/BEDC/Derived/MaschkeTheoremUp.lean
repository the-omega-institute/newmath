import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive MaschkeTheoremUp : Type where
  | mk (G V R X A Q H C P N : BHist) : MaschkeTheoremUp
  deriving DecidableEq

end BEDC.Derived
