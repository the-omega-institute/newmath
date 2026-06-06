import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive BertrandTestUp : Type where
  | mk (S Q L D T W R E H C P N : BHist) : BertrandTestUp
  deriving DecidableEq

end BEDC.Derived
