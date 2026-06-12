import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RegularSequenceBishopUp : Type where
  | mk (W D Q R N : BHist) : RegularSequenceBishopUp
  deriving DecidableEq

end BEDC.Derived
