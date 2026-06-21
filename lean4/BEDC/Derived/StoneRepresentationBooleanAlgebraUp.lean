import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive StoneRepresentationBooleanAlgebraUp : Type where
  | mk (B U T L M H C P N : BHist) : StoneRepresentationBooleanAlgebraUp
  deriving DecidableEq

end BEDC.Derived
