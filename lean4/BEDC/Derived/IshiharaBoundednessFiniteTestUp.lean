import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive IshiharaBoundednessFiniteTestUp : Type where
  | mk
      (sourceSequence finiteWindow lowerTest upperTest locatedSplit streamReadback
        regularReadback toleranceBudget realSeal transport replay provenance localName : BHist) :
      IshiharaBoundednessFiniteTestUp
  deriving DecidableEq

end BEDC.Derived
