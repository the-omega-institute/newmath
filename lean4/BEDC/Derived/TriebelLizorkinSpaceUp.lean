import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive TriebelLizorkinSpaceUp : Type where
  | mk
      (sobolev holder weakDerivative dyadic regularRational realSeal windowSchedule
        localPosition mixedAggregation besovComparison transport replay provenance localName :
          BHist) :
      TriebelLizorkinSpaceUp
  deriving DecidableEq

end BEDC.Derived
