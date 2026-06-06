import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive FilterSubbasisCofinalCompletionUp : Type where
  | mk
      (subbasis generatedBase cauchyFilter window readback realSeal transport replay provenance
        name : BHist) :
      FilterSubbasisCofinalCompletionUp
  deriving DecidableEq

end BEDC.Derived
