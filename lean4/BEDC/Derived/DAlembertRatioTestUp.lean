import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive DAlembertRatioTestUp : Type where
  | mk
      (series adjacentTerms ratioBound rationalMargin dyadicLedger streamWindows regularReadback
        cauchyHandoff realSeal transport replay provenance localName : BHist) :
        DAlembertRatioTestUp
  deriving DecidableEq

end BEDC.Derived
