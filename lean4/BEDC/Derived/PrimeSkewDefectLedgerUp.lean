import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive PrimeSkewDefectLedgerUp : Type where
  | mk (Z P B I F H C Q R N : BHist) : PrimeSkewDefectLedgerUp

end BEDC.Derived
