import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive DyadicTentFunctionUp : Type where
  | mk
      (center support height leftSlope rightSlope endpointRows
        dyadicReadback transport replay package name : BHist) :
      DyadicTentFunctionUp
  deriving DecidableEq

end BEDC.Derived
