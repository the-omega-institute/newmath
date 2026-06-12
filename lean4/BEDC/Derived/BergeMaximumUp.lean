import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive BergeMaximumUp : Type where
  | packet
      (parameter feasibleGraph objective valueWindow maximumComparison transport replay provenance
        localName : BHist) :
      BergeMaximumUp
  deriving DecidableEq

end BEDC.Derived
