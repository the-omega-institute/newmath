import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive SemidecidableOpenUp : Type where
  | mk
      (classifier topology streamWindow regSeqReadback realSeal transport replay provenance
        name : BHist) :
      SemidecidableOpenUp
  deriving DecidableEq

end BEDC.Derived
