import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive SequentialPrecompactUp : Type where
  | mk
      (source finiteNet streamWindow readback realSeal transport replay provenance localName :
        BHist) :
      SequentialPrecompactUp
  deriving DecidableEq

end BEDC.Derived
