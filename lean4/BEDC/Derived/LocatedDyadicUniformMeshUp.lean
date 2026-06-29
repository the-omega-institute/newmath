import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive LocatedDyadicUniformMeshUp : Type where
  | mk
      (intervalNet endpointEvidence toleranceReadback streamRows realSeal transport replay
        provenance localName : BHist) :
      LocatedDyadicUniformMeshUp
  deriving DecidableEq

end BEDC.Derived
