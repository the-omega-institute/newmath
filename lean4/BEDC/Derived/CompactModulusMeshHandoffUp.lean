import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CompactModulusMeshHandoffUp : Type where
  | mk
      (compactNet pointwiseModulus dyadicTolerance rationalFold uniformModulus realSeal
        transport replay provenance localName : BHist) :
      CompactModulusMeshHandoffUp
  deriving DecidableEq

end BEDC.Derived
