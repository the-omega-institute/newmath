import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive SchreierSimsUp : Type where
  | mk
      (permutationSource groupSource orbitStabilizerSource finiteActionSource
        baseRow transversalLedger schreierGeneratorRow siftTrace transport replay
        provenance localNameCert : BHist) :
      SchreierSimsUp
  deriving DecidableEq

end BEDC.Derived
