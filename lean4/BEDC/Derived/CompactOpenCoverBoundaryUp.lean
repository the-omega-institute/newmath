import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CompactOpenCoverBoundaryUp : Type where
  | mk :
      (compactMetric finiteCoverRequest finiteEpsilonNetWitness radiusLedger uniformModulusHandoff
        transport replay provenance localName : BHist) →
        CompactOpenCoverBoundaryUp
  deriving DecidableEq

end BEDC.Derived
