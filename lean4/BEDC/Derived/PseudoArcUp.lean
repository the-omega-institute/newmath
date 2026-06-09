import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive PseudoArcUp : Type where
  | mk
      (compactMetric inverseLimit chainability hereditaryIndecomposable readback realSeal transport replay
        provenance name : BHist) :
      PseudoArcUp
  deriving DecidableEq

end BEDC.Derived
