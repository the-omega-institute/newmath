import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive SubspaceTopologyUniformityUp : Type where
  | mk
      (topology admission relativeOpen locatedUniform restrictedEntourage metricComparison
        realSeal transport replay provenance localNameCert : BHist) :
      SubspaceTopologyUniformityUp

end BEDC.Derived
