import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive HenstockGaugePartitionUp : Type where
  | mk
      (interval gauge taggedIntervals endpointReadback fineness coverage disjointness
        contReplay provenance name : BHist) :
      HenstockGaugePartitionUp

end BEDC.Derived
