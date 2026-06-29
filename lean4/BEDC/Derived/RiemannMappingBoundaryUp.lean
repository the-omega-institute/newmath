import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RiemannMappingBoundaryUp : Type where
  | mk
      (interior jordan circle compactWindow graph readback realSeal transport replay provenance
        name : BHist) :
      RiemannMappingBoundaryUp
  deriving DecidableEq

end BEDC.Derived
