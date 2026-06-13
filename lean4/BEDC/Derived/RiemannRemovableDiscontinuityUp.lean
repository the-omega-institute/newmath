import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RiemannRemovableDiscontinuityUp : Type where
  | mk
      (defect offDefect approach windows readback realSeal handoff transport replay provenance
        localName : BHist) :
      RiemannRemovableDiscontinuityUp

end BEDC.Derived
