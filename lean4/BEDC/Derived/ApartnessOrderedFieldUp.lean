import BEDC.FKernel.Hist

namespace BEDC.Derived

inductive ApartnessOrderedFieldUp : Type where
  | mk
      (real apartness order algebra transport replay provenance name :
        _root_.BEDC.FKernel.Hist.BHist) :
      ApartnessOrderedFieldUp

end BEDC.Derived
