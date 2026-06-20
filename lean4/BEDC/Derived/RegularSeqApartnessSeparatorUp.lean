import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RegularSeqApartnessSeparatorUp : Type where
  | mk
      (stream regular dyadic realSeal located apartness
        transport replay provenance name : BHist) :
      RegularSeqApartnessSeparatorUp
  deriving DecidableEq

end BEDC.Derived
