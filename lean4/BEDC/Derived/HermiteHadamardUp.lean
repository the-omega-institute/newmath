import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive HermiteHadamardUp : Type where
  | mk
      (function interval midpoint average jensen karamata comparison endpoint transport replay
        provenance name : BHist) :
      HermiteHadamardUp
  deriving DecidableEq

end BEDC.Derived
