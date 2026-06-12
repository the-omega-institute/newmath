import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive DarbouxOscillationUp : Type where
  | mk
      (partition mesh upper lower oscillation realSeal transport replay provenance name : BHist) :
      DarbouxOscillationUp
  deriving DecidableEq

end BEDC.Derived
