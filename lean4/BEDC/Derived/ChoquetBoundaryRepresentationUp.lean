import BEDC.FKernel.Hist

open BEDC.FKernel.Hist

namespace BEDC
namespace Derived

inductive ChoquetBoundaryRepresentationUp : Type where
  | mk (K V L B M A E H C P N : BHist) : ChoquetBoundaryRepresentationUp
  deriving DecidableEq

end Derived
end BEDC
