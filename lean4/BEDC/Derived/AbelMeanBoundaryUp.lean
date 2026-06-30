import BEDC.FKernel.Hist

open BEDC.FKernel.Hist

namespace BEDC
namespace Derived

inductive AbelMeanBoundaryUp : Type where
  | mk (S A T U W D R E H C P N : BHist) : AbelMeanBoundaryUp
  deriving DecidableEq

end Derived
end BEDC
