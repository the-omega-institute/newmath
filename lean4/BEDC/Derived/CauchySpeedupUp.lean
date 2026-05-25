import BEDC.FKernel.Hist

namespace BEDC
namespace Derived

inductive CauchySpeedupUp : Type
| mk (A J D W R E H C P N : BEDC.FKernel.Hist.BHist) : CauchySpeedupUp
  deriving DecidableEq

end Derived
end BEDC
