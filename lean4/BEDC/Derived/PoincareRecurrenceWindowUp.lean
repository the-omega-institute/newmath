import BEDC.FKernel.Hist

open BEDC.FKernel.Hist

namespace BEDC
namespace Derived

inductive PoincareRecurrenceWindowUp : Type where
  | mk (D E P M A I T H C Q N : BHist) : PoincareRecurrenceWindowUp
  deriving DecidableEq

end Derived
end BEDC
