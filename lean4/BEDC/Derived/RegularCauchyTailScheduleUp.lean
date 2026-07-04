import BEDC.Derived.RegularCauchyTailScheduleUp.TasteGate

namespace BEDC.Derived.RegularCauchyTailScheduleUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

def RegularCauchyTailSchedule_handoff_route
    (Q R W D K T M F E H C P N route tailRead meetRead fusionRead sealRead : BHist) :
    Prop :=
  -- BEDC touchpoint anchor: BHist Cont
  Cont Q R route ∧ Cont route W tailRead ∧ Cont tailRead M meetRead ∧
    Cont meetRead F fusionRead ∧ Cont fusionRead E sealRead

end BEDC.Derived.RegularCauchyTailScheduleUp
