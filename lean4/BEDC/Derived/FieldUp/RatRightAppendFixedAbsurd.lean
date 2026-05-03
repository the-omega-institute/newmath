import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem RatHistoryCarrier_right_append_fixed_absurd {h g : BHist} :
    RatHistoryCarrier h -> hsame (append h g) g -> False := by
  intro carrier fixed
  have leftEmpty : hsame h BHist.Empty :=
    cont_left_unit_unique (cont_intro fixed.symm)
  exact RatHistoryCarrier_not_empty carrier leftEmpty

end BEDC.Derived.FieldUp
