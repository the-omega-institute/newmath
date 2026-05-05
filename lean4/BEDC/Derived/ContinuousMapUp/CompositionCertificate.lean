import BEDC.Derived.ContinuousMapUp

namespace BEDC.Derived.ContinuousMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuousMapCarrier_comp_certificate_deterministic
    {source mid target mapF mapG mapFG modF modG modFG certF certG certFG certFG2 distF
      distG displayed : BHist} :
    ContinuousMapCarrier source mapF mid modF certF distF ->
      ContinuousMapCarrier mid mapG target modG certG distG ->
        Cont mapF mapG mapFG ->
          Cont modF modG modFG ->
            Cont target modFG certFG ->
              ContinuousMapCarrier source mapFG target modFG certFG2 displayed ->
                hsame certFG certFG2 := by
  intro first second graphRel modulusRel certRel displayedCarrier
  have canonical :
      ContinuousMapCarrier source mapFG target modFG certFG (append source target) :=
    ContinuousMapCarrier_comp_closed first second graphRel modulusRel certRel
  exact
    (ContinuousMapCarrier_target_cert_distance_deterministic canonical
      displayedCarrier).right.left

end BEDC.Derived.ContinuousMapUp
