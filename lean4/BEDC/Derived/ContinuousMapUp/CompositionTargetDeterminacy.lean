import BEDC.Derived.ContinuousMapUp

namespace BEDC.Derived.ContinuousMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuousMapCarrier_comp_target_cert_distance_deterministic
    {source mid target target2 mapF mapG mapFG modF modG modFG certF certG certFG certFG2
      distF distG displayed : BHist} :
    ContinuousMapCarrier source mapF mid modF certF distF ->
      ContinuousMapCarrier mid mapG target modG certG distG ->
        Cont mapF mapG mapFG ->
          Cont modF modG modFG ->
            Cont target modFG certFG ->
              ContinuousMapCarrier source mapFG target2 modFG certFG2 displayed ->
                hsame target target2 ∧ hsame certFG certFG2 ∧
                  hsame displayed (append source target) ∧
                    Cont source target (append source target) := by
  intro first second graphRel modulusRel certRel displayedCarrier
  have canonical :
      ContinuousMapCarrier source mapFG target modFG certFG (append source target) :=
    ContinuousMapCarrier_comp_closed first second graphRel modulusRel certRel
  have deterministic :=
    ContinuousMapCarrier_target_cert_distance_deterministic canonical displayedCarrier
  exact And.intro deterministic.left
    (And.intro deterministic.right.left
      (And.intro (hsame_symm deterministic.right.right.left) deterministic.right.right.right))

end BEDC.Derived.ContinuousMapUp
