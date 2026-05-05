import BEDC.Derived.ContinuousUp

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuousFunctionCarrier_parallel_composite_determinacy
    {source middle target f g fg fg_prime modF modG modFG modFG_prime certF certG cert
      cert_prime : BHist} :
    ContinuousFunctionCarrier source f middle modF certF ->
      ContinuousFunctionCarrier middle g target modG certG ->
        Cont f g fg ->
          Cont f g fg_prime ->
            Cont modF modG modFG ->
              Cont modF modG modFG_prime ->
                Cont target modFG cert ->
                  Cont target modFG_prime cert_prime ->
                    ContinuousFunctionCarrier source fg target modFG cert ∧
                      ContinuousFunctionCarrier source fg_prime target modFG_prime cert_prime ∧
                        hsame fg fg_prime ∧ hsame modFG modFG_prime ∧
                          hsame cert cert_prime := by
  intro first second fgRel fgRel' modRel modRel' certRel certRel'
  have leftCarrier : ContinuousFunctionCarrier source fg target modFG cert :=
    ContinuousFunctionCarrier_comp_closed first second fgRel modRel certRel
  have rightCarrier : ContinuousFunctionCarrier source fg_prime target modFG_prime cert_prime :=
    ContinuousFunctionCarrier_comp_closed first second fgRel' modRel' certRel'
  have sameGraph : hsame fg fg_prime :=
    cont_deterministic fgRel fgRel'
  have sameModulus : hsame modFG modFG_prime :=
    cont_deterministic modRel modRel'
  have sameCert : hsame cert cert_prime :=
    cont_respects_hsame (hsame_refl target) sameModulus certRel certRel'
  exact
    And.intro leftCarrier
      (And.intro rightCarrier
        (And.intro sameGraph
          (And.intro sameModulus sameCert)))

end BEDC.Derived.ContinuousUp
