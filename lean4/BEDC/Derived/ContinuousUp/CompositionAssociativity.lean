import BEDC.Derived.ContinuousUp

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuousFunctionCarrier_composition_associative_certificate_synchronization
    {source mid1 mid2 target f g h fg gh mapL mapR modF modG modH modFG modGH modL modR
      certF certG certH certFG certGH certL certR : BHist} :
    ContinuousFunctionCarrier source f mid1 modF certF ->
      ContinuousFunctionCarrier mid1 g mid2 modG certG ->
        ContinuousFunctionCarrier mid2 h target modH certH ->
          Cont f g fg ->
            Cont modF modG modFG ->
              Cont mid2 modFG certFG ->
                Cont fg h mapL ->
                  Cont modFG modH modL ->
                    Cont target modL certL ->
                      Cont g h gh ->
                        Cont modG modH modGH ->
                          Cont target modGH certGH ->
                            Cont f gh mapR ->
                              Cont modF modGH modR ->
                                Cont target modR certR ->
                                  ContinuousFunctionCarrier source mapL target modL certL ∧
                                    ContinuousFunctionCarrier source mapR target modR certR ∧
                                      hsame mapL mapR ∧ hsame modL modR ∧ hsame certL certR := by
  intro carrierF carrierG carrierH fgRel modFGRel certFGRel mapLRel modLRel certLRel
  intro ghRel modGHRel certGHRel mapRRel modRRel certRRel
  have carrierFG : ContinuousFunctionCarrier source fg mid2 modFG certFG :=
    ContinuousFunctionCarrier_comp_closed carrierF carrierG fgRel modFGRel certFGRel
  have carrierGH : ContinuousFunctionCarrier mid1 gh target modGH certGH :=
    ContinuousFunctionCarrier_comp_closed carrierG carrierH ghRel modGHRel certGHRel
  have carrierL : ContinuousFunctionCarrier source mapL target modL certL :=
    ContinuousFunctionCarrier_comp_closed carrierFG carrierH mapLRel modLRel certLRel
  have carrierR : ContinuousFunctionCarrier source mapR target modR certR :=
    ContinuousFunctionCarrier_comp_closed carrierF carrierGH mapRRel modRRel certRRel
  have sameMap : hsame mapL mapR :=
    cont_assoc_hsame fgRel mapLRel ghRel mapRRel
  have sameMod : hsame modL modR :=
    cont_assoc_hsame modFGRel modLRel modGHRel modRRel
  have sameCert : hsame certL certR :=
    cont_respects_hsame (hsame_refl target) sameMod certLRel certRRel
  exact
    And.intro carrierL
      (And.intro carrierR (And.intro sameMap (And.intro sameMod sameCert)))

end BEDC.Derived.ContinuousUp
