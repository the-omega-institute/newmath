import BEDC.Derived.ContinuousUp

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuousFunctionCarrier_triple_composition_certificate_synchronization
    {source mid1 mid2 target f g h fg gh mapL mapR modF modG modH modFG modGH modL modR
      certF certG certH certFG certGH certL certR : BHist} :
    ContinuousFunctionCarrier source f mid1 modF certF ->
      ContinuousFunctionCarrier mid1 g mid2 modG certG ->
        ContinuousFunctionCarrier mid2 h target modH certH ->
          Cont f g fg -> Cont modF modG modFG -> Cont mid2 modFG certFG ->
            Cont fg h mapL -> Cont modFG modH modL -> Cont target modL certL ->
              Cont g h gh -> Cont modG modH modGH -> Cont target modGH certGH ->
                Cont f gh mapR -> Cont modF modGH modR -> Cont target modR certR ->
                  ContinuousFunctionCarrier source mapL target modL certL ∧
                    ContinuousFunctionCarrier source mapR target modR certR ∧
                      hsame mapL mapR ∧ hsame modL modR ∧ hsame certL certR := by
  intro carrierF carrierG carrierH graphFG modulusFG certFGRel graphL modulusL certLRel
    graphGH modulusGH _certGHRel graphR modulusR certRRel
  have carrierFG :
      ContinuousFunctionCarrier source fg mid2 modFG certFG :=
    ContinuousFunctionCarrier_comp_closed carrierF carrierG graphFG modulusFG certFGRel
  have carrierGH :
      ContinuousFunctionCarrier mid1 gh target modGH certGH :=
    ContinuousFunctionCarrier_comp_closed carrierG carrierH graphGH modulusGH _certGHRel
  have carrierL :
      ContinuousFunctionCarrier source mapL target modL certL :=
    ContinuousFunctionCarrier_comp_closed carrierFG carrierH graphL modulusL certLRel
  have carrierR :
      ContinuousFunctionCarrier source mapR target modR certR :=
    ContinuousFunctionCarrier_comp_closed carrierF carrierGH graphR modulusR certRRel
  have graphSame : hsame mapL mapR :=
    cont_assoc_unique graphFG graphGH graphL graphR
  have modulusSame : hsame modL modR :=
    cont_assoc_unique modulusFG modulusGH modulusL modulusR
  have certSame : hsame certL certR :=
    cont_respects_hsame (hsame_refl target) modulusSame certLRel certRRel
  exact And.intro carrierL
    (And.intro carrierR (And.intro graphSame (And.intro modulusSame certSame)))

end BEDC.Derived.ContinuousUp
