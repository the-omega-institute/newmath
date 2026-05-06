import BEDC.Derived.LatticeUp

namespace BEDC.Derived.LatticeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

protected theorem LatticeMeet_absorbs_smaller_ordered_endpoint_from_bounds
    {Carrier : BHist -> Prop}
    {Classifier Le : BHist -> BHist -> Prop}
    {meet : BHist -> BHist -> BHist}
    (cert : NameCert Carrier Classifier)
    (le_refl : forall {x : BHist}, Carrier x -> Le x x)
    (antisymm :
      forall {x y : BHist}, Carrier x -> Carrier y -> Le x y -> Le y x -> Classifier x y)
    (meet_carrier : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (meet x y))
    (meet_lower_right : forall {x y : BHist}, Carrier x -> Carrier y -> Le (meet x y) y)
    (meet_greatest :
      forall {w x y : BHist}, Carrier w -> Carrier x -> Carrier y -> Le w x -> Le w y ->
        Le w (meet x y))
    {x z : BHist} :
    Carrier x -> Carrier z -> Le x z -> Classifier (meet z x) x := by
  intro carrierX carrierZ leXZ
  have carrierMeet : Carrier (meet z x) := meet_carrier carrierZ carrierX
  have carrierMeetViaCert : Carrier (meet z x) :=
    NameCert.carrier_respects_equiv cert (NameCert.equiv_refl cert carrierMeet) carrierMeet
  have meetLeX : Le (meet z x) x := meet_lower_right carrierZ carrierX
  have xLeMeet : Le x (meet z x) :=
    meet_greatest carrierX carrierZ carrierX leXZ (le_refl carrierX)
  exact antisymm carrierMeetViaCert carrierX meetLeX xLeMeet

end BEDC.Derived.LatticeUp
