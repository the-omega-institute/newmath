import BEDC.Derived.LatticeUp

namespace BEDC.Derived.LatticeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem LatticeModular_lower_comparison_from_directional_bounds
    {Carrier : BHist -> Prop}
    {Classifier Le : BHist -> BHist -> Prop}
    {meet join : BHist -> BHist -> BHist}
    (cert : NameCert Carrier Classifier)
    (le_trans :
      forall {a b c : BHist}, Carrier a -> Carrier b -> Carrier c ->
        Le a b -> Le b c -> Le a c)
    (meet_carrier : forall {a b : BHist}, Carrier a -> Carrier b -> Carrier (meet a b))
    (join_carrier : forall {a b : BHist}, Carrier a -> Carrier b -> Carrier (join a b))
    (meet_lower_left : forall {a b : BHist}, Carrier a -> Carrier b -> Le (meet a b) a)
    (meet_lower_right : forall {a b : BHist}, Carrier a -> Carrier b -> Le (meet a b) b)
    (meet_greatest :
      forall {w a b : BHist}, Carrier w -> Carrier a -> Carrier b ->
        Le w a -> Le w b -> Le w (meet a b))
    (join_upper_left : forall {a b : BHist}, Carrier a -> Carrier b -> Le a (join a b))
    (join_upper_right : forall {a b : BHist}, Carrier a -> Carrier b -> Le b (join a b))
    (join_least :
      forall {w a b : BHist}, Carrier w -> Carrier a -> Carrier b ->
        Le a w -> Le b w -> Le (join a b) w)
    {x y z : BHist} :
    Carrier x -> Carrier y -> Carrier z -> Le x z ->
      Le (join x (meet y z)) (meet (join x y) z) := by
  intro carrierX carrierY carrierZ xLeZ
  have carrierXFromCert : Carrier x :=
    NameCert.carrier_respects_equiv cert (NameCert.equiv_refl cert carrierX) carrierX
  have carrierYZ : Carrier (meet y z) := meet_carrier carrierY carrierZ
  have carrierXY : Carrier (join x y) := join_carrier carrierXFromCert carrierY
  have carrierLeft : Carrier (join x (meet y z)) :=
    join_carrier carrierXFromCert carrierYZ
  have xLeXY : Le x (join x y) :=
    join_upper_left carrierXFromCert carrierY
  have yzLeY : Le (meet y z) y :=
    meet_lower_left carrierY carrierZ
  have yzLeZ : Le (meet y z) z :=
    meet_lower_right carrierY carrierZ
  have yzLeXY : Le (meet y z) (join x y) :=
    le_trans carrierYZ carrierY carrierXY yzLeY (join_upper_right carrierXFromCert carrierY)
  have leftLeXY : Le (join x (meet y z)) (join x y) :=
    join_least carrierXY carrierXFromCert carrierYZ xLeXY yzLeXY
  have leftLeZ : Le (join x (meet y z)) z :=
    join_least carrierZ carrierXFromCert carrierYZ xLeZ yzLeZ
  exact meet_greatest carrierLeft carrierXY carrierZ leftLeXY leftLeZ

end BEDC.Derived.LatticeUp
