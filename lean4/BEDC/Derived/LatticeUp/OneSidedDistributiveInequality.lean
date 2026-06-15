import BEDC.Derived.LatticeUp

namespace BEDC.Derived.LatticeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem LatticeDirected_one_sided_distributive_inequality_from_bounds
    {Carrier : BHist -> Prop}
    {Le : BHist -> BHist -> Prop}
    {meet join : BHist -> BHist -> BHist}
    (cert : NameCert Carrier Le)
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
    Carrier x ->
      Carrier y -> Carrier z ->
        Le (join (meet x y) (meet x z)) (meet x (join y z)) := by
  -- BEDC touchpoint anchor: BHist NameCert
  intro carrierX carrierY carrierZ
  have carrierJoinYZ : Carrier (join y z) :=
    join_carrier carrierY carrierZ
  have carrierMeetXY : Carrier (meet x y) :=
    meet_carrier carrierX carrierY
  have carrierMeetXZ : Carrier (meet x z) :=
    meet_carrier carrierX carrierZ
  have carrierTarget : Carrier (meet x (join y z)) :=
    meet_carrier carrierX carrierJoinYZ
  have meetXYLeX : Le (meet x y) x :=
    meet_lower_left carrierX carrierY
  have meetXYLeY : Le (meet x y) y :=
    meet_lower_right carrierX carrierY
  have yLeJoinYZ : Le y (join y z) :=
    join_upper_left carrierY carrierZ
  have meetXYLeJoinYZ : Le (meet x y) (join y z) :=
    le_trans carrierMeetXY carrierY carrierJoinYZ meetXYLeY yLeJoinYZ
  have meetXYLeTarget : Le (meet x y) (meet x (join y z)) :=
    meet_greatest carrierMeetXY carrierX carrierJoinYZ meetXYLeX meetXYLeJoinYZ
  have meetXZLeX : Le (meet x z) x :=
    meet_lower_left carrierX carrierZ
  have meetXZLeZ : Le (meet x z) z :=
    meet_lower_right carrierX carrierZ
  have zLeJoinYZ : Le z (join y z) :=
    join_upper_right carrierY carrierZ
  have meetXZLeJoinYZ : Le (meet x z) (join y z) :=
    le_trans carrierMeetXZ carrierZ carrierJoinYZ meetXZLeZ zLeJoinYZ
  have meetXZLeTarget : Le (meet x z) (meet x (join y z)) :=
    meet_greatest carrierMeetXZ carrierX carrierJoinYZ meetXZLeX meetXZLeJoinYZ
  exact
    join_least carrierTarget carrierMeetXY carrierMeetXZ meetXYLeTarget meetXZLeTarget

end BEDC.Derived.LatticeUp
