import BEDC.Derived.LatticeUp

namespace BEDC.Derived.LatticeUp

open BEDC.FKernel.Hist

theorem LatticeDirected_idempotence_absorption_from_bounds
    {Carrier : BHist -> Prop}
    {Classifier Le : BHist -> BHist -> Prop}
    {meet join : BHist -> BHist -> BHist}
    (le_refl : forall {x : BHist}, Carrier x -> Le x x)
    (antisymm :
      forall {x y : BHist}, Carrier x -> Carrier y -> Le x y -> Le y x -> Classifier x y)
    (meet_carrier : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (meet x y))
    (join_carrier : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (join x y))
    (meet_lower_left : forall {x y : BHist}, Carrier x -> Carrier y -> Le (meet x y) x)
    (meet_greatest :
      forall {z x y : BHist}, Carrier z -> Carrier x -> Carrier y ->
        Le z x -> Le z y -> Le z (meet x y))
    (join_upper_left : forall {x y : BHist}, Carrier x -> Carrier y -> Le x (join x y))
    (join_least :
      forall {z x y : BHist}, Carrier z -> Carrier x -> Carrier y ->
        Le x z -> Le y z -> Le (join x y) z)
    {x y : BHist} :
    Carrier x -> Carrier y ->
      Classifier (meet x x) x ∧
        Classifier (join x x) x ∧
          Classifier (meet x (join x y)) x ∧
            Classifier (join x (meet x y)) x := by
  intro carrierX carrierY
  have carrierMeetXX : Carrier (meet x x) := meet_carrier carrierX carrierX
  have meetXXLeX : Le (meet x x) x := meet_lower_left carrierX carrierX
  have xLeMeetXX : Le x (meet x x) :=
    meet_greatest carrierX carrierX carrierX (le_refl carrierX) (le_refl carrierX)
  have meetXXClass : Classifier (meet x x) x :=
    antisymm carrierMeetXX carrierX meetXXLeX xLeMeetXX
  have carrierJoinXX : Carrier (join x x) := join_carrier carrierX carrierX
  have xLeJoinXX : Le x (join x x) := join_upper_left carrierX carrierX
  have joinXXLeX : Le (join x x) x :=
    join_least carrierX carrierX carrierX (le_refl carrierX) (le_refl carrierX)
  have joinXXClass : Classifier (join x x) x :=
    antisymm carrierJoinXX carrierX joinXXLeX xLeJoinXX
  have carrierJoinXY : Carrier (join x y) := join_carrier carrierX carrierY
  have carrierMeetXJoin : Carrier (meet x (join x y)) :=
    meet_carrier carrierX carrierJoinXY
  have meetXJoinLeX : Le (meet x (join x y)) x :=
    meet_lower_left carrierX carrierJoinXY
  have xLeJoinXY : Le x (join x y) := join_upper_left carrierX carrierY
  have xLeMeetXJoin : Le x (meet x (join x y)) :=
    meet_greatest carrierX carrierX carrierJoinXY (le_refl carrierX) xLeJoinXY
  have meetXJoinClass : Classifier (meet x (join x y)) x :=
    antisymm carrierMeetXJoin carrierX meetXJoinLeX xLeMeetXJoin
  have carrierMeetXY : Carrier (meet x y) := meet_carrier carrierX carrierY
  have carrierJoinXMeet : Carrier (join x (meet x y)) :=
    join_carrier carrierX carrierMeetXY
  have xLeJoinXMeet : Le x (join x (meet x y)) :=
    join_upper_left carrierX carrierMeetXY
  have meetXYLeX : Le (meet x y) x := meet_lower_left carrierX carrierY
  have joinXMeetLeX : Le (join x (meet x y)) x :=
    join_least carrierX carrierX carrierMeetXY (le_refl carrierX) meetXYLeX
  have joinXMeetClass : Classifier (join x (meet x y)) x :=
    antisymm carrierJoinXMeet carrierX joinXMeetLeX xLeJoinXMeet
  exact
    And.intro meetXXClass
      (And.intro joinXXClass (And.intro meetXJoinClass joinXMeetClass))

end BEDC.Derived.LatticeUp
