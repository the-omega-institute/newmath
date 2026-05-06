import BEDC.Derived.LatticeUp

namespace BEDC.Derived.LatticeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem LatticeDirected_commutativity_from_bounds
    {Carrier : BHist -> Prop} {Classifier Le : BHist -> BHist -> Prop}
    {meet join : BHist -> BHist -> BHist}
    (cert : NameCert Carrier Classifier)
    (antisymm : forall {a b : BHist}, Carrier a -> Carrier b -> Le a b -> Le b a ->
      Classifier a b)
    (meet_carrier : forall {a b : BHist}, Carrier a -> Carrier b -> Carrier (meet a b))
    (join_carrier : forall {a b : BHist}, Carrier a -> Carrier b -> Carrier (join a b))
    (meet_lower_left : forall {a b : BHist}, Carrier a -> Carrier b -> Le (meet a b) a)
    (meet_lower_right : forall {a b : BHist}, Carrier a -> Carrier b -> Le (meet a b) b)
    (meet_greatest : forall {w a b : BHist}, Carrier w -> Carrier a -> Carrier b ->
      Le w a -> Le w b -> Le w (meet a b))
    (join_upper_left : forall {a b : BHist}, Carrier a -> Carrier b -> Le a (join a b))
    (join_upper_right : forall {a b : BHist}, Carrier a -> Carrier b -> Le b (join a b))
    (join_least : forall {w a b : BHist}, Carrier w -> Carrier a -> Carrier b ->
      Le a w -> Le b w -> Le (join a b) w)
    {x y : BHist} :
    Carrier x -> Carrier y -> Classifier (meet x y) (meet y x) ∧
      Classifier (join x y) (join y x) := by
  intro carrierX carrierY
  have carrierXSelf : Classifier x x := NameCert.equiv_refl cert carrierX
  have carrierXViaCert : Carrier x :=
    NameCert.carrier_respects_equiv cert carrierXSelf carrierX
  have meetXYCarrier : Carrier (meet x y) := meet_carrier carrierXViaCert carrierY
  have meetYXCarrier : Carrier (meet y x) := meet_carrier carrierY carrierX
  have meetXY_le_meetYX : Le (meet x y) (meet y x) :=
    meet_greatest meetXYCarrier carrierY carrierX
      (meet_lower_right carrierX carrierY)
      (meet_lower_left carrierX carrierY)
  have meetYX_le_meetXY : Le (meet y x) (meet x y) :=
    meet_greatest meetYXCarrier carrierX carrierY
      (meet_lower_right carrierY carrierX)
      (meet_lower_left carrierY carrierX)
  have joinXYCarrier : Carrier (join x y) := join_carrier carrierX carrierY
  have joinYXCarrier : Carrier (join y x) := join_carrier carrierY carrierX
  have joinYX_le_joinXY : Le (join y x) (join x y) :=
    join_least joinXYCarrier carrierY carrierX
      (join_upper_right carrierX carrierY)
      (join_upper_left carrierX carrierY)
  have joinXY_le_joinYX : Le (join x y) (join y x) :=
    join_least joinYXCarrier carrierX carrierY
      (join_upper_right carrierY carrierX)
      (join_upper_left carrierY carrierX)
  exact And.intro
    (antisymm meetXYCarrier meetYXCarrier meetXY_le_meetYX meetYX_le_meetXY)
    (antisymm joinXYCarrier joinYXCarrier joinXY_le_joinYX joinYX_le_joinXY)

end BEDC.Derived.LatticeUp
