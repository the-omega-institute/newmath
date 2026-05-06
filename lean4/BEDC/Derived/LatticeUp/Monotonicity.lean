import BEDC.Derived.LatticeUp

namespace BEDC.Derived.LatticeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Derived.PreorderUp

theorem LatticeJoin_two_sided_monotonicity_from_directional_bounds
    {Carrier : BHist -> Prop}
    {Classifier Le : BHist -> BHist -> Prop}
    {join : BHist -> BHist -> BHist}
    (cert : NameCert Carrier Classifier)
    (le_trans :
      forall {a b c : BHist}, Carrier a -> Carrier b -> Carrier c -> Le a b -> Le b c ->
        Le a c)
    (join_carrier : forall {a b : BHist}, Carrier a -> Carrier b -> Carrier (join a b))
    (join_upper_left : forall {a b : BHist}, Carrier a -> Carrier b -> Le a (join a b))
    (join_upper_right : forall {a b : BHist}, Carrier a -> Carrier b -> Le b (join a b))
    (join_least :
      forall {w a b : BHist},
        Carrier w -> Carrier a -> Carrier b -> Le a w -> Le b w -> Le (join a b) w)
    {a a' b b' : BHist} :
    Carrier a -> Carrier a' -> Carrier b -> Carrier b' -> Le a a' -> Le b b' ->
      Le (join a b) (join a' b') := by
  cases NameCert.carrier_inhabited cert with
  | intro _witness _witnessCarrier =>
      intro carrierA carrierA' carrierB carrierB' leAA' leBB'
      have carrierJoinTarget : Carrier (join a' b') := join_carrier carrierA' carrierB'
      have leAJoinTarget : Le a (join a' b') :=
        le_trans carrierA carrierA' carrierJoinTarget leAA'
          (join_upper_left carrierA' carrierB')
      have leBJoinTarget : Le b (join a' b') :=
        le_trans carrierB carrierB' carrierJoinTarget leBB'
          (join_upper_right carrierA' carrierB')
      exact join_least carrierJoinTarget carrierA carrierB leAJoinTarget leBJoinTarget

theorem LatticeSingletonMeet_monotone_empty {a a' b b' : BHist} :
    LatticeSingletonCarrier a ->
      LatticeSingletonCarrier a' ->
        LatticeSingletonCarrier b ->
          LatticeSingletonCarrier b' ->
            LatticeSingletonLE a a' ->
              LatticeSingletonLE b b' ->
                LatticeSingletonLE (LatticeSingletonMeet a b) (LatticeSingletonMeet a' b') ∧
                  hsame (LatticeSingletonMeet a b) BHist.Empty ∧
                    hsame (LatticeSingletonMeet a' b') BHist.Empty := by
  intro _carrierA _carrierA' _carrierB _carrierB' _leAA' _leBB'
  have meetEmpty : hsame (LatticeSingletonMeet a b) BHist.Empty := hsame_refl BHist.Empty
  have meetEmpty' : hsame (LatticeSingletonMeet a' b') BHist.Empty :=
    hsame_refl BHist.Empty
  have meetLE :
      LatticeSingletonLE (LatticeSingletonMeet a b) (LatticeSingletonMeet a' b') :=
    ⟨meetEmpty, meetEmpty',
      PreorderPrefixLE_of_hsame (hsame_trans meetEmpty (hsame_symm meetEmpty'))⟩
  exact ⟨meetLE, meetEmpty, meetEmpty'⟩

end BEDC.Derived.LatticeUp
