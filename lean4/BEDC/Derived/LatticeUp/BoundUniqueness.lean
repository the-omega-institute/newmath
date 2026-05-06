import BEDC.Derived.LatticeUp

namespace BEDC.Derived.LatticeUp

open BEDC.FKernel.Hist

protected theorem LatticeSingleton_bound_uniqueness_from_directional_certificates
    {x y m j : BHist} :
    LatticeSingletonCarrier x ->
      LatticeSingletonCarrier y ->
        LatticeSingletonCarrier m ->
          LatticeSingletonCarrier j ->
            LatticeSingletonLE m x ->
              LatticeSingletonLE m y ->
                LatticeSingletonLE x j ->
                  LatticeSingletonLE y j ->
                    (forall {z : BHist}, LatticeSingletonCarrier z ->
                      LatticeSingletonLE z x -> LatticeSingletonLE z y ->
                        LatticeSingletonLE z m) ->
                    (forall {z : BHist}, LatticeSingletonCarrier z ->
                      LatticeSingletonLE x z -> LatticeSingletonLE y z ->
                        LatticeSingletonLE j z) ->
                    LatticeSingletonClassifier m (LatticeSingletonMeet x y) ∧
                      LatticeSingletonClassifier j (LatticeSingletonJoin x y) ∧
                        hsame m BHist.Empty ∧ hsame j BHist.Empty := by
  intro carrierX carrierY carrierM carrierJ lowerMX lowerMY upperXJ upperYJ meetGreatest
    joinLeast
  have meetRows :=
    LatticeSingletonMeet_greatest_lower_bound_empty_iff carrierX carrierY carrierM
  have joinRows :=
    LatticeSingletonJoin_least_upper_bound_empty_iff carrierX carrierY carrierJ
  have meetEmpty : hsame (LatticeSingletonMeet x y) BHist.Empty :=
    hsame_refl BHist.Empty
  have joinEmpty : hsame (LatticeSingletonJoin x y) BHist.Empty :=
    hsame_refl BHist.Empty
  have mLeMeet : LatticeSingletonLE m (LatticeSingletonMeet x y) :=
    Iff.mpr meetRows ⟨lowerMX, lowerMY, meetEmpty⟩
  have meetSelfRows :=
    LatticeSingletonMeet_greatest_lower_bound_empty_iff carrierX carrierY meetEmpty
  have meetSelfBounds :=
    Iff.mp meetSelfRows
      (LatticeSingletonLE_empty_endpoints_iff.mpr ⟨meetEmpty, meetEmpty⟩)
  have meetLeM : LatticeSingletonLE (LatticeSingletonMeet x y) m :=
    meetGreatest meetEmpty meetSelfBounds.left meetSelfBounds.right.left
  have meetAntisymm :=
    LatticeSingletonLE_antisymm_classifier mLeMeet meetLeM
  have joinLeJ : LatticeSingletonLE (LatticeSingletonJoin x y) j :=
    Iff.mpr joinRows ⟨upperXJ, upperYJ, joinEmpty⟩
  have joinSelfRows :=
    LatticeSingletonJoin_least_upper_bound_empty_iff carrierX carrierY joinEmpty
  have joinSelfBounds :=
    Iff.mp joinSelfRows
      (LatticeSingletonLE_empty_endpoints_iff.mpr ⟨joinEmpty, joinEmpty⟩)
  have jLeJoin : LatticeSingletonLE j (LatticeSingletonJoin x y) :=
    joinLeast joinEmpty joinSelfBounds.left joinSelfBounds.right.left
  have joinAntisymm :=
    LatticeSingletonLE_antisymm_classifier jLeJoin joinLeJ
  exact ⟨meetAntisymm.left, joinAntisymm.left, meetAntisymm.right.left,
    joinAntisymm.right.left⟩

end BEDC.Derived.LatticeUp
