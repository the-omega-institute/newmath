import BEDC.Derived.LatticeUp

namespace BEDC.Derived.LatticeUp

open BEDC.FKernel.Hist

theorem LatticeSingleton_distributivity_modular_law {x y z : BHist} :
    LatticeSingletonCarrier x -> LatticeSingletonCarrier y -> LatticeSingletonCarrier z ->
      LatticeSingletonLE x z ->
        LatticeSingletonLE (LatticeSingletonJoin x (LatticeSingletonMeet y z))
          (LatticeSingletonMeet (LatticeSingletonJoin x y) z) ∧
        LatticeSingletonClassifier (LatticeSingletonJoin x (LatticeSingletonMeet y z))
          (LatticeSingletonMeet (LatticeSingletonJoin x y) z) := by
  intro _carrierX _carrierY _carrierZ _xLeZ
  have leftEmpty :
      hsame (LatticeSingletonJoin x (LatticeSingletonMeet y z)) BHist.Empty :=
    hsame_refl BHist.Empty
  have rightEmpty :
      hsame (LatticeSingletonMeet (LatticeSingletonJoin x y) z) BHist.Empty :=
    hsame_refl BHist.Empty
  exact
    And.intro
      (LatticeSingletonLE_empty_endpoints_iff.mpr (And.intro leftEmpty rightEmpty))
      (LatticeSingletonClassifier_empty_endpoints_iff.mpr (And.intro leftEmpty rightEmpty))

end BEDC.Derived.LatticeUp
