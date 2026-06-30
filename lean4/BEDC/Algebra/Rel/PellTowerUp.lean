import BEDC.Derived.PellTowerUp

namespace BEDC.Algebra.Rel

abbrev PellBasicSolution (D : IntegerUp) :=
  BEDC.Derived.PellTowerUp.PellBasicSolution D

abbrev PellSolutionGroupLaws (D : IntegerUp) :=
  BEDC.Derived.PellTowerUp.PellSolutionGroupLaws D

abbrev PellPair :=
  BEDC.Derived.PellTowerUp.PellPair

abbrev PellSolution (D : IntegerUp) :=
  BEDC.Derived.PellTowerUp.PellSolution D

abbrev pellTower {D : IntegerUp} (seed : PellBasicSolution D)
    (n : Nat) : PellSolution D :=
  BEDC.Derived.PellTowerUp.pellTower seed n

abbrev pellTowerPair {D : IntegerUp} (seed : PellBasicSolution D)
    (n : Nat) : PellPair :=
  BEDC.Derived.PellTowerUp.pellTowerPair seed n

abbrev pellTowerGenerated {D : IntegerUp}
    (seed : PellBasicSolution D) (p : PellPair) : Prop :=
  BEDC.Derived.PellTowerUp.pellTowerGenerated seed p

abbrev pellTowerFuelList {D : IntegerUp}
    (seed : PellBasicSolution D) (n : Nat) : List (PellSolution D) :=
  BEDC.Derived.PellTowerUp.pellTowerFuelList seed n

abbrev pellSolutionGroupLaws (D : IntegerUp) :
    PellSolutionGroupLaws D :=
  BEDC.Derived.PellTowerUp.pellSolutionGroupLaws D

abbrev pellDTwoBasic :
    PellBasicSolution BEDC.Derived.PellTowerUp.pellDTwo :=
  BEDC.Derived.PellTowerUp.pellDTwoBasic

abbrev pellDThreeBasic :
    PellBasicSolution BEDC.Derived.PellTowerUp.pellDThree :=
  BEDC.Derived.PellTowerUp.pellDThreeBasic

theorem PellTowerUp_isPell
    {D : IntegerUp} (seed : PellBasicSolution D) (n : Nat) :
    BEDC.Derived.PellTowerUp.IsPellSolution D
      (pellTower seed n).x
      (pellTower seed n).y :=
  BEDC.Derived.PellTowerUp.pellTower_isPell seed n

theorem PellTowerUp_generated_isPell
    {D : IntegerUp} {seed : PellBasicSolution D}
    {p : BEDC.Derived.PellTowerUp.PellPair} :
    pellTowerGenerated seed p ->
      BEDC.Derived.PellTowerUp.IsPellSolution D p.x p.y :=
  BEDC.Derived.PellTowerUp.pellTowerGenerated_isPell

theorem PellTowerUp_pair_eq_quadPow
    {D : IntegerUp} (seed : PellBasicSolution D) (n : Nat) :
    BEDC.Derived.PellTowerUp.QuadEq
      (BEDC.Derived.PellTowerUp.quadMk
        (pellTowerPair seed n).x (pellTowerPair seed n).y)
      (BEDC.Derived.PellTowerUp.quadPow
        (BEDC.Derived.PellTowerUp.pellBasicQuad seed) n) :=
  BEDC.Derived.PellTowerUp.pellTowerPair_eq_quadPow seed n

theorem PellTowerUp_DTwo_tower_isPell (n : Nat) :
    BEDC.Derived.PellTowerUp.IsPellSolution
      BEDC.Derived.PellTowerUp.pellDTwo
      (pellTower pellDTwoBasic n).x
      (pellTower pellDTwoBasic n).y :=
  BEDC.Derived.PellTowerUp.pellDTwo_tower_isPell n

theorem PellTowerUp_DThree_tower_isPell (n : Nat) :
    BEDC.Derived.PellTowerUp.IsPellSolution
      BEDC.Derived.PellTowerUp.pellDThree
      (pellTower pellDThreeBasic n).x
      (pellTower pellDThreeBasic n).y :=
  BEDC.Derived.PellTowerUp.pellDThree_tower_isPell n

end BEDC.Algebra.Rel
