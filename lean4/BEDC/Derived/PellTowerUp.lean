import BEDC.Derived.PellUp
import BEDC.Derived.QuadIntUp
import BEDC.Derived.PellLucasUp

namespace BEDC.Derived.PellTowerUp

abbrev Z := BEDC.Algebra.Rel.IntegerUp
abbrev Zeq := BEDC.Algebra.Rel.IntEq
abbrev Zzero := BEDC.Algebra.Rel.intZero
abbrev Zone := BEDC.Algebra.Rel.intOne
abbrev Zmul := BEDC.Algebra.Rel.IntMul

private def R : BEDC.Algebra.Rel.RelCommRing Z Zeq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

abbrev PellPair := BEDC.Derived.PellUp.PellPair
abbrev PellPairEq := BEDC.Derived.PellUp.PellPairEq
abbrev PellSolution := BEDC.Derived.PellUp.PellSolution
abbrev PellSolutionEq {D : Z} (a b : PellSolution D) : Prop :=
  BEDC.Derived.PellUp.PellSolutionEq a b
abbrev IsPellSolution (D x y : Z) : Prop :=
  BEDC.Derived.PellUp.IsPellSolution D x y

abbrev pellNorm := BEDC.Derived.PellUp.pellNorm
abbrev pellSolutionOne (D : Z) : PellSolution D :=
  BEDC.Derived.PellUp.pellSolutionOne D
abbrev pellSolutionMul {D : Z} (a b : PellSolution D) : PellSolution D :=
  BEDC.Derived.PellUp.pellSolutionMul a b
abbrev pellSolutionInv {D : Z} (a : PellSolution D) : PellSolution D :=
  BEDC.Derived.PellUp.pellSolutionInv a

abbrev QuadInt := BEDC.Derived.QuadIntUp.QuadInt
abbrev QuadEq {D : Z} (x y : QuadInt D) : Prop :=
  BEDC.Derived.QuadIntUp.QuadEq x y
abbrev quadMk {D : Z} (x y : Z) : QuadInt D :=
  BEDC.Derived.QuadIntUp.quadMk (d := D) x y
abbrev quadOne {D : Z} : QuadInt D :=
  BEDC.Derived.QuadIntUp.quadOne (d := D)
abbrev quadMul {D : Z} (x y : QuadInt D) : QuadInt D :=
  BEDC.Derived.QuadIntUp.quadMul x y

-- 基本解只记录一个已验证的 Pell 解, 不声明最小性或唯一性。
structure PellBasicSolution (D : Z) where
  x : Z
  y : Z
  isPell : IsPellSolution D x y

def PellBasicSolution.toSolution {D : Z}
    (seed : PellBasicSolution D) : PellSolution D :=
  { x := seed.x, y := seed.y, isPell := seed.isPell }

def PellBasicSolution.toPair {D : Z}
    (seed : PellBasicSolution D) : PellPair :=
  { x := seed.x, y := seed.y }

def pellTower {D : Z} (seed : PellBasicSolution D) :
    Nat -> PellSolution D
  | Nat.zero => pellSolutionOne D
  | Nat.succ n => pellSolutionMul seed.toSolution (pellTower seed n)

def pellTowerPair {D : Z} (seed : PellBasicSolution D)
    (n : Nat) : PellPair :=
  { x := (pellTower seed n).x, y := (pellTower seed n).y }

def pellTowerGenerated {D : Z} (seed : PellBasicSolution D)
    (p : PellPair) : Prop :=
  ∃ n : Nat, PellPairEq p (pellTowerPair seed n)

def pellTowerFuelList {D : Z} (seed : PellBasicSolution D) :
    Nat -> List (PellSolution D)
  | Nat.zero => [pellTower seed Nat.zero]
  | Nat.succ n => pellTowerFuelList seed n ++ [pellTower seed (Nat.succ n)]

theorem pellTower_zero {D : Z} (seed : PellBasicSolution D) :
    PellSolutionEq (pellTower seed Nat.zero) (pellSolutionOne D) :=
  BEDC.Derived.PellUp.PellSolutionEq_refl (pellSolutionOne D)

theorem pellTower_succ {D : Z} (seed : PellBasicSolution D)
    (n : Nat) :
    PellSolutionEq (pellTower seed (Nat.succ n))
      (pellSolutionMul seed.toSolution (pellTower seed n)) :=
  BEDC.Derived.PellUp.PellSolutionEq_refl
    (pellSolutionMul seed.toSolution (pellTower seed n))

theorem pellTower_one_eq_seed {D : Z} (seed : PellBasicSolution D) :
    PellSolutionEq (pellTower seed 1) seed.toSolution :=
  BEDC.Derived.PellUp.pellSolutionMul_one seed.toSolution

-- 强归纳版闭合证明: 每一层递归幂仍满足同一个 Pell 方程。
theorem pellTower_isPell_strong {D : Z}
    (seed : PellBasicSolution D) (n : Nat) :
    IsPellSolution D (pellTower seed n).x (pellTower seed n).y := by
  let motive := fun k : Nat =>
    IsPellSolution D (pellTower seed k).x (pellTower seed k).y
  have step : ∀ k : Nat, (∀ m : Nat, m < k -> motive m) -> motive k := by
    intro k ih
    cases k with
    | zero =>
        exact BEDC.Derived.PellUp.pell_trivial_solution D
    | succ k =>
        change IsPellSolution D
          (pellSolutionMul seed.toSolution (pellTower seed k)).x
          (pellSolutionMul seed.toSolution (pellTower seed k)).y
        exact BEDC.Derived.PellUp.brahmagupta_compose_isPellSolution
          D seed.x seed.y (pellTower seed k).x (pellTower seed k).y
          seed.isPell (ih k (Nat.lt_succ_self k))
  exact Nat.strongRecOn n step

theorem pellTower_isPell {D : Z}
    (seed : PellBasicSolution D) (n : Nat) :
    IsPellSolution D (pellTower seed n).x (pellTower seed n).y :=
  pellTower_isPell_strong seed n

theorem pellTowerGenerated_isPell {D : Z}
    {seed : PellBasicSolution D} {p : PellPair} :
    pellTowerGenerated seed p -> IsPellSolution D p.x p.y := by
  intro generated
  cases generated with
  | intro n same =>
      exact R.trans
        (BEDC.Derived.PellUp.pellNorm_respects same.left same.right)
        (pellTower_isPell seed n)

def quadPow {D : Z} (u : QuadInt D) : Nat -> QuadInt D
  | Nat.zero => quadOne
  | Nat.succ n => quadMul u (quadPow u n)

def pellBasicQuad {D : Z} (seed : PellBasicSolution D) : QuadInt D :=
  quadMk seed.x seed.y

theorem quadPow_zero {D : Z} (u : QuadInt D) :
    QuadEq (quadPow u Nat.zero) quadOne :=
  BEDC.Derived.QuadIntUp.QuadEq_refl quadOne

theorem quadPow_succ {D : Z} (u : QuadInt D) (n : Nat) :
    QuadEq (quadPow u (Nat.succ n)) (quadMul u (quadPow u n)) :=
  BEDC.Derived.QuadIntUp.QuadEq_refl (quadMul u (quadPow u n))

theorem pellTowerPair_eq_quadPow {D : Z}
    (seed : PellBasicSolution D) (n : Nat) :
    QuadEq
      (quadMk (pellTowerPair seed n).x (pellTowerPair seed n).y)
      (quadPow (pellBasicQuad seed) n) := by
  induction n with
  | zero =>
      exact BEDC.Derived.QuadIntUp.QuadEq_refl quadOne
  | succ n ih =>
      have step :
          QuadEq
            (quadMk (pellTowerPair seed (Nat.succ n)).x
              (pellTowerPair seed (Nat.succ n)).y)
            (quadMul (pellBasicQuad seed)
              (quadMk (pellTowerPair seed n).x
                (pellTowerPair seed n).y)) := by
        constructor
        · exact R.refl
            (BEDC.Derived.PellUp.pellComposeX D
              seed.x seed.y (pellTower seed n).x (pellTower seed n).y)
        · exact R.refl
            (BEDC.Derived.PellUp.pellComposeY D
              seed.x seed.y (pellTower seed n).x (pellTower seed n).y)
      exact BEDC.Derived.QuadIntUp.QuadEq_trans step
        (BEDC.Derived.QuadIntUp.quadMul_respects
          (BEDC.Derived.QuadIntUp.QuadEq_refl (pellBasicQuad seed))
          ih)

structure PellSolutionGroupLaws (D : Z) where
  eq_refl : ∀ a : PellSolution D, PellSolutionEq a a
  eq_symm : ∀ {a b : PellSolution D}, PellSolutionEq a b -> PellSolutionEq b a
  eq_trans :
    ∀ {a b c : PellSolution D},
      PellSolutionEq a b -> PellSolutionEq b c -> PellSolutionEq a c
  mul_respects :
    ∀ {a a' b b' : PellSolution D}, PellSolutionEq a a' ->
      PellSolutionEq b b' -> PellSolutionEq (pellSolutionMul a b)
        (pellSolutionMul a' b')
  mul_closed :
    ∀ a b : PellSolution D,
      IsPellSolution D (pellSolutionMul a b).x (pellSolutionMul a b).y
  mul_assoc :
    ∀ a b c : PellSolution D,
      PellSolutionEq (pellSolutionMul (pellSolutionMul a b) c)
        (pellSolutionMul a (pellSolutionMul b c))
  mul_comm :
    ∀ a b : PellSolution D,
      PellSolutionEq (pellSolutionMul a b) (pellSolutionMul b a)
  mul_one :
    ∀ a : PellSolution D, PellSolutionEq (pellSolutionMul a (pellSolutionOne D)) a
  one_mul :
    ∀ a : PellSolution D, PellSolutionEq (pellSolutionMul (pellSolutionOne D) a) a
  mul_inv :
    ∀ a : PellSolution D,
      PellSolutionEq (pellSolutionMul a (pellSolutionInv a)) (pellSolutionOne D)
  inv_mul :
    ∀ a : PellSolution D,
      PellSolutionEq (pellSolutionMul (pellSolutionInv a) a) (pellSolutionOne D)

def pellSolutionGroupLaws (D : Z) : PellSolutionGroupLaws D where
  eq_refl := BEDC.Derived.PellUp.PellSolutionEq_refl
  eq_symm := by
    intro a b
    exact BEDC.Derived.PellUp.PellSolutionEq_symm
  eq_trans := by
    intro a b c
    exact BEDC.Derived.PellUp.PellSolutionEq_trans
  mul_respects := by
    intro a a' b b'
    exact BEDC.Derived.PellUp.pellSolutionMul_respects
  mul_closed := BEDC.Derived.PellUp.pellSolutionMul_closed
  mul_assoc := BEDC.Derived.PellUp.pellSolutionMul_assoc
  mul_comm := BEDC.Derived.PellUp.pellSolutionMul_comm
  mul_one := BEDC.Derived.PellUp.pellSolutionMul_one
  one_mul := BEDC.Derived.PellUp.pellSolutionOne_mul
  mul_inv := BEDC.Derived.PellUp.pellSolutionMul_inv
  inv_mul := BEDC.Derived.PellUp.pellSolutionInv_mul

def ztwo : Z :=
  BEDC.Derived.PellLucasUp.ztwo

def zthree : Z :=
  BEDC.Derived.PellLucasUp.intOfNatStd 3

def pellDTwo : Z :=
  ztwo

def pellDThree : Z :=
  zthree

theorem pellDTwo_basic_isPell :
    IsPellSolution pellDTwo zthree ztwo := by
  exact R.refl Zone

def pellDTwoBasic : PellBasicSolution pellDTwo :=
  { x := zthree, y := ztwo, isPell := pellDTwo_basic_isPell }

theorem pellDThree_basic_isPell :
    IsPellSolution pellDThree ztwo Zone := by
  exact R.refl Zone

def pellDThreeBasic : PellBasicSolution pellDThree :=
  { x := ztwo, y := Zone, isPell := pellDThree_basic_isPell }

theorem pellDTwo_tower_isPell (n : Nat) :
    IsPellSolution pellDTwo
      (pellTower pellDTwoBasic n).x
      (pellTower pellDTwoBasic n).y :=
  pellTower_isPell pellDTwoBasic n

theorem pellDThree_tower_isPell (n : Nat) :
    IsPellSolution pellDThree
      (pellTower pellDThreeBasic n).x
      (pellTower pellDThreeBasic n).y :=
  pellTower_isPell pellDThreeBasic n

theorem pellDTwo_tower_one_coordinates :
    PellPairEq (pellTowerPair pellDTwoBasic 1)
      { x := zthree, y := ztwo } := by
  exact pellTower_one_eq_seed pellDTwoBasic

theorem pellDThree_tower_one_coordinates :
    PellPairEq (pellTowerPair pellDThreeBasic 1)
      { x := ztwo, y := Zone } := by
  exact pellTower_one_eq_seed pellDThreeBasic

end BEDC.Derived.PellTowerUp
