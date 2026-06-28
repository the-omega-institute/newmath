import BEDC.Derived.EulerTheoremUp
import BEDC.Derived.ZModFieldUp
import BEDC.Derived.ZModResidueList
import BEDC.Algebra.Rel.IntegerUp

namespace BEDC.Derived.DirichletCharacterUp

open BEDC.Algebra.FiniteFold
open BEDC.Algebra.Rel
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PadicUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.ZModUp
open BEDC.Derived.ZModFieldUp
open BEDC.Derived.ZModResidueList
open BEDC.Derived.EulerTheoremUp

abbrev IntCarrier : Type :=
  BEDC.Algebra.Rel.IntegerUp

abbrev IntRelEq : IntCarrier -> IntCarrier -> Prop :=
  BEDC.Algebra.Rel.IntEq

def integerRing : RelCommRing IntCarrier IntRelEq :=
  IntegerUp_RelCommRing

def intEq := IntRelEq

def intZero : IntCarrier :=
  BEDC.Algebra.Rel.intZero

def intOne : IntCarrier :=
  BEDC.Algebra.Rel.intOne

def intNegOne : IntCarrier :=
  BEDC.Algebra.Rel.IntNeg intOne

def zmodRing (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) :
    RelCommRing (ZMod n) zmodEq :=
  zmodRelCommRing n nUnary nNonempty

def zmodUnit (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (x : ZMod n) : Prop :=
  relUnit (zmodRing n nUnary nNonempty) x

def zmodCharMul (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (x y : ZMod n) : ZMod n :=
  zmodMul n nUnary nNonempty x y

structure DirichletCharacter (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) where
  value : ZMod n -> IntCarrier
  respects : ∀ {x y : ZMod n}, zmodEq x y -> intEq (value x) (value y)
  completely_multiplicative : ∀ x y : ZMod n,
    intEq (value (zmodCharMul n nUnary nNonempty x y))
      (IntMul (value x) (value y))
  zero_on_nonunits : ∀ x : ZMod n,
    (zmodUnit n nUnary nNonempty x -> False) -> intEq (value x) intZero

def bhistEqBool (a b : BHist) : Bool :=
  if _h : a = b then true else false

theorem bhistEqBool_true {a b : BHist} :
    bhistEqBool a b = true -> hsame a b := by
  unfold bhistEqBool
  by_cases h : a = b
  · rw [dif_pos h]
    intro _hit
    exact h
  · rw [dif_neg h]
    intro hit
    cases hit

theorem bhistEqBool_false {a b : BHist} :
    bhistEqBool a b = false -> hsame a b -> False := by
  unfold bhistEqBool
  by_cases h : a = b
  · rw [dif_pos h]
    intro miss _same
    cases miss
  · intro _miss same
    exact h same

theorem bhistEqBool_self (a : BHist) :
    bhistEqBool a a = true := by
  unfold bhistEqBool
  rw [dif_pos rfl]

def zmodEqBool {n : BHist} (x y : ZMod n) : Bool :=
  bhistEqBool x.val y.val

theorem zmodEqBool_true {n : BHist} {x y : ZMod n} :
    zmodEqBool x y = true -> zmodEq x y := by
  intro hit
  exact bhistEqBool_true hit

theorem zmodEqBool_false {n : BHist} {x y : ZMod n} :
    zmodEqBool x y = false -> zmodEq x y -> False := by
  intro hit same
  exact bhistEqBool_false hit same

theorem zmodEqBool_of_zmodEq {n : BHist} {x y : ZMod n} :
    zmodEq x y -> zmodEqBool x y = true := by
  intro same
  unfold zmodEqBool zmodEq at *
  rw [same]
  exact bhistEqBool_self y.val

def listHasZMod {n : BHist} (x : ZMod n) : List (ZMod n) -> Bool
  | [] => false
  | y :: ys => if zmodEqBool x y = true then true else listHasZMod x ys

theorem listHasZMod_true {n : BHist} (x : ZMod n) :
    ∀ {xs : List (ZMod n)}, listHasZMod x xs = true ->
      ∃ y : ZMod n, y ∈ xs ∧ zmodEq x y
  | [], hit => by
      cases hit
  | y :: ys, hit => by
      unfold listHasZMod at hit
      cases sameBool : zmodEqBool x y
      · rw [sameBool] at hit
        cases listHasZMod_true x hit with
        | intro z zData =>
            exact ⟨z, List.Mem.tail y zData.left, zData.right⟩
      · exact ⟨y, List.Mem.head ys, zmodEqBool_true sameBool⟩

theorem listHasZMod_false_no_witness {n : BHist} (x : ZMod n) :
    ∀ {xs : List (ZMod n)}, listHasZMod x xs = false ->
      (∃ y : ZMod n, y ∈ xs ∧ zmodEq x y) -> False
  | [], _hit, witness => by
      cases witness with
      | intro y yData =>
          cases yData.left
  | y :: ys, hit, witness => by
      unfold listHasZMod at hit
      cases sameBool : zmodEqBool x y
      · rw [sameBool] at hit
        cases witness with
        | intro z zData =>
            cases zData.left with
            | head =>
                have sameHead : zmodEq x y := zData.right
                have headTrue : zmodEqBool x y = true :=
                  zmodEqBool_of_zmodEq sameHead
                rw [sameBool] at headTrue
                cases headTrue
            | tail _ tailMem =>
                exact listHasZMod_false_no_witness x hit
                  ⟨z, tailMem, zData.right⟩
      · rw [sameBool] at hit
        cases hit

theorem listHasZMod_membership_iff {n : BHist} (x : ZMod n)
    (xs : List (ZMod n)) :
    listHasZMod x xs = true ↔ ∃ y : ZMod n, y ∈ xs ∧ zmodEq x y := by
  constructor
  · intro hit
    exact listHasZMod_true x hit
  · intro witness
    induction xs with
    | nil =>
        cases witness with
        | intro y yData =>
            cases yData.left
    | cons y ys ih =>
        cases witness with
        | intro z zData =>
            unfold listHasZMod
            cases zData.left with
            | head =>
                have sameXY : zmodEq x y := zData.right
                have eqBool : zmodEqBool x y = true :=
                  zmodEqBool_of_zmodEq sameXY
                rw [if_pos eqBool]
            | tail _ zMem =>
                cases sameXYBool : zmodEqBool x y
                · rw [if_neg (by intro h; cases h)]
                  exact ih ⟨z, zMem, zData.right⟩
                · rw [if_pos rfl]

theorem zmodUnit_of_mul_unit_left {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (x y : ZMod n) :
    zmodUnit n nUnary nNonempty (zmodCharMul n nUnary nNonempty x y) ->
      zmodUnit n nUnary nNonempty x := by
  intro productUnit
  let R := zmodRing n nUnary nNonempty
  cases productUnit with
  | intro inv invData =>
      exact ⟨R.mul y inv,
        by
          exact R.trans
            (R.symm (R.mul_assoc x y inv))
            invData.left,
        by
          have assoc :
              zmodEq (R.mul (R.mul y inv) x)
                (R.mul y (R.mul inv x)) :=
            R.mul_assoc y inv x
          have move :
              zmodEq (R.mul y (R.mul inv x))
                (R.mul inv (R.mul x y)) := by
            have inner :
                zmodEq (R.mul y (R.mul inv x))
                  (R.mul y (R.mul x inv)) :=
              R.mul_congr (R.refl y) (R.mul_comm inv x)
            have leftAssoc :
                zmodEq (R.mul y (R.mul x inv))
                  (R.mul (R.mul y x) inv) :=
              R.symm (R.mul_assoc y x inv)
            have commute :
                zmodEq (R.mul (R.mul y x) inv)
                  (R.mul (R.mul x y) inv) :=
              R.mul_congr (R.mul_comm y x) (R.refl inv)
            have toInvLeft :
                zmodEq (R.mul (R.mul x y) inv)
                  (R.mul inv (R.mul x y)) :=
              R.mul_comm (R.mul x y) inv
            exact R.trans inner (R.trans leftAssoc (R.trans commute toInvLeft))
          exact R.trans assoc (R.trans move invData.right)⟩

theorem zmodUnit_of_mul_unit_right {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (x y : ZMod n) :
    zmodUnit n nUnary nNonempty (zmodCharMul n nUnary nNonempty x y) ->
      zmodUnit n nUnary nNonempty y := by
  intro productUnit
  let R := zmodRing n nUnary nNonempty
  have swapped : zmodUnit n nUnary nNonempty (R.mul y x) := by
    cases productUnit with
    | intro inv invData =>
        exact ⟨inv,
          R.trans (R.mul_congr (R.mul_comm y x) (R.refl inv)) invData.left,
          R.trans (R.mul_congr (R.refl inv) (R.mul_comm y x)) invData.right⟩
  exact zmodUnit_of_mul_unit_left nUnary nNonempty y x swapped

theorem zmodUnit_mul {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) {x y : ZMod n} :
    zmodUnit n nUnary nNonempty x ->
      zmodUnit n nUnary nNonempty y ->
        zmodUnit n nUnary nNonempty (zmodCharMul n nUnary nNonempty x y) := by
  intro xUnit yUnit
  exact relUnit_mul (zmodRing n nUnary nNonempty) xUnit yUnit

def principalValueFromSystem {n : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (system : ZModReducedResidueSystem n nUnary nNonempty)
    (x : ZMod n) : IntCarrier :=
  if listHasZMod x system.units then intOne else intZero

theorem principalValue_unit {n : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (system : ZModReducedResidueSystem n nUnary nNonempty)
    (x : ZMod n) :
    zmodUnit n nUnary nNonempty x ->
      intEq (principalValueFromSystem nUnary nNonempty system x) intOne := by
  intro xUnit
  unfold principalValueFromSystem
  have xMem : x ∈ system.units := (system.complete x).mpr xUnit
  have hit :
      listHasZMod x system.units = true :=
    (listHasZMod_membership_iff x system.units).mpr
      ⟨x, xMem, zmodEq_refl x⟩
  rw [hit]
  exact BEDC.Derived.RationalUp.IntEq_refl intOne

theorem principalValue_nonunit {n : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (system : ZModReducedResidueSystem n nUnary nNonempty)
    (x : ZMod n) :
    (zmodUnit n nUnary nNonempty x -> False) ->
      intEq (principalValueFromSystem nUnary nNonempty system x) intZero := by
  intro xNonunit
  unfold principalValueFromSystem
  cases hit : listHasZMod x system.units
  · exact BEDC.Derived.RationalUp.IntEq_refl intZero
  · cases listHasZMod_true x hit with
    | intro y yData =>
        have yUnit : zmodUnit n nUnary nNonempty y :=
          (system.complete y).mp yData.left
        have xUnit : zmodUnit n nUnary nNonempty x := by
          cases yUnit with
          | intro inv invData =>
              exact ⟨inv,
                (zmodRing n nUnary nNonempty).trans
                  ((zmodRing n nUnary nNonempty).mul_congr yData.right
                    ((zmodRing n nUnary nNonempty).refl inv))
                  invData.left,
                (zmodRing n nUnary nNonempty).trans
                  ((zmodRing n nUnary nNonempty).mul_congr
                    ((zmodRing n nUnary nNonempty).refl inv) yData.right)
                  invData.right⟩
        exact False.elim (xNonunit xUnit)

theorem principalValue_respects {n : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (system : ZModReducedResidueSystem n nUnary nNonempty)
    {x y : ZMod n} :
    zmodEq x y ->
      intEq (principalValueFromSystem nUnary nNonempty system x)
        (principalValueFromSystem nUnary nNonempty system y) := by
  intro same
  unfold principalValueFromSystem
  cases xHit : listHasZMod x system.units <;> cases yHit : listHasZMod y system.units
  · exact BEDC.Derived.RationalUp.IntEq_refl intZero
  · cases listHasZMod_true y yHit with
    | intro y0 yData =>
        have xWitness : ∃ x0 : ZMod n, x0 ∈ system.units ∧ zmodEq x x0 :=
          ⟨y0, yData.left, zmodEq_trans same yData.right⟩
        exact False.elim (listHasZMod_false_no_witness x xHit xWitness)
  · cases listHasZMod_true x xHit with
    | intro x0 xData =>
        have yWitness : ∃ y0 : ZMod n, y0 ∈ system.units ∧ zmodEq y y0 :=
          ⟨x0, xData.left, zmodEq_trans (zmodEq_symm same) xData.right⟩
        exact False.elim (listHasZMod_false_no_witness y yHit yWitness)
  · exact BEDC.Derived.RationalUp.IntEq_refl intOne

theorem principalValue_completely_multiplicative {n : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (system : ZModReducedResidueSystem n nUnary nNonempty)
    (x y : ZMod n) :
    intEq
      (principalValueFromSystem nUnary nNonempty system
        (zmodCharMul n nUnary nNonempty x y))
      (IntMul (principalValueFromSystem nUnary nNonempty system x)
        (principalValueFromSystem nUnary nNonempty system y)) := by
  let xy := zmodCharMul n nUnary nNonempty x y
  unfold principalValueFromSystem
  cases xHit : listHasZMod x system.units <;>
    cases yHit : listHasZMod y system.units <;>
      cases xyHit : listHasZMod xy system.units
  · exact BEDC.Derived.RationalUp.IntEq_symm
      (BEDC.Algebra.Rel.IntegerUp_RelCommRing.zero_mul intZero)
  · cases listHasZMod_true xy xyHit with
    | intro xy0 xyData =>
        have xyUnit : zmodUnit n nUnary nNonempty xy :=
          let xy0Unit := (system.complete xy0).mp xyData.left
          match xy0Unit with
          | ⟨inv, invData⟩ =>
              ⟨inv,
                (zmodRing n nUnary nNonempty).trans
                  ((zmodRing n nUnary nNonempty).mul_congr xyData.right
                    ((zmodRing n nUnary nNonempty).refl inv))
                  invData.left,
                (zmodRing n nUnary nNonempty).trans
                  ((zmodRing n nUnary nNonempty).mul_congr
                    ((zmodRing n nUnary nNonempty).refl inv) xyData.right)
                  invData.right⟩
        have xUnit := zmodUnit_of_mul_unit_left nUnary nNonempty x y xyUnit
        have xMem : x ∈ system.units := (system.complete x).mpr xUnit
        exact False.elim
          (listHasZMod_false_no_witness x xHit ⟨x, xMem, zmodEq_refl x⟩)
  · exact BEDC.Derived.RationalUp.IntEq_symm (IntMul_zero intZero)
  · cases listHasZMod_true xy xyHit with
    | intro xy0 xyData =>
        have xyUnit : zmodUnit n nUnary nNonempty xy :=
          let xy0Unit := (system.complete xy0).mp xyData.left
          match xy0Unit with
          | ⟨inv, invData⟩ =>
              ⟨inv,
                (zmodRing n nUnary nNonempty).trans
                  ((zmodRing n nUnary nNonempty).mul_congr xyData.right
                    ((zmodRing n nUnary nNonempty).refl inv))
                  invData.left,
                (zmodRing n nUnary nNonempty).trans
                  ((zmodRing n nUnary nNonempty).mul_congr
                    ((zmodRing n nUnary nNonempty).refl inv) xyData.right)
                  invData.right⟩
        have xUnit := zmodUnit_of_mul_unit_left nUnary nNonempty x y xyUnit
        have xMem : x ∈ system.units := (system.complete x).mpr xUnit
        exact False.elim
          (listHasZMod_false_no_witness x xHit ⟨x, xMem, zmodEq_refl x⟩)
  · exact BEDC.Derived.RationalUp.IntEq_symm
      (BEDC.Algebra.Rel.IntegerUp_RelCommRing.zero_mul intOne)
  · cases listHasZMod_true xy xyHit with
    | intro xy0 xyData =>
        have xyUnit : zmodUnit n nUnary nNonempty xy :=
          let xy0Unit := (system.complete xy0).mp xyData.left
          match xy0Unit with
          | ⟨inv, invData⟩ =>
              ⟨inv,
                (zmodRing n nUnary nNonempty).trans
                  ((zmodRing n nUnary nNonempty).mul_congr xyData.right
                    ((zmodRing n nUnary nNonempty).refl inv))
                  invData.left,
                (zmodRing n nUnary nNonempty).trans
                  ((zmodRing n nUnary nNonempty).mul_congr
                    ((zmodRing n nUnary nNonempty).refl inv) xyData.right)
                  invData.right⟩
        have yUnit := zmodUnit_of_mul_unit_right nUnary nNonempty x y xyUnit
        have yMem : y ∈ system.units := (system.complete y).mpr yUnit
        exact False.elim
          (listHasZMod_false_no_witness y yHit ⟨y, yMem, zmodEq_refl y⟩)
  · cases listHasZMod_true x xHit with
    | intro x0 xData =>
        cases listHasZMod_true y yHit with
        | intro y0 yData =>
            have xUnit : zmodUnit n nUnary nNonempty x :=
              let x0Unit := (system.complete x0).mp xData.left
              match x0Unit with
              | ⟨inv, invData⟩ =>
                  ⟨inv,
                    (zmodRing n nUnary nNonempty).trans
                      ((zmodRing n nUnary nNonempty).mul_congr xData.right
                        ((zmodRing n nUnary nNonempty).refl inv))
                      invData.left,
                    (zmodRing n nUnary nNonempty).trans
                      ((zmodRing n nUnary nNonempty).mul_congr
                        ((zmodRing n nUnary nNonempty).refl inv) xData.right)
                      invData.right⟩
            have yUnit : zmodUnit n nUnary nNonempty y :=
              let y0Unit := (system.complete y0).mp yData.left
              match y0Unit with
              | ⟨inv, invData⟩ =>
                  ⟨inv,
                    (zmodRing n nUnary nNonempty).trans
                      ((zmodRing n nUnary nNonempty).mul_congr yData.right
                        ((zmodRing n nUnary nNonempty).refl inv))
                      invData.left,
                    (zmodRing n nUnary nNonempty).trans
                      ((zmodRing n nUnary nNonempty).mul_congr
                        ((zmodRing n nUnary nNonempty).refl inv) yData.right)
                      invData.right⟩
            have xyUnit : zmodUnit n nUnary nNonempty xy :=
              zmodUnit_mul nUnary nNonempty xUnit yUnit
            have xyMem : xy ∈ system.units := (system.complete xy).mpr xyUnit
            exact False.elim
              (listHasZMod_false_no_witness xy xyHit
                ⟨xy, xyMem, zmodEq_refl xy⟩)
  · exact BEDC.Derived.RationalUp.IntEq_symm (IntMul_one intOne)

def principalCharacterFromSystem {n : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (system : ZModReducedResidueSystem n nUnary nNonempty) :
    DirichletCharacter n nUnary nNonempty where
  value := principalValueFromSystem nUnary nNonempty system
  respects := principalValue_respects nUnary nNonempty system
  completely_multiplicative :=
    principalValue_completely_multiplicative nUnary nNonempty system
  zero_on_nonunits := principalValue_nonunit nUnary nNonempty system

theorem principalCharacter_completely_multiplicative {n : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (system : ZModReducedResidueSystem n nUnary nNonempty)
    (x y : ZMod n) :
    intEq
      ((principalCharacterFromSystem nUnary nNonempty system).value
        (zmodCharMul n nUnary nNonempty x y))
      (IntMul ((principalCharacterFromSystem nUnary nNonempty system).value x)
        ((principalCharacterFromSystem nUnary nNonempty system).value y)) :=
  (principalCharacterFromSystem nUnary nNonempty system).completely_multiplicative x y

def characterSum {n : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (χ : DirichletCharacter n nUnary nNonempty)
    (xs : List (ZMod n)) : IntCarrier :=
  listSum integerRing (List.map χ.value xs)

theorem characterSum_perm {n : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (χ : DirichletCharacter n nUnary nNonempty)
    {xs ys : List (ZMod n)} :
    ListPerm xs ys -> intEq (characterSum nUnary nNonempty χ xs)
      (characterSum nUnary nNonempty χ ys) := by
  intro perm
  unfold characterSum
  exact sum_permInvariant integerRing (listPerm_map χ.value perm)

theorem principalCharacter_unit_sum_perm {n : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (system : ZModReducedResidueSystem n nUnary nNonempty)
    {xs : List (ZMod n)} :
    ListPerm xs system.units ->
      intEq
        (characterSum nUnary nNonempty
          (principalCharacterFromSystem nUnary nNonempty system) xs)
        (characterSum nUnary nNonempty
          (principalCharacterFromSystem nUnary nNonempty system) system.units) := by
  intro perm
  exact characterSum_perm nUnary nNonempty
    (principalCharacterFromSystem nUnary nNonempty system) perm

theorem characterSum_unit_mul_perm {n : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (χ : DirichletCharacter n nUnary nNonempty)
    (system : ZModReducedResidueSystem n nUnary nNonempty)
    (a : ZMod n) :
    zmodUnit n nUnary nNonempty a ->
      intEq
        (characterSum nUnary nNonempty χ
          (List.map
            (fun x : ZMod n => zmodCharMul n nUnary nNonempty a x)
            system.units))
        (characterSum nUnary nNonempty χ system.units) := by
  intro aUnit
  exact characterSum_perm nUnary nNonempty χ
    (zmod_unitMul_permutes_complete_units nUnary nNonempty a
      system.units aUnit system.nodup system.complete)

abbrev NatTwo : BHist := natToUnary 2
abbrev NatThree : BHist := natToUnary 3
abbrev NatFour : BHist := natToUnary 4

theorem NatTwo_prime : NatPrime NatTwo := by
  change NatPrime (BHist.e1 (BHist.e1 BHist.Empty))
  exact NatPrime_first_pair.left

theorem NatThree_prime : NatPrime NatThree := by
  change NatPrime (BHist.e1 (BHist.e1 (BHist.e1 BHist.Empty)))
  exact NatPrime_first_pair.right

def oneModThree : ZMod NatThree :=
  zmodOne NatThree NatThree_prime.left (NatPrime_empty_absurd NatThree_prime)

def twoModThree : ZMod NatThree :=
  zmodFromNat NatThree NatThree_prime.left
    (NatPrime_empty_absurd NatThree_prime) NatTwo (natToUnary_unary 2)

def nonzeroResidueSystemModThree :
    ZModReducedResidueSystem NatThree NatThree_prime.left
      (NatPrime_empty_absurd NatThree_prime) where
  factors := [NatThree]
  units := nonzeroResidues NatThree_prime
  nodup := nonzeroResidues_nodup NatThree_prime
  complete := by
    intro x
    constructor
    · intro mem
      exact ⟨zmodInv NatThree_prime x
          (nonzeroResidues_all_nonzero NatThree_prime x mem),
        zmodInv_mul NatThree_prime x
          (nonzeroResidues_all_nonzero NatThree_prime x mem),
        zmodMul_inv NatThree_prime x
          (nonzeroResidues_all_nonzero NatThree_prime x mem)⟩
    · intro unit
      cases unit with
      | intro inv invData =>
          have xNonzero : zmodNonzero x := by
            intro xZero
            have productZero :
                zmodEq
                  (zmodMul NatThree NatThree_prime.left
                    (NatPrime_empty_absurd NatThree_prime) x inv)
                  (zmodZero NatThree NatThree_prime.left
                    (NatPrime_empty_absurd NatThree_prime)) := by
              exact zmodEq_trans
                (zmodMul_congr NatThree_prime.left
                  (NatPrime_empty_absurd NatThree_prime)
                  (by change hsame x.val BHist.Empty; exact xZero)
                  (zmodEq_refl inv))
                (zmodMul_zero_left NatThree_prime.left
                  (NatPrime_empty_absurd NatThree_prime) inv)
            exact zmodOne_nonzero NatThree_prime
              (zmodEq_trans (zmodEq_symm invData.left) productZero)
          exact nonzero_residues_complete NatThree_prime x xNonzero
  phi_count := by
    rfl

def principalCharacterModThree :
    DirichletCharacter NatThree NatThree_prime.left
      (NatPrime_empty_absurd NatThree_prime) :=
  principalCharacterFromSystem NatThree_prime.left
    (NatPrime_empty_absurd NatThree_prime) nonzeroResidueSystemModThree

theorem principalCharacter_mod_three_one :
    intEq (principalCharacterModThree.value oneModThree) intOne := by
  exact principalValue_unit NatThree_prime.left
    (NatPrime_empty_absurd NatThree_prime) nonzeroResidueSystemModThree
    oneModThree
    ⟨oneModThree, zmodOne_mul_right NatThree_prime.left
      (NatPrime_empty_absurd NatThree_prime) oneModThree,
      zmodOne_mul_left NatThree_prime.left
        (NatPrime_empty_absurd NatThree_prime) oneModThree⟩

theorem principalCharacter_mod_three_two :
    intEq (principalCharacterModThree.value twoModThree) intOne := by
  exact principalValue_unit NatThree_prime.left
    (NatPrime_empty_absurd NatThree_prime) nonzeroResidueSystemModThree
    twoModThree
    ⟨zmodInv NatThree_prime twoModThree
        (by
          unfold twoModThree zmodNonzero zmodFromNat
          intro empty
          unfold NatThree NatTwo natToUnary natModFn at empty
          cases empty),
      zmodInv_mul NatThree_prime twoModThree
        (by
          unfold twoModThree zmodNonzero zmodFromNat
          intro empty
          unfold NatThree NatTwo natToUnary natModFn at empty
          cases empty),
      zmodMul_inv NatThree_prime twoModThree
        (by
          unfold twoModThree zmodNonzero zmodFromNat
          intro empty
          unfold NatThree NatTwo natToUnary natModFn at empty
          cases empty)⟩

theorem principalCharacter_mod_three_values :
    intEq (principalCharacterModThree.value oneModThree) intOne ∧
      intEq (principalCharacterModThree.value twoModThree) intOne := by
  exact ⟨principalCharacter_mod_three_one, principalCharacter_mod_three_two⟩

theorem principalCharacter_mod_three_completely_multiplicative
    (x y : ZMod NatThree) :
    intEq
      (principalCharacterModThree.value
        (zmodCharMul NatThree NatThree_prime.left
          (NatPrime_empty_absurd NatThree_prime) x y))
      (IntMul (principalCharacterModThree.value x)
        (principalCharacterModThree.value y)) :=
  principalCharacterModThree.completely_multiplicative x y

end BEDC.Derived.DirichletCharacterUp
