import BEDC.Derived.SternBrocotUp
import BEDC.Derived.RationalUp.MetricOrder

namespace BEDC.Derived.FareySequenceUp

open BEDC.Derived.RationalUp
open BEDC.Derived.SternBrocotUp

abbrev FareyFraction := PositiveFraction

def fareyMediant (x y : FareyFraction) : FareyFraction :=
  mediant x y

def fareyAdjacent (x y : FareyFraction) : Prop :=
  FareyAdjacent x y

def fareyCrossDet (x y : FareyFraction) :=
  crossDet x y

def fareyDenominatorBound (n : Nat) (x : FareyFraction) : Prop :=
  BEDC.FKernel.ExternalBinary.bwordLength x.den ≤ n

def fareyProperFraction (x : FareyFraction) : Prop :=
  ratLe ratZero x ∧ ratLe x ratOne

def fareyReduced (x : FareyFraction) : Prop :=
  ∃ y : FareyFraction, fareyAdjacent x y ∨ fareyAdjacent y x

inductive FareyCountByRatEq :
    FareyFraction -> List FareyFraction -> Nat -> Prop where
  | nil (x : FareyFraction) : FareyCountByRatEq x [] 0
  | hit {x y : FareyFraction} {ys : List FareyFraction} {k : Nat} :
      RatEq x y -> FareyCountByRatEq x ys k ->
        FareyCountByRatEq x (y :: ys) (Nat.succ k)
  | miss {x y : FareyFraction} {ys : List FareyFraction} {k : Nat} :
      (RatEq x y -> False) -> FareyCountByRatEq x ys k ->
        FareyCountByRatEq x (y :: ys) k

def fareyNodupByRatEq (xs : List FareyFraction) : Prop :=
  ∀ (x : FareyFraction) (k : Nat), FareyCountByRatEq x xs k -> k ≤ 1

inductive FareyAdjacentList : List FareyFraction -> Prop where
  | nil : FareyAdjacentList []
  | single (x : FareyFraction) : FareyAdjacentList [x]
  | cons {x y : FareyFraction} {tail : List FareyFraction} :
      fareyAdjacent x y -> FareyAdjacentList (y :: tail) ->
        FareyAdjacentList (x :: y :: tail)

inductive FareySortedList : List FareyFraction -> Prop where
  | nil : FareySortedList []
  | single (x : FareyFraction) : FareySortedList [x]
  | cons {x y : FareyFraction} {tail : List FareyFraction} :
      ratLt x y -> FareySortedList (y :: tail) ->
        FareySortedList (x :: y :: tail)

inductive FareyMember : FareyFraction -> List FareyFraction -> Prop where
  | head {x y : FareyFraction} {tail : List FareyFraction} :
      RatEq x y -> FareyMember x (y :: tail)
  | tail {x y : FareyFraction} {tail : List FareyFraction} :
      FareyMember x tail -> FareyMember x (y :: tail)

def FareySequence (n : Nat) (xs : List FareyFraction) : Prop :=
  FareySortedList xs ∧ FareyAdjacentList xs ∧ fareyNodupByRatEq xs ∧
    ∀ x : FareyFraction,
      FareyMember x xs ->
        fareyProperFraction x ∧ fareyDenominatorBound n x ∧ fareyReduced x

theorem farey_mediant_num (x y : FareyFraction) :
    (fareyMediant x y).num = intRing.add x.num y.num := by
  exact mediant_num x y

theorem farey_mediant_den (x y : FareyFraction) :
    BEDC.FKernel.Hist.hsame (fareyMediant x y).den
      (BEDC.FKernel.Cont.append x.den y.den) := by
  exact mediant_den x y

theorem farey_adjacent_cross_eq_one {x y : FareyFraction} :
    fareyAdjacent x y -> IntRel (fareyCrossDet x y) intRing.one := by
  intro adjacent
  exact fareyAdjacent_cross_eq_one adjacent

theorem farey_adjacent_mediant_neighbors {x y : FareyFraction} :
    fareyAdjacent x y ->
      fareyAdjacent x (fareyMediant x y) ∧
        fareyAdjacent (fareyMediant x y) y := by
  intro adjacent
  exact fareyAdjacent_mediant_neighbors adjacent

theorem farey_adjacent_left_mediant {x y : FareyFraction} :
    fareyAdjacent x y -> fareyAdjacent x (fareyMediant x y) := by
  intro adjacent
  exact (farey_adjacent_mediant_neighbors adjacent).left

theorem farey_adjacent_mediant_right {x y : FareyFraction} :
    fareyAdjacent x y -> fareyAdjacent (fareyMediant x y) y := by
  intro adjacent
  exact (farey_adjacent_mediant_neighbors adjacent).right

theorem farey_mediant_left_cross_eq_one {x y : FareyFraction} :
    fareyAdjacent x y ->
      IntRel (fareyCrossDet x (fareyMediant x y)) intRing.one := by
  intro adjacent
  exact farey_adjacent_cross_eq_one (farey_adjacent_left_mediant adjacent)

theorem farey_mediant_right_cross_eq_one {x y : FareyFraction} :
    fareyAdjacent x y ->
      IntRel (fareyCrossDet (fareyMediant x y) y) intRing.one := by
  intro adjacent
  exact farey_adjacent_cross_eq_one (farey_adjacent_mediant_right adjacent)

theorem farey_adjacent_mediant_reduced {x y : FareyFraction} :
    fareyAdjacent x y -> fareyReduced (fareyMediant x y) := by
  intro adjacent
  exact ⟨y, Or.inl (farey_adjacent_mediant_right adjacent)⟩

theorem farey_adjacent_list_mediant_refines_pair {x y : FareyFraction} :
    fareyAdjacent x y ->
      FareyAdjacentList [x, fareyMediant x y, y] := by
  intro adjacent
  exact FareyAdjacentList.cons
    (farey_adjacent_left_mediant adjacent)
    (FareyAdjacentList.cons
      (farey_adjacent_mediant_right adjacent)
      (FareyAdjacentList.single y))

theorem farey_sequence_adjacent_surface {n : Nat} {xs : List FareyFraction} :
    FareySequence n xs -> FareyAdjacentList xs := by
  intro sequence
  exact sequence.right.left

theorem farey_sequence_sorted_surface {n : Nat} {xs : List FareyFraction} :
    FareySequence n xs -> FareySortedList xs := by
  intro sequence
  exact sequence.left

theorem farey_sequence_member_bound {n : Nat} {xs : List FareyFraction}
    {x : FareyFraction} :
    FareySequence n xs -> FareyMember x xs -> fareyDenominatorBound n x := by
  intro sequence member
  exact (sequence.right.right.right x member).right.left

theorem farey_sequence_member_reduced {n : Nat} {xs : List FareyFraction}
    {x : FareyFraction} :
    FareySequence n xs -> FareyMember x xs -> fareyReduced x := by
  intro sequence member
  exact (sequence.right.right.right x member).right.right

end BEDC.Derived.FareySequenceUp
