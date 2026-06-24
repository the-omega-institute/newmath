import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealInverseUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealInverseUp : Type where
  | mk (x a p w r s h c l n : BHist) : RealInverseUp
  deriving DecidableEq

def realInverseEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realInverseEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realInverseEncodeBHist h

def realInverseDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realInverseDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realInverseDecodeBHist tail)

private theorem realInverse_decode_encode :
    forall h : BHist, realInverseDecodeBHist (realInverseEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realInverseFields : RealInverseUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealInverseUp.mk x a p w r s h c l n => [x, a, p, w, r, s, h, c, l, n]

def realInverseToEventFlow : RealInverseUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map realInverseEncodeBHist (realInverseFields x)

private def realInverseEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realInverseEventAt index rest

def realInverseFromEventFlow : EventFlow -> Option RealInverseUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (RealInverseUp.mk
          (realInverseDecodeBHist (realInverseEventAt 0 ef))
          (realInverseDecodeBHist (realInverseEventAt 1 ef))
          (realInverseDecodeBHist (realInverseEventAt 2 ef))
          (realInverseDecodeBHist (realInverseEventAt 3 ef))
          (realInverseDecodeBHist (realInverseEventAt 4 ef))
          (realInverseDecodeBHist (realInverseEventAt 5 ef))
          (realInverseDecodeBHist (realInverseEventAt 6 ef))
          (realInverseDecodeBHist (realInverseEventAt 7 ef))
          (realInverseDecodeBHist (realInverseEventAt 8 ef))
          (realInverseDecodeBHist (realInverseEventAt 9 ef)))

private theorem realInverse_round_trip :
    forall x : RealInverseUp, realInverseFromEventFlow (realInverseToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk x a p w r s h c l n =>
      change
        some
            (RealInverseUp.mk
              (realInverseDecodeBHist (realInverseEncodeBHist x))
              (realInverseDecodeBHist (realInverseEncodeBHist a))
              (realInverseDecodeBHist (realInverseEncodeBHist p))
              (realInverseDecodeBHist (realInverseEncodeBHist w))
              (realInverseDecodeBHist (realInverseEncodeBHist r))
              (realInverseDecodeBHist (realInverseEncodeBHist s))
              (realInverseDecodeBHist (realInverseEncodeBHist h))
              (realInverseDecodeBHist (realInverseEncodeBHist c))
              (realInverseDecodeBHist (realInverseEncodeBHist l))
              (realInverseDecodeBHist (realInverseEncodeBHist n))) =
          some (RealInverseUp.mk x a p w r s h c l n)
      rw [realInverse_decode_encode x, realInverse_decode_encode a, realInverse_decode_encode p,
        realInverse_decode_encode w, realInverse_decode_encode r, realInverse_decode_encode s,
        realInverse_decode_encode h, realInverse_decode_encode c, realInverse_decode_encode l,
        realInverse_decode_encode n]

private theorem realInverseToEventFlow_injective {x y : RealInverseUp} :
    realInverseToEventFlow x = realInverseToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realInverseFromEventFlow (realInverseToEventFlow x) =
        realInverseFromEventFlow (realInverseToEventFlow y) :=
    congrArg realInverseFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realInverse_round_trip x).symm (Eq.trans hread (realInverse_round_trip y)))

private theorem realInverse_field_faithful :
    forall x y : RealInverseUp, realInverseFields x = realInverseFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk x1 a1 p1 w1 r1 s1 h1 c1 l1 n1 =>
      cases y with
      | mk x2 a2 p2 w2 r2 s2 h2 c2 l2 n2 =>
          cases hfields
          rfl

instance realInverseBHistCarrier : BHistCarrier RealInverseUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realInverseToEventFlow
  fromEventFlow := realInverseFromEventFlow

instance realInverseChapterTasteGate : ChapterTasteGate RealInverseUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realInverseFromEventFlow (realInverseToEventFlow x) = some x
    exact realInverse_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realInverseToEventFlow_injective heq)

instance realInverseFieldFaithful : FieldFaithful RealInverseUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realInverseFields
  field_faithful := realInverse_field_faithful

instance realInverseNontrivial : BEDC.Meta.TasteGate.Nontrivial RealInverseUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealInverseUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealInverseUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RealInverseTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RealInverseUp) ∧
      Nonempty (FieldFaithful RealInverseUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial RealInverseUp) ∧
      (forall h : BHist, realInverseDecodeBHist (realInverseEncodeBHist h) = h) ∧
      (forall x : RealInverseUp,
        realInverseFromEventFlow (realInverseToEventFlow x) = some x) ∧
      (forall x y : RealInverseUp,
        realInverseToEventFlow x = realInverseToEventFlow y -> x = y) ∧
      realInverseEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨realInverseChapterTasteGate⟩
  constructor
  · exact ⟨realInverseFieldFaithful⟩
  constructor
  · exact ⟨realInverseNontrivial⟩
  constructor
  · exact realInverse_decode_encode
  constructor
  · exact realInverse_round_trip
  constructor
  · intro x y
    exact realInverseToEventFlow_injective
  · rfl

end BEDC.Derived.RealInverseUp
