import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AronszajnTreeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AronszajnTreeUp : Type where
  | mk (T O L B H C P N : BHist) : AronszajnTreeUp
  deriving DecidableEq

def aronszajnTreeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: aronszajnTreeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: aronszajnTreeEncodeBHist h

def aronszajnTreeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (aronszajnTreeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (aronszajnTreeDecodeBHist tail)

private theorem aronszajnTree_decode_encode_bhist :
    ∀ h : BHist, aronszajnTreeDecodeBHist (aronszajnTreeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def aronszajnTreeFields : AronszajnTreeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AronszajnTreeUp.mk T O L B H C P N => [T, O, L, B, H, C, P, N]

def aronszajnTreeToEventFlow : AronszajnTreeUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (aronszajnTreeFields x).map aronszajnTreeEncodeBHist

private def aronszajnTreeRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => aronszajnTreeRawAt index rest

def aronszajnTreeFromEventFlow (flow : EventFlow) : Option AronszajnTreeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AronszajnTreeUp.mk
      (aronszajnTreeDecodeBHist (aronszajnTreeRawAt 0 flow))
      (aronszajnTreeDecodeBHist (aronszajnTreeRawAt 1 flow))
      (aronszajnTreeDecodeBHist (aronszajnTreeRawAt 2 flow))
      (aronszajnTreeDecodeBHist (aronszajnTreeRawAt 3 flow))
      (aronszajnTreeDecodeBHist (aronszajnTreeRawAt 4 flow))
      (aronszajnTreeDecodeBHist (aronszajnTreeRawAt 5 flow))
      (aronszajnTreeDecodeBHist (aronszajnTreeRawAt 6 flow))
      (aronszajnTreeDecodeBHist (aronszajnTreeRawAt 7 flow)))

private theorem aronszajnTree_round_trip :
    ∀ x : AronszajnTreeUp,
      aronszajnTreeFromEventFlow (aronszajnTreeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T O L B H C P N =>
      change
        some
          (AronszajnTreeUp.mk
            (aronszajnTreeDecodeBHist (aronszajnTreeEncodeBHist T))
            (aronszajnTreeDecodeBHist (aronszajnTreeEncodeBHist O))
            (aronszajnTreeDecodeBHist (aronszajnTreeEncodeBHist L))
            (aronszajnTreeDecodeBHist (aronszajnTreeEncodeBHist B))
            (aronszajnTreeDecodeBHist (aronszajnTreeEncodeBHist H))
            (aronszajnTreeDecodeBHist (aronszajnTreeEncodeBHist C))
            (aronszajnTreeDecodeBHist (aronszajnTreeEncodeBHist P))
            (aronszajnTreeDecodeBHist (aronszajnTreeEncodeBHist N))) =
          some (AronszajnTreeUp.mk T O L B H C P N)
      rw [aronszajnTree_decode_encode_bhist T,
        aronszajnTree_decode_encode_bhist O,
        aronszajnTree_decode_encode_bhist L,
        aronszajnTree_decode_encode_bhist B,
        aronszajnTree_decode_encode_bhist H,
        aronszajnTree_decode_encode_bhist C,
        aronszajnTree_decode_encode_bhist P,
        aronszajnTree_decode_encode_bhist N]

private theorem aronszajnTreeToEventFlow_injective {x y : AronszajnTreeUp} :
    aronszajnTreeToEventFlow x = aronszajnTreeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = aronszajnTreeFromEventFlow (aronszajnTreeToEventFlow x) :=
        (aronszajnTree_round_trip x).symm
      _ = aronszajnTreeFromEventFlow (aronszajnTreeToEventFlow y) :=
        congrArg aronszajnTreeFromEventFlow hxy
      _ = some y := aronszajnTree_round_trip y
  exact Option.some.inj optionEq

private theorem aronszajnTree_fields_faithful :
    ∀ x y : AronszajnTreeUp, aronszajnTreeFields x = aronszajnTreeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T1 O1 L1 B1 H1 C1 P1 N1 =>
      cases y with
      | mk T2 O2 L2 B2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance aronszajnTreeBHistCarrier : BHistCarrier AronszajnTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := aronszajnTreeToEventFlow
  fromEventFlow := aronszajnTreeFromEventFlow

instance aronszajnTreeChapterTasteGate : ChapterTasteGate AronszajnTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change aronszajnTreeFromEventFlow (aronszajnTreeToEventFlow x) = some x
    exact aronszajnTree_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (aronszajnTreeToEventFlow_injective heq)

instance aronszajnTreeFieldFaithful : FieldFaithful AronszajnTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := aronszajnTreeFields
  field_faithful := aronszajnTree_fields_faithful

instance aronszajnTreeNontrivial :
    BEDC.Meta.TasteGate.Nontrivial AronszajnTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AronszajnTreeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      AronszajnTreeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem AronszajnTreeTasteGate_single_carrier_alignment :
    (∀ h : BHist, aronszajnTreeDecodeBHist (aronszajnTreeEncodeBHist h) = h) ∧
      (∀ x : AronszajnTreeUp,
        aronszajnTreeFromEventFlow (aronszajnTreeToEventFlow x) = some x) ∧
        (∀ x y : AronszajnTreeUp,
          aronszajnTreeToEventFlow x = aronszajnTreeToEventFlow y → x = y) ∧
          aronszajnTreeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨aronszajnTree_decode_encode_bhist,
      aronszajnTree_round_trip,
      (by
        intro x y heq
        exact aronszajnTreeToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.AronszajnTreeUp
