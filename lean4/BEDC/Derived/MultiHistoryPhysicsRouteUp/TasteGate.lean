import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MultiHistoryPhysicsRouteUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MultiHistoryPhysicsRouteUp : Type where
  | mk (G L M Q F H C P N : BHist) : MultiHistoryPhysicsRouteUp
  deriving DecidableEq

def multiHistoryPhysicsRouteEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: multiHistoryPhysicsRouteEncodeBHist h
  | BHist.e1 h => BMark.b1 :: multiHistoryPhysicsRouteEncodeBHist h

def multiHistoryPhysicsRouteDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (multiHistoryPhysicsRouteDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (multiHistoryPhysicsRouteDecodeBHist tail)

private def multiHistoryPhysicsRouteNthRawEvent : EventFlow → Nat → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | [], _ => []
  | head :: _tail, Nat.zero => head
  | _head :: tail, Nat.succ n => multiHistoryPhysicsRouteNthRawEvent tail n

private theorem multiHistoryPhysicsRoute_decode_encode_bhist :
    ∀ h : BHist,
      multiHistoryPhysicsRouteDecodeBHist (multiHistoryPhysicsRouteEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem multiHistoryPhysicsRoute_mk_congr
    {G G' L L' M M' Q Q' F F' H H' C C' P P' N N' : BHist}
    (hG : G' = G)
    (hL : L' = L)
    (hM : M' = M)
    (hQ : Q' = Q)
    (hF : F' = F)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    MultiHistoryPhysicsRouteUp.mk G' L' M' Q' F' H' C' P' N' =
      MultiHistoryPhysicsRouteUp.mk G L M Q F H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hG
  cases hL
  cases hM
  cases hQ
  cases hF
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def multiHistoryPhysicsRouteFields : MultiHistoryPhysicsRouteUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MultiHistoryPhysicsRouteUp.mk G L M Q F H C P N => [G, L, M, Q, F, H, C, P, N]

def multiHistoryPhysicsRouteToEventFlow : MultiHistoryPhysicsRouteUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MultiHistoryPhysicsRouteUp.mk G L M Q F H C P N =>
      [multiHistoryPhysicsRouteEncodeBHist G,
        multiHistoryPhysicsRouteEncodeBHist L,
        multiHistoryPhysicsRouteEncodeBHist M,
        multiHistoryPhysicsRouteEncodeBHist Q,
        multiHistoryPhysicsRouteEncodeBHist F,
        multiHistoryPhysicsRouteEncodeBHist H,
        multiHistoryPhysicsRouteEncodeBHist C,
        multiHistoryPhysicsRouteEncodeBHist P,
        multiHistoryPhysicsRouteEncodeBHist N]

def multiHistoryPhysicsRouteFromEventFlow
    (ef : EventFlow) : Option MultiHistoryPhysicsRouteUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MultiHistoryPhysicsRouteUp.mk
      (multiHistoryPhysicsRouteDecodeBHist (multiHistoryPhysicsRouteNthRawEvent ef 0))
      (multiHistoryPhysicsRouteDecodeBHist (multiHistoryPhysicsRouteNthRawEvent ef 1))
      (multiHistoryPhysicsRouteDecodeBHist (multiHistoryPhysicsRouteNthRawEvent ef 2))
      (multiHistoryPhysicsRouteDecodeBHist (multiHistoryPhysicsRouteNthRawEvent ef 3))
      (multiHistoryPhysicsRouteDecodeBHist (multiHistoryPhysicsRouteNthRawEvent ef 4))
      (multiHistoryPhysicsRouteDecodeBHist (multiHistoryPhysicsRouteNthRawEvent ef 5))
      (multiHistoryPhysicsRouteDecodeBHist (multiHistoryPhysicsRouteNthRawEvent ef 6))
      (multiHistoryPhysicsRouteDecodeBHist (multiHistoryPhysicsRouteNthRawEvent ef 7))
      (multiHistoryPhysicsRouteDecodeBHist (multiHistoryPhysicsRouteNthRawEvent ef 8)))

private theorem multiHistoryPhysicsRoute_round_trip :
    ∀ x : MultiHistoryPhysicsRouteUp,
      multiHistoryPhysicsRouteFromEventFlow
        (multiHistoryPhysicsRouteToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk G L M Q F H C P N =>
      exact
        congrArg some
          (multiHistoryPhysicsRoute_mk_congr
            (multiHistoryPhysicsRoute_decode_encode_bhist G)
            (multiHistoryPhysicsRoute_decode_encode_bhist L)
            (multiHistoryPhysicsRoute_decode_encode_bhist M)
            (multiHistoryPhysicsRoute_decode_encode_bhist Q)
            (multiHistoryPhysicsRoute_decode_encode_bhist F)
            (multiHistoryPhysicsRoute_decode_encode_bhist H)
            (multiHistoryPhysicsRoute_decode_encode_bhist C)
            (multiHistoryPhysicsRoute_decode_encode_bhist P)
            (multiHistoryPhysicsRoute_decode_encode_bhist N))

private theorem multiHistoryPhysicsRouteToEventFlow_injective
    {x y : MultiHistoryPhysicsRouteUp} :
    multiHistoryPhysicsRouteToEventFlow x = multiHistoryPhysicsRouteToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      multiHistoryPhysicsRouteFromEventFlow (multiHistoryPhysicsRouteToEventFlow x) =
        multiHistoryPhysicsRouteFromEventFlow (multiHistoryPhysicsRouteToEventFlow y) :=
    congrArg multiHistoryPhysicsRouteFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (multiHistoryPhysicsRoute_round_trip x).symm
      (Eq.trans hread (multiHistoryPhysicsRoute_round_trip y)))

private theorem multiHistoryPhysicsRoute_field_faithful :
    ∀ x y : MultiHistoryPhysicsRouteUp,
      multiHistoryPhysicsRouteFields x = multiHistoryPhysicsRouteFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk G L M Q F H C P N =>
      cases y with
      | mk G' L' M' Q' F' H' C' P' N' =>
          cases hfields
          rfl

instance multiHistoryPhysicsRouteBHistCarrier : BHistCarrier MultiHistoryPhysicsRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := multiHistoryPhysicsRouteToEventFlow
  fromEventFlow := multiHistoryPhysicsRouteFromEventFlow

instance multiHistoryPhysicsRouteChapterTasteGate :
    ChapterTasteGate MultiHistoryPhysicsRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change multiHistoryPhysicsRouteFromEventFlow
      (multiHistoryPhysicsRouteToEventFlow x) = some x
    exact multiHistoryPhysicsRoute_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (multiHistoryPhysicsRouteToEventFlow_injective heq)

instance multiHistoryPhysicsRouteFieldFaithful :
    FieldFaithful MultiHistoryPhysicsRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := multiHistoryPhysicsRouteFields
  field_faithful := multiHistoryPhysicsRoute_field_faithful

instance multiHistoryPhysicsRouteNontrivial : Nontrivial MultiHistoryPhysicsRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MultiHistoryPhysicsRouteUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MultiHistoryPhysicsRouteUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MultiHistoryPhysicsRouteUp :=
  -- BEDC touchpoint anchor: BHist BMark
  multiHistoryPhysicsRouteChapterTasteGate

theorem MultiHistoryPhysicsRouteTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      multiHistoryPhysicsRouteDecodeBHist (multiHistoryPhysicsRouteEncodeBHist h) = h) ∧
      (∀ x : MultiHistoryPhysicsRouteUp,
        multiHistoryPhysicsRouteFromEventFlow (multiHistoryPhysicsRouteToEventFlow x) =
          some x) ∧
        (∀ x y : MultiHistoryPhysicsRouteUp,
          multiHistoryPhysicsRouteToEventFlow x = multiHistoryPhysicsRouteToEventFlow y →
            x = y) ∧
          multiHistoryPhysicsRouteEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨multiHistoryPhysicsRoute_decode_encode_bhist,
      multiHistoryPhysicsRoute_round_trip,
      (fun _x _y heq => multiHistoryPhysicsRouteToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MultiHistoryPhysicsRouteUp
