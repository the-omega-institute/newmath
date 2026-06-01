import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MooreSmithCauchyNetFilterBridgeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MooreSmithCauchyNetFilterBridgeUp : Type where
  | mk (D T F K U M S R Y E H C P N : BHist) : MooreSmithCauchyNetFilterBridgeUp
  deriving DecidableEq

def mooreSmithCauchyNetFilterBridgeEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: mooreSmithCauchyNetFilterBridgeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: mooreSmithCauchyNetFilterBridgeEncodeBHist h

def mooreSmithCauchyNetFilterBridgeDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (mooreSmithCauchyNetFilterBridgeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (mooreSmithCauchyNetFilterBridgeDecodeBHist tail)

private theorem mooreSmithCauchyNetFilterBridge_decode_encode_bhist :
    forall h : BHist,
      mooreSmithCauchyNetFilterBridgeDecodeBHist
        (mooreSmithCauchyNetFilterBridgeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def mooreSmithCauchyNetFilterBridgeToEventFlow :
    MooreSmithCauchyNetFilterBridgeUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MooreSmithCauchyNetFilterBridgeUp.mk D T F K U M S R Y E H C P N =>
      [mooreSmithCauchyNetFilterBridgeEncodeBHist D,
        mooreSmithCauchyNetFilterBridgeEncodeBHist T,
        mooreSmithCauchyNetFilterBridgeEncodeBHist F,
        mooreSmithCauchyNetFilterBridgeEncodeBHist K,
        mooreSmithCauchyNetFilterBridgeEncodeBHist U,
        mooreSmithCauchyNetFilterBridgeEncodeBHist M,
        mooreSmithCauchyNetFilterBridgeEncodeBHist S,
        mooreSmithCauchyNetFilterBridgeEncodeBHist R,
        mooreSmithCauchyNetFilterBridgeEncodeBHist Y,
        mooreSmithCauchyNetFilterBridgeEncodeBHist E,
        mooreSmithCauchyNetFilterBridgeEncodeBHist H,
        mooreSmithCauchyNetFilterBridgeEncodeBHist C,
        mooreSmithCauchyNetFilterBridgeEncodeBHist P,
        mooreSmithCauchyNetFilterBridgeEncodeBHist N]

private def mooreSmithCauchyNetFilterBridgeEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => mooreSmithCauchyNetFilterBridgeEventAt index rest

def mooreSmithCauchyNetFilterBridgeFromEventFlow :
    EventFlow -> Option MooreSmithCauchyNetFilterBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (MooreSmithCauchyNetFilterBridgeUp.mk
        (mooreSmithCauchyNetFilterBridgeDecodeBHist
          (mooreSmithCauchyNetFilterBridgeEventAt 0 ef))
        (mooreSmithCauchyNetFilterBridgeDecodeBHist
          (mooreSmithCauchyNetFilterBridgeEventAt 1 ef))
        (mooreSmithCauchyNetFilterBridgeDecodeBHist
          (mooreSmithCauchyNetFilterBridgeEventAt 2 ef))
        (mooreSmithCauchyNetFilterBridgeDecodeBHist
          (mooreSmithCauchyNetFilterBridgeEventAt 3 ef))
        (mooreSmithCauchyNetFilterBridgeDecodeBHist
          (mooreSmithCauchyNetFilterBridgeEventAt 4 ef))
        (mooreSmithCauchyNetFilterBridgeDecodeBHist
          (mooreSmithCauchyNetFilterBridgeEventAt 5 ef))
        (mooreSmithCauchyNetFilterBridgeDecodeBHist
          (mooreSmithCauchyNetFilterBridgeEventAt 6 ef))
        (mooreSmithCauchyNetFilterBridgeDecodeBHist
          (mooreSmithCauchyNetFilterBridgeEventAt 7 ef))
        (mooreSmithCauchyNetFilterBridgeDecodeBHist
          (mooreSmithCauchyNetFilterBridgeEventAt 8 ef))
        (mooreSmithCauchyNetFilterBridgeDecodeBHist
          (mooreSmithCauchyNetFilterBridgeEventAt 9 ef))
        (mooreSmithCauchyNetFilterBridgeDecodeBHist
          (mooreSmithCauchyNetFilterBridgeEventAt 10 ef))
        (mooreSmithCauchyNetFilterBridgeDecodeBHist
          (mooreSmithCauchyNetFilterBridgeEventAt 11 ef))
        (mooreSmithCauchyNetFilterBridgeDecodeBHist
          (mooreSmithCauchyNetFilterBridgeEventAt 12 ef))
        (mooreSmithCauchyNetFilterBridgeDecodeBHist
          (mooreSmithCauchyNetFilterBridgeEventAt 13 ef)))

private theorem mooreSmithCauchyNetFilterBridge_round_trip :
    forall x : MooreSmithCauchyNetFilterBridgeUp,
      mooreSmithCauchyNetFilterBridgeFromEventFlow
        (mooreSmithCauchyNetFilterBridgeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D T F K U M S R Y E H C P N =>
      change
        some
            (MooreSmithCauchyNetFilterBridgeUp.mk
              (mooreSmithCauchyNetFilterBridgeDecodeBHist
                (mooreSmithCauchyNetFilterBridgeEncodeBHist D))
              (mooreSmithCauchyNetFilterBridgeDecodeBHist
                (mooreSmithCauchyNetFilterBridgeEncodeBHist T))
              (mooreSmithCauchyNetFilterBridgeDecodeBHist
                (mooreSmithCauchyNetFilterBridgeEncodeBHist F))
              (mooreSmithCauchyNetFilterBridgeDecodeBHist
                (mooreSmithCauchyNetFilterBridgeEncodeBHist K))
              (mooreSmithCauchyNetFilterBridgeDecodeBHist
                (mooreSmithCauchyNetFilterBridgeEncodeBHist U))
              (mooreSmithCauchyNetFilterBridgeDecodeBHist
                (mooreSmithCauchyNetFilterBridgeEncodeBHist M))
              (mooreSmithCauchyNetFilterBridgeDecodeBHist
                (mooreSmithCauchyNetFilterBridgeEncodeBHist S))
              (mooreSmithCauchyNetFilterBridgeDecodeBHist
                (mooreSmithCauchyNetFilterBridgeEncodeBHist R))
              (mooreSmithCauchyNetFilterBridgeDecodeBHist
                (mooreSmithCauchyNetFilterBridgeEncodeBHist Y))
              (mooreSmithCauchyNetFilterBridgeDecodeBHist
                (mooreSmithCauchyNetFilterBridgeEncodeBHist E))
              (mooreSmithCauchyNetFilterBridgeDecodeBHist
                (mooreSmithCauchyNetFilterBridgeEncodeBHist H))
              (mooreSmithCauchyNetFilterBridgeDecodeBHist
                (mooreSmithCauchyNetFilterBridgeEncodeBHist C))
              (mooreSmithCauchyNetFilterBridgeDecodeBHist
                (mooreSmithCauchyNetFilterBridgeEncodeBHist P))
              (mooreSmithCauchyNetFilterBridgeDecodeBHist
                (mooreSmithCauchyNetFilterBridgeEncodeBHist N))) =
          some (MooreSmithCauchyNetFilterBridgeUp.mk D T F K U M S R Y E H C P N)
      rw [mooreSmithCauchyNetFilterBridge_decode_encode_bhist D,
        mooreSmithCauchyNetFilterBridge_decode_encode_bhist T,
        mooreSmithCauchyNetFilterBridge_decode_encode_bhist F,
        mooreSmithCauchyNetFilterBridge_decode_encode_bhist K,
        mooreSmithCauchyNetFilterBridge_decode_encode_bhist U,
        mooreSmithCauchyNetFilterBridge_decode_encode_bhist M,
        mooreSmithCauchyNetFilterBridge_decode_encode_bhist S,
        mooreSmithCauchyNetFilterBridge_decode_encode_bhist R,
        mooreSmithCauchyNetFilterBridge_decode_encode_bhist Y,
        mooreSmithCauchyNetFilterBridge_decode_encode_bhist E,
        mooreSmithCauchyNetFilterBridge_decode_encode_bhist H,
        mooreSmithCauchyNetFilterBridge_decode_encode_bhist C,
        mooreSmithCauchyNetFilterBridge_decode_encode_bhist P,
        mooreSmithCauchyNetFilterBridge_decode_encode_bhist N]

private theorem mooreSmithCauchyNetFilterBridgeToEventFlow_injective
    {x y : MooreSmithCauchyNetFilterBridgeUp} :
    mooreSmithCauchyNetFilterBridgeToEventFlow x =
        mooreSmithCauchyNetFilterBridgeToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      mooreSmithCauchyNetFilterBridgeFromEventFlow
          (mooreSmithCauchyNetFilterBridgeToEventFlow x) =
        mooreSmithCauchyNetFilterBridgeFromEventFlow
          (mooreSmithCauchyNetFilterBridgeToEventFlow y) :=
    congrArg mooreSmithCauchyNetFilterBridgeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (mooreSmithCauchyNetFilterBridge_round_trip x).symm
      (Eq.trans hread (mooreSmithCauchyNetFilterBridge_round_trip y)))

instance mooreSmithCauchyNetFilterBridgeBHistCarrier :
    BHistCarrier MooreSmithCauchyNetFilterBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := mooreSmithCauchyNetFilterBridgeToEventFlow
  fromEventFlow := mooreSmithCauchyNetFilterBridgeFromEventFlow

instance mooreSmithCauchyNetFilterBridgeChapterTasteGate :
    ChapterTasteGate MooreSmithCauchyNetFilterBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      mooreSmithCauchyNetFilterBridgeFromEventFlow
        (mooreSmithCauchyNetFilterBridgeToEventFlow x) = some x
    exact mooreSmithCauchyNetFilterBridge_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (mooreSmithCauchyNetFilterBridgeToEventFlow_injective heq)

def taste_gate : ChapterTasteGate MooreSmithCauchyNetFilterBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  mooreSmithCauchyNetFilterBridgeChapterTasteGate

theorem MooreSmithCauchyNetFilterBridgeTasteGate_single_carrier_alignment :
    (forall h : BHist,
      mooreSmithCauchyNetFilterBridgeDecodeBHist
        (mooreSmithCauchyNetFilterBridgeEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier MooreSmithCauchyNetFilterBridgeUp) ∧
        Nonempty (ChapterTasteGate MooreSmithCauchyNetFilterBridgeUp) ∧
          mooreSmithCauchyNetFilterBridgeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨mooreSmithCauchyNetFilterBridge_decode_encode_bhist,
      Nonempty.intro mooreSmithCauchyNetFilterBridgeBHistCarrier,
      Nonempty.intro mooreSmithCauchyNetFilterBridgeChapterTasteGate,
      rfl⟩

end BEDC.Derived.MooreSmithCauchyNetFilterBridgeUp
