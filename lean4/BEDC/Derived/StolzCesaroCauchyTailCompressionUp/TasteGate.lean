import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StolzCesaroCauchyTailCompressionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StolzCesaroCauchyTailCompressionUp where
  | mk (W G D S R E H C P N : BHist) : StolzCesaroCauchyTailCompressionUp
deriving DecidableEq

def stolzCesaroCauchyTailCompressionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: stolzCesaroCauchyTailCompressionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: stolzCesaroCauchyTailCompressionEncodeBHist h

def stolzCesaroCauchyTailCompressionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (stolzCesaroCauchyTailCompressionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (stolzCesaroCauchyTailCompressionDecodeBHist tail)

private theorem StolzCesaroCauchyTailCompression_decode_encode :
    ∀ h : BHist,
      stolzCesaroCauchyTailCompressionDecodeBHist
        (stolzCesaroCauchyTailCompressionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def stolzCesaroCauchyTailCompressionToEventFlow :
    StolzCesaroCauchyTailCompressionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | StolzCesaroCauchyTailCompressionUp.mk W G D S R E H C P N =>
      [stolzCesaroCauchyTailCompressionEncodeBHist W,
        stolzCesaroCauchyTailCompressionEncodeBHist G,
        stolzCesaroCauchyTailCompressionEncodeBHist D,
        stolzCesaroCauchyTailCompressionEncodeBHist S,
        stolzCesaroCauchyTailCompressionEncodeBHist R,
        stolzCesaroCauchyTailCompressionEncodeBHist E,
        stolzCesaroCauchyTailCompressionEncodeBHist H,
        stolzCesaroCauchyTailCompressionEncodeBHist C,
        stolzCesaroCauchyTailCompressionEncodeBHist P,
        stolzCesaroCauchyTailCompressionEncodeBHist N]

private def stolzCesaroCauchyTailCompressionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      stolzCesaroCauchyTailCompressionEventAtDefault index rest

def stolzCesaroCauchyTailCompressionDecodeEventFlow
    (ef : EventFlow) : StolzCesaroCauchyTailCompressionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  StolzCesaroCauchyTailCompressionUp.mk
    (stolzCesaroCauchyTailCompressionDecodeBHist
      (stolzCesaroCauchyTailCompressionEventAtDefault 0 ef))
    (stolzCesaroCauchyTailCompressionDecodeBHist
      (stolzCesaroCauchyTailCompressionEventAtDefault 1 ef))
    (stolzCesaroCauchyTailCompressionDecodeBHist
      (stolzCesaroCauchyTailCompressionEventAtDefault 2 ef))
    (stolzCesaroCauchyTailCompressionDecodeBHist
      (stolzCesaroCauchyTailCompressionEventAtDefault 3 ef))
    (stolzCesaroCauchyTailCompressionDecodeBHist
      (stolzCesaroCauchyTailCompressionEventAtDefault 4 ef))
    (stolzCesaroCauchyTailCompressionDecodeBHist
      (stolzCesaroCauchyTailCompressionEventAtDefault 5 ef))
    (stolzCesaroCauchyTailCompressionDecodeBHist
      (stolzCesaroCauchyTailCompressionEventAtDefault 6 ef))
    (stolzCesaroCauchyTailCompressionDecodeBHist
      (stolzCesaroCauchyTailCompressionEventAtDefault 7 ef))
    (stolzCesaroCauchyTailCompressionDecodeBHist
      (stolzCesaroCauchyTailCompressionEventAtDefault 8 ef))
    (stolzCesaroCauchyTailCompressionDecodeBHist
      (stolzCesaroCauchyTailCompressionEventAtDefault 9 ef))

def stolzCesaroCauchyTailCompressionFromEventFlow
    (ef : EventFlow) : Option StolzCesaroCauchyTailCompressionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some (stolzCesaroCauchyTailCompressionDecodeEventFlow ef)

private theorem StolzCesaroCauchyTailCompression_round_trip :
    ∀ x : StolzCesaroCauchyTailCompressionUp,
      stolzCesaroCauchyTailCompressionFromEventFlow
        (stolzCesaroCauchyTailCompressionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W G D S R E H C P N =>
      change
        some
          (StolzCesaroCauchyTailCompressionUp.mk
            (stolzCesaroCauchyTailCompressionDecodeBHist
              (stolzCesaroCauchyTailCompressionEncodeBHist W))
            (stolzCesaroCauchyTailCompressionDecodeBHist
              (stolzCesaroCauchyTailCompressionEncodeBHist G))
            (stolzCesaroCauchyTailCompressionDecodeBHist
              (stolzCesaroCauchyTailCompressionEncodeBHist D))
            (stolzCesaroCauchyTailCompressionDecodeBHist
              (stolzCesaroCauchyTailCompressionEncodeBHist S))
            (stolzCesaroCauchyTailCompressionDecodeBHist
              (stolzCesaroCauchyTailCompressionEncodeBHist R))
            (stolzCesaroCauchyTailCompressionDecodeBHist
              (stolzCesaroCauchyTailCompressionEncodeBHist E))
            (stolzCesaroCauchyTailCompressionDecodeBHist
              (stolzCesaroCauchyTailCompressionEncodeBHist H))
            (stolzCesaroCauchyTailCompressionDecodeBHist
              (stolzCesaroCauchyTailCompressionEncodeBHist C))
            (stolzCesaroCauchyTailCompressionDecodeBHist
              (stolzCesaroCauchyTailCompressionEncodeBHist P))
            (stolzCesaroCauchyTailCompressionDecodeBHist
              (stolzCesaroCauchyTailCompressionEncodeBHist N))) =
          some (StolzCesaroCauchyTailCompressionUp.mk W G D S R E H C P N)
      rw [StolzCesaroCauchyTailCompression_decode_encode W,
        StolzCesaroCauchyTailCompression_decode_encode G,
        StolzCesaroCauchyTailCompression_decode_encode D,
        StolzCesaroCauchyTailCompression_decode_encode S,
        StolzCesaroCauchyTailCompression_decode_encode R,
        StolzCesaroCauchyTailCompression_decode_encode E,
        StolzCesaroCauchyTailCompression_decode_encode H,
        StolzCesaroCauchyTailCompression_decode_encode C,
        StolzCesaroCauchyTailCompression_decode_encode P,
        StolzCesaroCauchyTailCompression_decode_encode N]

private theorem stolzCesaroCauchyTailCompressionToEventFlow_injective
    {x y : StolzCesaroCauchyTailCompressionUp} :
    stolzCesaroCauchyTailCompressionToEventFlow x =
      stolzCesaroCauchyTailCompressionToEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      stolzCesaroCauchyTailCompressionFromEventFlow
          (stolzCesaroCauchyTailCompressionToEventFlow x) =
        stolzCesaroCauchyTailCompressionFromEventFlow
          (stolzCesaroCauchyTailCompressionToEventFlow y) :=
    congrArg stolzCesaroCauchyTailCompressionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (StolzCesaroCauchyTailCompression_round_trip x).symm
      (Eq.trans hread (StolzCesaroCauchyTailCompression_round_trip y)))

instance stolzCesaroCauchyTailCompressionBHistCarrier :
    BHistCarrier StolzCesaroCauchyTailCompressionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := stolzCesaroCauchyTailCompressionToEventFlow
  fromEventFlow := stolzCesaroCauchyTailCompressionFromEventFlow

instance stolzCesaroCauchyTailCompressionChapterTasteGate :
    ChapterTasteGate StolzCesaroCauchyTailCompressionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      stolzCesaroCauchyTailCompressionFromEventFlow
        (stolzCesaroCauchyTailCompressionToEventFlow x) = some x
    exact StolzCesaroCauchyTailCompression_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (stolzCesaroCauchyTailCompressionToEventFlow_injective heq)

instance stolzCesaroCauchyTailCompressionNontrivial :
    Nontrivial StolzCesaroCauchyTailCompressionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨StolzCesaroCauchyTailCompressionUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      StolzCesaroCauchyTailCompressionUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate StolzCesaroCauchyTailCompressionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  stolzCesaroCauchyTailCompressionChapterTasteGate

theorem StolzCesaroCauchyTailCompressionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      stolzCesaroCauchyTailCompressionDecodeBHist
        (stolzCesaroCauchyTailCompressionEncodeBHist h) = h) ∧
      (∀ x : StolzCesaroCauchyTailCompressionUp,
        stolzCesaroCauchyTailCompressionFromEventFlow
          (stolzCesaroCauchyTailCompressionToEventFlow x) = some x) ∧
        (∀ x y : StolzCesaroCauchyTailCompressionUp,
          stolzCesaroCauchyTailCompressionToEventFlow x =
            stolzCesaroCauchyTailCompressionToEventFlow y → x = y) ∧
          stolzCesaroCauchyTailCompressionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate Nontrivial
  exact
    ⟨StolzCesaroCauchyTailCompression_decode_encode,
      StolzCesaroCauchyTailCompression_round_trip,
      (fun _ _ heq => stolzCesaroCauchyTailCompressionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.StolzCesaroCauchyTailCompressionUp
