import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FredholmAlternativeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FredholmAlternativeUp : Type where
  | mk
      (source target bounded compact laxMilgram riesz kernel obstruction transport replay
        provenance name : BHist) : FredholmAlternativeUp
  deriving DecidableEq

def fredholmAlternativeEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fredholmAlternativeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fredholmAlternativeEncodeBHist h

def fredholmAlternativeDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fredholmAlternativeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fredholmAlternativeDecodeBHist tail)

private theorem fredholmAlternative_decode_encode :
    forall h : BHist,
      fredholmAlternativeDecodeBHist (fredholmAlternativeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def fredholmAlternativeToEventFlow : FredholmAlternativeUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FredholmAlternativeUp.mk source target bounded compact laxMilgram riesz kernel obstruction
      transport replay provenance name =>
      [[BMark.b0],
        fredholmAlternativeEncodeBHist source,
        [BMark.b1],
        fredholmAlternativeEncodeBHist target,
        [BMark.b0, BMark.b0],
        fredholmAlternativeEncodeBHist bounded,
        [BMark.b0, BMark.b1],
        fredholmAlternativeEncodeBHist compact,
        [BMark.b1, BMark.b0],
        fredholmAlternativeEncodeBHist laxMilgram,
        [BMark.b1, BMark.b1],
        fredholmAlternativeEncodeBHist riesz,
        [BMark.b0, BMark.b0, BMark.b0],
        fredholmAlternativeEncodeBHist kernel,
        [BMark.b0, BMark.b0, BMark.b1],
        fredholmAlternativeEncodeBHist obstruction,
        [BMark.b0, BMark.b1, BMark.b0],
        fredholmAlternativeEncodeBHist transport,
        [BMark.b0, BMark.b1, BMark.b1],
        fredholmAlternativeEncodeBHist replay,
        [BMark.b1, BMark.b0, BMark.b0],
        fredholmAlternativeEncodeBHist provenance,
        [BMark.b1, BMark.b0, BMark.b1],
        fredholmAlternativeEncodeBHist name]

private def fredholmAlternativeEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ index, _ :: rest => fredholmAlternativeEventAtDefault index rest

def fredholmAlternativeFromEventFlow : EventFlow -> Option FredholmAlternativeUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (FredholmAlternativeUp.mk
          (fredholmAlternativeDecodeBHist (fredholmAlternativeEventAtDefault 1 flow))
          (fredholmAlternativeDecodeBHist (fredholmAlternativeEventAtDefault 3 flow))
          (fredholmAlternativeDecodeBHist (fredholmAlternativeEventAtDefault 5 flow))
          (fredholmAlternativeDecodeBHist (fredholmAlternativeEventAtDefault 7 flow))
          (fredholmAlternativeDecodeBHist (fredholmAlternativeEventAtDefault 9 flow))
          (fredholmAlternativeDecodeBHist (fredholmAlternativeEventAtDefault 11 flow))
          (fredholmAlternativeDecodeBHist (fredholmAlternativeEventAtDefault 13 flow))
          (fredholmAlternativeDecodeBHist (fredholmAlternativeEventAtDefault 15 flow))
          (fredholmAlternativeDecodeBHist (fredholmAlternativeEventAtDefault 17 flow))
          (fredholmAlternativeDecodeBHist (fredholmAlternativeEventAtDefault 19 flow))
          (fredholmAlternativeDecodeBHist (fredholmAlternativeEventAtDefault 21 flow))
          (fredholmAlternativeDecodeBHist (fredholmAlternativeEventAtDefault 23 flow)))

private theorem fredholmAlternative_round_trip :
    forall x : FredholmAlternativeUp,
      fredholmAlternativeFromEventFlow (fredholmAlternativeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source target bounded compact laxMilgram riesz kernel obstruction transport replay
      provenance name =>
      change
        some
          (FredholmAlternativeUp.mk
            (fredholmAlternativeDecodeBHist (fredholmAlternativeEncodeBHist source))
            (fredholmAlternativeDecodeBHist (fredholmAlternativeEncodeBHist target))
            (fredholmAlternativeDecodeBHist (fredholmAlternativeEncodeBHist bounded))
            (fredholmAlternativeDecodeBHist (fredholmAlternativeEncodeBHist compact))
            (fredholmAlternativeDecodeBHist (fredholmAlternativeEncodeBHist laxMilgram))
            (fredholmAlternativeDecodeBHist (fredholmAlternativeEncodeBHist riesz))
            (fredholmAlternativeDecodeBHist (fredholmAlternativeEncodeBHist kernel))
            (fredholmAlternativeDecodeBHist (fredholmAlternativeEncodeBHist obstruction))
            (fredholmAlternativeDecodeBHist (fredholmAlternativeEncodeBHist transport))
            (fredholmAlternativeDecodeBHist (fredholmAlternativeEncodeBHist replay))
            (fredholmAlternativeDecodeBHist (fredholmAlternativeEncodeBHist provenance))
            (fredholmAlternativeDecodeBHist (fredholmAlternativeEncodeBHist name))) =
          some
            (FredholmAlternativeUp.mk source target bounded compact laxMilgram riesz kernel
              obstruction transport replay provenance name)
      rw [fredholmAlternative_decode_encode source,
        fredholmAlternative_decode_encode target,
        fredholmAlternative_decode_encode bounded,
        fredholmAlternative_decode_encode compact,
        fredholmAlternative_decode_encode laxMilgram,
        fredholmAlternative_decode_encode riesz,
        fredholmAlternative_decode_encode kernel,
        fredholmAlternative_decode_encode obstruction,
        fredholmAlternative_decode_encode transport,
        fredholmAlternative_decode_encode replay,
        fredholmAlternative_decode_encode provenance,
        fredholmAlternative_decode_encode name]

private theorem fredholmAlternativeToEventFlow_injective {x y : FredholmAlternativeUp} :
    fredholmAlternativeToEventFlow x = fredholmAlternativeToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fredholmAlternativeFromEventFlow (fredholmAlternativeToEventFlow x) =
        fredholmAlternativeFromEventFlow (fredholmAlternativeToEventFlow y) :=
    congrArg fredholmAlternativeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (fredholmAlternative_round_trip x).symm
      (Eq.trans hread (fredholmAlternative_round_trip y)))

instance fredholmAlternativeBHistCarrier : BHistCarrier FredholmAlternativeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fredholmAlternativeToEventFlow
  fromEventFlow := fredholmAlternativeFromEventFlow

instance fredholmAlternativeChapterTasteGate : ChapterTasteGate FredholmAlternativeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fredholmAlternativeFromEventFlow (fredholmAlternativeToEventFlow x) = some x
    exact fredholmAlternative_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (fredholmAlternativeToEventFlow_injective heq)

theorem FredholmAlternativeTasteGate_single_carrier_alignment :
    (forall h : BHist, fredholmAlternativeDecodeBHist (fredholmAlternativeEncodeBHist h) = h) /\
      (forall x : FredholmAlternativeUp,
        fredholmAlternativeFromEventFlow (fredholmAlternativeToEventFlow x) = some x) /\
      (forall x y : FredholmAlternativeUp,
        fredholmAlternativeToEventFlow x = fredholmAlternativeToEventFlow y -> x = y) /\
      fredholmAlternativeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨fredholmAlternative_decode_encode,
      fredholmAlternative_round_trip,
      (fun _ _ heq => fredholmAlternativeToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FredholmAlternativeUp
