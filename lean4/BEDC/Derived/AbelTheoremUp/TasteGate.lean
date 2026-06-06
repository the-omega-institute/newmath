import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AbelTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AbelTheoremUp : Type where
  | mk (A H C D W R E T P N : BHist) : AbelTheoremUp
  deriving DecidableEq

def abelTheoremEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: abelTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: abelTheoremEncodeBHist h

def abelTheoremDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (abelTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (abelTheoremDecodeBHist tail)

private theorem abelTheorem_decode_encode_bhist :
    ∀ h : BHist, abelTheoremDecodeBHist (abelTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def abelTheoremToEventFlow : AbelTheoremUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AbelTheoremUp.mk A H C D W R E T P N =>
      [[BMark.b0],
        abelTheoremEncodeBHist A,
        [BMark.b1, BMark.b0],
        abelTheoremEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b0],
        abelTheoremEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        abelTheoremEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        abelTheoremEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        abelTheoremEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        abelTheoremEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        abelTheoremEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        abelTheoremEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        abelTheoremEncodeBHist N]

private def abelTheoremEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => abelTheoremEventAt index rest

def abelTheoremFromEventFlow (ef : EventFlow) : Option AbelTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AbelTheoremUp.mk
      (abelTheoremDecodeBHist (abelTheoremEventAt 1 ef))
      (abelTheoremDecodeBHist (abelTheoremEventAt 3 ef))
      (abelTheoremDecodeBHist (abelTheoremEventAt 5 ef))
      (abelTheoremDecodeBHist (abelTheoremEventAt 7 ef))
      (abelTheoremDecodeBHist (abelTheoremEventAt 9 ef))
      (abelTheoremDecodeBHist (abelTheoremEventAt 11 ef))
      (abelTheoremDecodeBHist (abelTheoremEventAt 13 ef))
      (abelTheoremDecodeBHist (abelTheoremEventAt 15 ef))
      (abelTheoremDecodeBHist (abelTheoremEventAt 17 ef))
      (abelTheoremDecodeBHist (abelTheoremEventAt 19 ef)))

private theorem abelTheorem_round_trip :
    ∀ x : AbelTheoremUp, abelTheoremFromEventFlow (abelTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A H C D W R E T P N =>
      change
        some
          (AbelTheoremUp.mk
            (abelTheoremDecodeBHist (abelTheoremEncodeBHist A))
            (abelTheoremDecodeBHist (abelTheoremEncodeBHist H))
            (abelTheoremDecodeBHist (abelTheoremEncodeBHist C))
            (abelTheoremDecodeBHist (abelTheoremEncodeBHist D))
            (abelTheoremDecodeBHist (abelTheoremEncodeBHist W))
            (abelTheoremDecodeBHist (abelTheoremEncodeBHist R))
            (abelTheoremDecodeBHist (abelTheoremEncodeBHist E))
            (abelTheoremDecodeBHist (abelTheoremEncodeBHist T))
            (abelTheoremDecodeBHist (abelTheoremEncodeBHist P))
            (abelTheoremDecodeBHist (abelTheoremEncodeBHist N))) =
          some (AbelTheoremUp.mk A H C D W R E T P N)
      rw [abelTheorem_decode_encode_bhist A,
        abelTheorem_decode_encode_bhist H,
        abelTheorem_decode_encode_bhist C,
        abelTheorem_decode_encode_bhist D,
        abelTheorem_decode_encode_bhist W,
        abelTheorem_decode_encode_bhist R,
        abelTheorem_decode_encode_bhist E,
        abelTheorem_decode_encode_bhist T,
        abelTheorem_decode_encode_bhist P,
        abelTheorem_decode_encode_bhist N]

private theorem abelTheoremToEventFlow_injective {x y : AbelTheoremUp} :
    abelTheoremToEventFlow x = abelTheoremToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      abelTheoremFromEventFlow (abelTheoremToEventFlow x) =
        abelTheoremFromEventFlow (abelTheoremToEventFlow y) :=
    congrArg abelTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (abelTheorem_round_trip x).symm
      (Eq.trans hread (abelTheorem_round_trip y)))

instance abelTheoremBHistCarrier : BHistCarrier AbelTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := abelTheoremToEventFlow
  fromEventFlow := abelTheoremFromEventFlow

instance abelTheoremChapterTasteGate : ChapterTasteGate AbelTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change abelTheoremFromEventFlow (abelTheoremToEventFlow x) = some x
    exact abelTheorem_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (abelTheoremToEventFlow_injective heq)

theorem AbelTheoremTasteGate_single_carrier_alignment :
    (∃ carrier : BHistCarrier AbelTheoremUp,
        Nonempty (@ChapterTasteGate AbelTheoremUp carrier)) ∧
      (∀ h : BHist, abelTheoremDecodeBHist (abelTheoremEncodeBHist h) = h) ∧
      (∀ x : AbelTheoremUp, abelTheoremFromEventFlow (abelTheoremToEventFlow x) = some x) ∧
      abelTheoremEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨abelTheoremBHistCarrier, ⟨abelTheoremChapterTasteGate⟩⟩
  · constructor
    · exact abelTheorem_decode_encode_bhist
    · constructor
      · exact abelTheorem_round_trip
      · rfl

end BEDC.Derived.AbelTheoremUp
