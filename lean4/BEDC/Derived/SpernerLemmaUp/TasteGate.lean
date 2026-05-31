import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SpernerLemmaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SpernerLemmaUp : Type where
  | mk (k d b f w h c p n : BHist) : SpernerLemmaUp
  deriving DecidableEq

def spernerLemmaEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: spernerLemmaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: spernerLemmaEncodeBHist h

def spernerLemmaDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (spernerLemmaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (spernerLemmaDecodeBHist tail)

private theorem SpernerLemmaTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, spernerLemmaDecodeBHist (spernerLemmaEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def spernerLemmaToEventFlow : SpernerLemmaUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SpernerLemmaUp.mk k d b f w h c p n =>
      [[BMark.b0],
        spernerLemmaEncodeBHist k,
        [BMark.b1, BMark.b0],
        spernerLemmaEncodeBHist d,
        [BMark.b1, BMark.b1, BMark.b0],
        spernerLemmaEncodeBHist b,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        spernerLemmaEncodeBHist f,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        spernerLemmaEncodeBHist w,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        spernerLemmaEncodeBHist h,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        spernerLemmaEncodeBHist c,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        spernerLemmaEncodeBHist p,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        spernerLemmaEncodeBHist n]

private def spernerLemmaEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => spernerLemmaEventAtDefault index rest

def spernerLemmaFromEventFlow (ef : EventFlow) : Option SpernerLemmaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SpernerLemmaUp.mk
      (spernerLemmaDecodeBHist (spernerLemmaEventAtDefault 1 ef))
      (spernerLemmaDecodeBHist (spernerLemmaEventAtDefault 3 ef))
      (spernerLemmaDecodeBHist (spernerLemmaEventAtDefault 5 ef))
      (spernerLemmaDecodeBHist (spernerLemmaEventAtDefault 7 ef))
      (spernerLemmaDecodeBHist (spernerLemmaEventAtDefault 9 ef))
      (spernerLemmaDecodeBHist (spernerLemmaEventAtDefault 11 ef))
      (spernerLemmaDecodeBHist (spernerLemmaEventAtDefault 13 ef))
      (spernerLemmaDecodeBHist (spernerLemmaEventAtDefault 15 ef))
      (spernerLemmaDecodeBHist (spernerLemmaEventAtDefault 17 ef)))

private theorem SpernerLemmaTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SpernerLemmaUp, spernerLemmaFromEventFlow (spernerLemmaToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk k d b f w h c p n =>
      change
        some
          (SpernerLemmaUp.mk
            (spernerLemmaDecodeBHist (spernerLemmaEncodeBHist k))
            (spernerLemmaDecodeBHist (spernerLemmaEncodeBHist d))
            (spernerLemmaDecodeBHist (spernerLemmaEncodeBHist b))
            (spernerLemmaDecodeBHist (spernerLemmaEncodeBHist f))
            (spernerLemmaDecodeBHist (spernerLemmaEncodeBHist w))
            (spernerLemmaDecodeBHist (spernerLemmaEncodeBHist h))
            (spernerLemmaDecodeBHist (spernerLemmaEncodeBHist c))
            (spernerLemmaDecodeBHist (spernerLemmaEncodeBHist p))
            (spernerLemmaDecodeBHist (spernerLemmaEncodeBHist n))) =
          some (SpernerLemmaUp.mk k d b f w h c p n)
      rw [SpernerLemmaTasteGate_single_carrier_alignment_decode_encode k,
        SpernerLemmaTasteGate_single_carrier_alignment_decode_encode d,
        SpernerLemmaTasteGate_single_carrier_alignment_decode_encode b,
        SpernerLemmaTasteGate_single_carrier_alignment_decode_encode f,
        SpernerLemmaTasteGate_single_carrier_alignment_decode_encode w,
        SpernerLemmaTasteGate_single_carrier_alignment_decode_encode h,
        SpernerLemmaTasteGate_single_carrier_alignment_decode_encode c,
        SpernerLemmaTasteGate_single_carrier_alignment_decode_encode p,
        SpernerLemmaTasteGate_single_carrier_alignment_decode_encode n]

private theorem SpernerLemmaTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SpernerLemmaUp} :
    spernerLemmaToEventFlow x = spernerLemmaToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      spernerLemmaFromEventFlow (spernerLemmaToEventFlow x) =
        spernerLemmaFromEventFlow (spernerLemmaToEventFlow y) :=
    congrArg spernerLemmaFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SpernerLemmaTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SpernerLemmaTasteGate_single_carrier_alignment_round_trip y)))

instance spernerLemmaBHistCarrier : BHistCarrier SpernerLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := spernerLemmaToEventFlow
  fromEventFlow := spernerLemmaFromEventFlow

instance spernerLemmaChapterTasteGate : ChapterTasteGate SpernerLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change spernerLemmaFromEventFlow (spernerLemmaToEventFlow x) = some x
    exact SpernerLemmaTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SpernerLemmaTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate SpernerLemmaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  spernerLemmaChapterTasteGate

theorem SpernerLemmaTasteGate_single_carrier_alignment :
    (∀ h : BHist, spernerLemmaDecodeBHist (spernerLemmaEncodeBHist h) = h) ∧
      (∀ x : SpernerLemmaUp,
        spernerLemmaFromEventFlow (spernerLemmaToEventFlow x) = some x) ∧
        (∀ x y : SpernerLemmaUp,
          spernerLemmaToEventFlow x = spernerLemmaToEventFlow y → x = y) ∧
          spernerLemmaEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨SpernerLemmaTasteGate_single_carrier_alignment_decode_encode,
      SpernerLemmaTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => SpernerLemmaTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SpernerLemmaUp
