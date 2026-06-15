import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConstructiveImplicitFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConstructiveImplicitFunctionUp : Type where
  | mk (F J A M I H C P N : BHist) : ConstructiveImplicitFunctionUp
  deriving DecidableEq

def constructiveImplicitFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: constructiveImplicitFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: constructiveImplicitFunctionEncodeBHist h

def constructiveImplicitFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (constructiveImplicitFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (constructiveImplicitFunctionDecodeBHist tail)

private theorem ConstructiveImplicitFunctionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      constructiveImplicitFunctionDecodeBHist
        (constructiveImplicitFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def constructiveImplicitFunctionToEventFlow :
    ConstructiveImplicitFunctionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ConstructiveImplicitFunctionUp.mk F J A M I H C P N =>
      [constructiveImplicitFunctionEncodeBHist F,
        constructiveImplicitFunctionEncodeBHist J,
        constructiveImplicitFunctionEncodeBHist A,
        constructiveImplicitFunctionEncodeBHist M,
        constructiveImplicitFunctionEncodeBHist I,
        constructiveImplicitFunctionEncodeBHist H,
        constructiveImplicitFunctionEncodeBHist C,
        constructiveImplicitFunctionEncodeBHist P,
        constructiveImplicitFunctionEncodeBHist N]

private def constructiveImplicitFunctionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => constructiveImplicitFunctionEventAtDefault index rest

def constructiveImplicitFunctionFromEventFlow :
    EventFlow → Option ConstructiveImplicitFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (ConstructiveImplicitFunctionUp.mk
        (constructiveImplicitFunctionDecodeBHist
          (constructiveImplicitFunctionEventAtDefault 0 ef))
        (constructiveImplicitFunctionDecodeBHist
          (constructiveImplicitFunctionEventAtDefault 1 ef))
        (constructiveImplicitFunctionDecodeBHist
          (constructiveImplicitFunctionEventAtDefault 2 ef))
        (constructiveImplicitFunctionDecodeBHist
          (constructiveImplicitFunctionEventAtDefault 3 ef))
        (constructiveImplicitFunctionDecodeBHist
          (constructiveImplicitFunctionEventAtDefault 4 ef))
        (constructiveImplicitFunctionDecodeBHist
          (constructiveImplicitFunctionEventAtDefault 5 ef))
        (constructiveImplicitFunctionDecodeBHist
          (constructiveImplicitFunctionEventAtDefault 6 ef))
        (constructiveImplicitFunctionDecodeBHist
          (constructiveImplicitFunctionEventAtDefault 7 ef))
        (constructiveImplicitFunctionDecodeBHist
          (constructiveImplicitFunctionEventAtDefault 8 ef)))

private theorem ConstructiveImplicitFunctionTasteGate_single_carrier_alignment_round_trip
    (x : ConstructiveImplicitFunctionUp) :
    constructiveImplicitFunctionFromEventFlow
      (constructiveImplicitFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F J A M I H C P N =>
      change
        some
            (ConstructiveImplicitFunctionUp.mk
              (constructiveImplicitFunctionDecodeBHist
                (constructiveImplicitFunctionEncodeBHist F))
              (constructiveImplicitFunctionDecodeBHist
                (constructiveImplicitFunctionEncodeBHist J))
              (constructiveImplicitFunctionDecodeBHist
                (constructiveImplicitFunctionEncodeBHist A))
              (constructiveImplicitFunctionDecodeBHist
                (constructiveImplicitFunctionEncodeBHist M))
              (constructiveImplicitFunctionDecodeBHist
                (constructiveImplicitFunctionEncodeBHist I))
              (constructiveImplicitFunctionDecodeBHist
                (constructiveImplicitFunctionEncodeBHist H))
              (constructiveImplicitFunctionDecodeBHist
                (constructiveImplicitFunctionEncodeBHist C))
              (constructiveImplicitFunctionDecodeBHist
                (constructiveImplicitFunctionEncodeBHist P))
              (constructiveImplicitFunctionDecodeBHist
                (constructiveImplicitFunctionEncodeBHist N))) =
          some (ConstructiveImplicitFunctionUp.mk F J A M I H C P N)
      rw [ConstructiveImplicitFunctionTasteGate_single_carrier_alignment_decode_encode F,
        ConstructiveImplicitFunctionTasteGate_single_carrier_alignment_decode_encode J,
        ConstructiveImplicitFunctionTasteGate_single_carrier_alignment_decode_encode A,
        ConstructiveImplicitFunctionTasteGate_single_carrier_alignment_decode_encode M,
        ConstructiveImplicitFunctionTasteGate_single_carrier_alignment_decode_encode I,
        ConstructiveImplicitFunctionTasteGate_single_carrier_alignment_decode_encode H,
        ConstructiveImplicitFunctionTasteGate_single_carrier_alignment_decode_encode C,
        ConstructiveImplicitFunctionTasteGate_single_carrier_alignment_decode_encode P,
        ConstructiveImplicitFunctionTasteGate_single_carrier_alignment_decode_encode N]

private theorem ConstructiveImplicitFunctionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ConstructiveImplicitFunctionUp} :
    constructiveImplicitFunctionToEventFlow x =
        constructiveImplicitFunctionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      constructiveImplicitFunctionFromEventFlow
          (constructiveImplicitFunctionToEventFlow x) =
        constructiveImplicitFunctionFromEventFlow
          (constructiveImplicitFunctionToEventFlow y) :=
    congrArg constructiveImplicitFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ConstructiveImplicitFunctionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ConstructiveImplicitFunctionTasteGate_single_carrier_alignment_round_trip y)))

instance constructiveImplicitFunctionBHistCarrier :
    BHistCarrier ConstructiveImplicitFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := constructiveImplicitFunctionToEventFlow
  fromEventFlow := constructiveImplicitFunctionFromEventFlow

instance constructiveImplicitFunctionChapterTasteGate :
    ChapterTasteGate ConstructiveImplicitFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      constructiveImplicitFunctionFromEventFlow
        (constructiveImplicitFunctionToEventFlow x) = some x
    exact ConstructiveImplicitFunctionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ConstructiveImplicitFunctionTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def taste_gate : ChapterTasteGate ConstructiveImplicitFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  constructiveImplicitFunctionChapterTasteGate

theorem ConstructiveImplicitFunctionTasteGate_single_carrier_alignment :
    (∃ carrier : BHistCarrier ConstructiveImplicitFunctionUp,
      Nonempty (@ChapterTasteGate ConstructiveImplicitFunctionUp carrier)) ∧
      (∀ h : BHist,
        constructiveImplicitFunctionDecodeBHist
          (constructiveImplicitFunctionEncodeBHist h) = h) ∧
        (∀ x : ConstructiveImplicitFunctionUp,
          constructiveImplicitFunctionFromEventFlow
            (constructiveImplicitFunctionToEventFlow x) = some x) ∧
          constructiveImplicitFunctionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨constructiveImplicitFunctionBHistCarrier,
        ⟨constructiveImplicitFunctionChapterTasteGate⟩⟩,
      ConstructiveImplicitFunctionTasteGate_single_carrier_alignment_decode_encode,
      ConstructiveImplicitFunctionTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.ConstructiveImplicitFunctionUp
