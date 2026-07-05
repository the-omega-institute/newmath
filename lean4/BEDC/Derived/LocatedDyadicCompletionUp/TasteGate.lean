import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedDyadicCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedDyadicCompletionUp : Type where
  | mk
      (source dyadicLedger cauchyRoute completionSeal transport replay provenance localName :
        BHist) : LocatedDyadicCompletionUp
  deriving DecidableEq

def locatedDyadicCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedDyadicCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedDyadicCompletionEncodeBHist h

def locatedDyadicCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedDyadicCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedDyadicCompletionDecodeBHist tail)

private theorem locatedDyadicCompletion_decode_encode :
    ∀ h : BHist, locatedDyadicCompletionDecodeBHist
      (locatedDyadicCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedDyadicCompletionFields : LocatedDyadicCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedDyadicCompletionUp.mk source dyadicLedger cauchyRoute completionSeal transport
      replay provenance localName =>
      [source, dyadicLedger, cauchyRoute, completionSeal, transport, replay, provenance,
        localName]

def locatedDyadicCompletionToEventFlow : LocatedDyadicCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map locatedDyadicCompletionEncodeBHist (locatedDyadicCompletionFields x)

private def locatedDyadicCompletionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedDyadicCompletionEventAt index rest

def locatedDyadicCompletionFromEventFlow : EventFlow → Option LocatedDyadicCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (LocatedDyadicCompletionUp.mk
          (locatedDyadicCompletionDecodeBHist (locatedDyadicCompletionEventAt 0 ef))
          (locatedDyadicCompletionDecodeBHist (locatedDyadicCompletionEventAt 1 ef))
          (locatedDyadicCompletionDecodeBHist (locatedDyadicCompletionEventAt 2 ef))
          (locatedDyadicCompletionDecodeBHist (locatedDyadicCompletionEventAt 3 ef))
          (locatedDyadicCompletionDecodeBHist (locatedDyadicCompletionEventAt 4 ef))
          (locatedDyadicCompletionDecodeBHist (locatedDyadicCompletionEventAt 5 ef))
          (locatedDyadicCompletionDecodeBHist (locatedDyadicCompletionEventAt 6 ef))
          (locatedDyadicCompletionDecodeBHist (locatedDyadicCompletionEventAt 7 ef)))

private theorem locatedDyadicCompletion_round_trip :
    ∀ x : LocatedDyadicCompletionUp,
      locatedDyadicCompletionFromEventFlow (locatedDyadicCompletionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source dyadicLedger cauchyRoute completionSeal transport replay provenance localName =>
      change
        some
            (LocatedDyadicCompletionUp.mk
              (locatedDyadicCompletionDecodeBHist
                (locatedDyadicCompletionEncodeBHist source))
              (locatedDyadicCompletionDecodeBHist
                (locatedDyadicCompletionEncodeBHist dyadicLedger))
              (locatedDyadicCompletionDecodeBHist
                (locatedDyadicCompletionEncodeBHist cauchyRoute))
              (locatedDyadicCompletionDecodeBHist
                (locatedDyadicCompletionEncodeBHist completionSeal))
              (locatedDyadicCompletionDecodeBHist
                (locatedDyadicCompletionEncodeBHist transport))
              (locatedDyadicCompletionDecodeBHist
                (locatedDyadicCompletionEncodeBHist replay))
              (locatedDyadicCompletionDecodeBHist
                (locatedDyadicCompletionEncodeBHist provenance))
              (locatedDyadicCompletionDecodeBHist
                (locatedDyadicCompletionEncodeBHist localName))) =
          some
            (LocatedDyadicCompletionUp.mk source dyadicLedger cauchyRoute completionSeal
              transport replay provenance localName)
      rw [locatedDyadicCompletion_decode_encode source,
        locatedDyadicCompletion_decode_encode dyadicLedger,
        locatedDyadicCompletion_decode_encode cauchyRoute,
        locatedDyadicCompletion_decode_encode completionSeal,
        locatedDyadicCompletion_decode_encode transport,
        locatedDyadicCompletion_decode_encode replay,
        locatedDyadicCompletion_decode_encode provenance,
        locatedDyadicCompletion_decode_encode localName]

private theorem locatedDyadicCompletionToEventFlow_injective
    {x y : LocatedDyadicCompletionUp} :
    locatedDyadicCompletionToEventFlow x = locatedDyadicCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedDyadicCompletionFromEventFlow (locatedDyadicCompletionToEventFlow x) =
        locatedDyadicCompletionFromEventFlow (locatedDyadicCompletionToEventFlow y) :=
    congrArg locatedDyadicCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedDyadicCompletion_round_trip x).symm
      (Eq.trans hread (locatedDyadicCompletion_round_trip y)))

private theorem locatedDyadicCompletion_field_faithful :
    ∀ x y : LocatedDyadicCompletionUp,
      locatedDyadicCompletionFields x = locatedDyadicCompletionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source1 dyadicLedger1 cauchyRoute1 completionSeal1 transport1 replay1 provenance1
      localName1 =>
      cases y with
      | mk source2 dyadicLedger2 cauchyRoute2 completionSeal2 transport2 replay2 provenance2
          localName2 =>
          cases hfields
          rfl

instance locatedDyadicCompletionBHistCarrier :
    BHistCarrier LocatedDyadicCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedDyadicCompletionToEventFlow
  fromEventFlow := locatedDyadicCompletionFromEventFlow

instance locatedDyadicCompletionChapterTasteGate :
    ChapterTasteGate LocatedDyadicCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedDyadicCompletionFromEventFlow (locatedDyadicCompletionToEventFlow x) = some x
    exact locatedDyadicCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedDyadicCompletionToEventFlow_injective heq)

instance locatedDyadicCompletionFieldFaithful :
    FieldFaithful LocatedDyadicCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedDyadicCompletionFields
  field_faithful := locatedDyadicCompletion_field_faithful

instance locatedDyadicCompletionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial LocatedDyadicCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedDyadicCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      LocatedDyadicCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem LocatedDyadicCompletionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LocatedDyadicCompletionUp) ∧
      Nonempty (FieldFaithful LocatedDyadicCompletionUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial LocatedDyadicCompletionUp) ∧
      (∀ h : BHist,
        locatedDyadicCompletionDecodeBHist (locatedDyadicCompletionEncodeBHist h) = h) ∧
      (∀ x : LocatedDyadicCompletionUp,
        locatedDyadicCompletionFromEventFlow (locatedDyadicCompletionToEventFlow x) =
          some x) ∧
      locatedDyadicCompletionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨locatedDyadicCompletionChapterTasteGate⟩
  constructor
  · exact ⟨locatedDyadicCompletionFieldFaithful⟩
  constructor
  · exact ⟨locatedDyadicCompletionNontrivial⟩
  constructor
  · exact locatedDyadicCompletion_decode_encode
  constructor
  · exact locatedDyadicCompletion_round_trip
  · rfl

end BEDC.Derived.LocatedDyadicCompletionUp
