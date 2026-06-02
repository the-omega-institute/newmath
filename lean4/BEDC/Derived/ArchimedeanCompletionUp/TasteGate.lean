import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ArchimedeanCompletionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ArchimedeanCompletionUp : Type where
  | mk
      (fieldSource cofinality regularReadback toleranceLedger orderComparison realSeal
        transport replay provenance localName : BHist) :
      ArchimedeanCompletionUp

def archimedeanCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: archimedeanCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: archimedeanCompletionEncodeBHist h

def archimedeanCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (archimedeanCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (archimedeanCompletionDecodeBHist tail)

private theorem archimedeanCompletion_decode_encode_bhist :
    ∀ h : BHist,
      archimedeanCompletionDecodeBHist
        (archimedeanCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def archimedeanCompletionFields :
    ArchimedeanCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ArchimedeanCompletionUp.mk fieldSource cofinality regularReadback toleranceLedger
      orderComparison realSeal transport replay provenance localName =>
      [fieldSource, cofinality, regularReadback, toleranceLedger, orderComparison, realSeal,
        transport, replay, provenance, localName]

def archimedeanCompletionToEventFlow :
    ArchimedeanCompletionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (archimedeanCompletionFields x).map archimedeanCompletionEncodeBHist

private def archimedeanCompletionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      archimedeanCompletionEventAtDefault index rest

def archimedeanCompletionFromEventFlow
    (flow : EventFlow) : Option ArchimedeanCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ArchimedeanCompletionUp.mk
      (archimedeanCompletionDecodeBHist
        (archimedeanCompletionEventAtDefault 0 flow))
      (archimedeanCompletionDecodeBHist
        (archimedeanCompletionEventAtDefault 1 flow))
      (archimedeanCompletionDecodeBHist
        (archimedeanCompletionEventAtDefault 2 flow))
      (archimedeanCompletionDecodeBHist
        (archimedeanCompletionEventAtDefault 3 flow))
      (archimedeanCompletionDecodeBHist
        (archimedeanCompletionEventAtDefault 4 flow))
      (archimedeanCompletionDecodeBHist
        (archimedeanCompletionEventAtDefault 5 flow))
      (archimedeanCompletionDecodeBHist
        (archimedeanCompletionEventAtDefault 6 flow))
      (archimedeanCompletionDecodeBHist
        (archimedeanCompletionEventAtDefault 7 flow))
      (archimedeanCompletionDecodeBHist
        (archimedeanCompletionEventAtDefault 8 flow))
      (archimedeanCompletionDecodeBHist
        (archimedeanCompletionEventAtDefault 9 flow)))

private theorem archimedeanCompletion_round_trip :
    ∀ x : ArchimedeanCompletionUp,
      archimedeanCompletionFromEventFlow
        (archimedeanCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk fieldSource cofinality regularReadback toleranceLedger orderComparison realSeal
      transport replay provenance localName =>
      change
        some
          (ArchimedeanCompletionUp.mk
            (archimedeanCompletionDecodeBHist
              (archimedeanCompletionEncodeBHist fieldSource))
            (archimedeanCompletionDecodeBHist
              (archimedeanCompletionEncodeBHist cofinality))
            (archimedeanCompletionDecodeBHist
              (archimedeanCompletionEncodeBHist regularReadback))
            (archimedeanCompletionDecodeBHist
              (archimedeanCompletionEncodeBHist toleranceLedger))
            (archimedeanCompletionDecodeBHist
              (archimedeanCompletionEncodeBHist orderComparison))
            (archimedeanCompletionDecodeBHist
              (archimedeanCompletionEncodeBHist realSeal))
            (archimedeanCompletionDecodeBHist
              (archimedeanCompletionEncodeBHist transport))
            (archimedeanCompletionDecodeBHist
              (archimedeanCompletionEncodeBHist replay))
            (archimedeanCompletionDecodeBHist
              (archimedeanCompletionEncodeBHist provenance))
            (archimedeanCompletionDecodeBHist
              (archimedeanCompletionEncodeBHist localName))) =
          some
            (ArchimedeanCompletionUp.mk fieldSource cofinality regularReadback
              toleranceLedger orderComparison realSeal transport replay provenance localName)
      rw [archimedeanCompletion_decode_encode_bhist fieldSource,
        archimedeanCompletion_decode_encode_bhist cofinality,
        archimedeanCompletion_decode_encode_bhist regularReadback,
        archimedeanCompletion_decode_encode_bhist toleranceLedger,
        archimedeanCompletion_decode_encode_bhist orderComparison,
        archimedeanCompletion_decode_encode_bhist realSeal,
        archimedeanCompletion_decode_encode_bhist transport,
        archimedeanCompletion_decode_encode_bhist replay,
        archimedeanCompletion_decode_encode_bhist provenance,
        archimedeanCompletion_decode_encode_bhist localName]

private theorem archimedeanCompletionToEventFlow_injective
    {x y : ArchimedeanCompletionUp} :
    archimedeanCompletionToEventFlow x =
      archimedeanCompletionToEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have readEq :
      archimedeanCompletionFromEventFlow
          (archimedeanCompletionToEventFlow x) =
        archimedeanCompletionFromEventFlow
          (archimedeanCompletionToEventFlow y) :=
    congrArg archimedeanCompletionFromEventFlow heq
  exact
    Option.some.inj
      (Eq.trans (archimedeanCompletion_round_trip x).symm
        (Eq.trans readEq (archimedeanCompletion_round_trip y)))

instance archimedeanCompletionBHistCarrier :
    BHistCarrier ArchimedeanCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := archimedeanCompletionToEventFlow
  fromEventFlow := archimedeanCompletionFromEventFlow

instance archimedeanCompletionChapterTasteGate :
    ChapterTasteGate ArchimedeanCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      archimedeanCompletionFromEventFlow
        (archimedeanCompletionToEventFlow x) = some x
    exact archimedeanCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (archimedeanCompletionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ArchimedeanCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  archimedeanCompletionChapterTasteGate

theorem ArchimedeanCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      archimedeanCompletionDecodeBHist
        (archimedeanCompletionEncodeBHist h) = h) ∧
      (∀ x : ArchimedeanCompletionUp,
        archimedeanCompletionFromEventFlow
          (archimedeanCompletionToEventFlow x) = some x) ∧
        (∀ x y : ArchimedeanCompletionUp,
          archimedeanCompletionToEventFlow x =
            archimedeanCompletionToEventFlow y →
              x = y) ∧
          archimedeanCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨archimedeanCompletion_decode_encode_bhist,
      archimedeanCompletion_round_trip,
      (fun _ _ heq => archimedeanCompletionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ArchimedeanCompletionUp.TasteGate
