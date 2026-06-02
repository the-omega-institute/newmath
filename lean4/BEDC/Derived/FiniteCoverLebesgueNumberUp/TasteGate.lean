import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteCoverLebesgueNumberUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteCoverLebesgueNumberUp : Type where
  | mk
      (compactMetric metric finiteCover radiusLedger lemmaRoute uniformHandoff transport replay
        provenance localName : BHist) :
      FiniteCoverLebesgueNumberUp

def finiteCoverLebesgueNumberEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteCoverLebesgueNumberEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteCoverLebesgueNumberEncodeBHist h

def finiteCoverLebesgueNumberDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteCoverLebesgueNumberDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteCoverLebesgueNumberDecodeBHist tail)

private theorem finiteCoverLebesgueNumber_decode_encode_bhist :
    ∀ h : BHist,
      finiteCoverLebesgueNumberDecodeBHist
        (finiteCoverLebesgueNumberEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteCoverLebesgueNumberFields :
    FiniteCoverLebesgueNumberUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteCoverLebesgueNumberUp.mk compactMetric metric finiteCover radiusLedger lemmaRoute
      uniformHandoff transport replay provenance localName =>
      [compactMetric, metric, finiteCover, radiusLedger, lemmaRoute, uniformHandoff,
        transport, replay, provenance, localName]

def finiteCoverLebesgueNumberToEventFlow :
    FiniteCoverLebesgueNumberUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (finiteCoverLebesgueNumberFields x).map finiteCoverLebesgueNumberEncodeBHist

private def finiteCoverLebesgueNumberEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      finiteCoverLebesgueNumberEventAtDefault index rest

def finiteCoverLebesgueNumberFromEventFlow
    (flow : EventFlow) : Option FiniteCoverLebesgueNumberUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteCoverLebesgueNumberUp.mk
      (finiteCoverLebesgueNumberDecodeBHist
        (finiteCoverLebesgueNumberEventAtDefault 0 flow))
      (finiteCoverLebesgueNumberDecodeBHist
        (finiteCoverLebesgueNumberEventAtDefault 1 flow))
      (finiteCoverLebesgueNumberDecodeBHist
        (finiteCoverLebesgueNumberEventAtDefault 2 flow))
      (finiteCoverLebesgueNumberDecodeBHist
        (finiteCoverLebesgueNumberEventAtDefault 3 flow))
      (finiteCoverLebesgueNumberDecodeBHist
        (finiteCoverLebesgueNumberEventAtDefault 4 flow))
      (finiteCoverLebesgueNumberDecodeBHist
        (finiteCoverLebesgueNumberEventAtDefault 5 flow))
      (finiteCoverLebesgueNumberDecodeBHist
        (finiteCoverLebesgueNumberEventAtDefault 6 flow))
      (finiteCoverLebesgueNumberDecodeBHist
        (finiteCoverLebesgueNumberEventAtDefault 7 flow))
      (finiteCoverLebesgueNumberDecodeBHist
        (finiteCoverLebesgueNumberEventAtDefault 8 flow))
      (finiteCoverLebesgueNumberDecodeBHist
        (finiteCoverLebesgueNumberEventAtDefault 9 flow)))

private theorem finiteCoverLebesgueNumber_round_trip :
    ∀ x : FiniteCoverLebesgueNumberUp,
      finiteCoverLebesgueNumberFromEventFlow
        (finiteCoverLebesgueNumberToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk compactMetric metric finiteCover radiusLedger lemmaRoute uniformHandoff transport
      replay provenance localName =>
      change
        some
          (FiniteCoverLebesgueNumberUp.mk
            (finiteCoverLebesgueNumberDecodeBHist
              (finiteCoverLebesgueNumberEncodeBHist compactMetric))
            (finiteCoverLebesgueNumberDecodeBHist
              (finiteCoverLebesgueNumberEncodeBHist metric))
            (finiteCoverLebesgueNumberDecodeBHist
              (finiteCoverLebesgueNumberEncodeBHist finiteCover))
            (finiteCoverLebesgueNumberDecodeBHist
              (finiteCoverLebesgueNumberEncodeBHist radiusLedger))
            (finiteCoverLebesgueNumberDecodeBHist
              (finiteCoverLebesgueNumberEncodeBHist lemmaRoute))
            (finiteCoverLebesgueNumberDecodeBHist
              (finiteCoverLebesgueNumberEncodeBHist uniformHandoff))
            (finiteCoverLebesgueNumberDecodeBHist
              (finiteCoverLebesgueNumberEncodeBHist transport))
            (finiteCoverLebesgueNumberDecodeBHist
              (finiteCoverLebesgueNumberEncodeBHist replay))
            (finiteCoverLebesgueNumberDecodeBHist
              (finiteCoverLebesgueNumberEncodeBHist provenance))
            (finiteCoverLebesgueNumberDecodeBHist
              (finiteCoverLebesgueNumberEncodeBHist localName))) =
          some
            (FiniteCoverLebesgueNumberUp.mk compactMetric metric finiteCover radiusLedger
              lemmaRoute uniformHandoff transport replay provenance localName)
      rw [finiteCoverLebesgueNumber_decode_encode_bhist compactMetric,
        finiteCoverLebesgueNumber_decode_encode_bhist metric,
        finiteCoverLebesgueNumber_decode_encode_bhist finiteCover,
        finiteCoverLebesgueNumber_decode_encode_bhist radiusLedger,
        finiteCoverLebesgueNumber_decode_encode_bhist lemmaRoute,
        finiteCoverLebesgueNumber_decode_encode_bhist uniformHandoff,
        finiteCoverLebesgueNumber_decode_encode_bhist transport,
        finiteCoverLebesgueNumber_decode_encode_bhist replay,
        finiteCoverLebesgueNumber_decode_encode_bhist provenance,
        finiteCoverLebesgueNumber_decode_encode_bhist localName]

private theorem finiteCoverLebesgueNumberToEventFlow_injective
    {x y : FiniteCoverLebesgueNumberUp} :
    finiteCoverLebesgueNumberToEventFlow x =
      finiteCoverLebesgueNumberToEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have readEq :
      finiteCoverLebesgueNumberFromEventFlow
          (finiteCoverLebesgueNumberToEventFlow x) =
        finiteCoverLebesgueNumberFromEventFlow
          (finiteCoverLebesgueNumberToEventFlow y) :=
    congrArg finiteCoverLebesgueNumberFromEventFlow heq
  exact
    Option.some.inj
      (Eq.trans (finiteCoverLebesgueNumber_round_trip x).symm
        (Eq.trans readEq (finiteCoverLebesgueNumber_round_trip y)))

instance finiteCoverLebesgueNumberBHistCarrier :
    BHistCarrier FiniteCoverLebesgueNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteCoverLebesgueNumberToEventFlow
  fromEventFlow := finiteCoverLebesgueNumberFromEventFlow

instance finiteCoverLebesgueNumberChapterTasteGate :
    ChapterTasteGate FiniteCoverLebesgueNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteCoverLebesgueNumberFromEventFlow
        (finiteCoverLebesgueNumberToEventFlow x) = some x
    exact finiteCoverLebesgueNumber_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteCoverLebesgueNumberToEventFlow_injective heq)

def taste_gate : ChapterTasteGate FiniteCoverLebesgueNumberUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteCoverLebesgueNumberChapterTasteGate

theorem FiniteCoverLebesgueNumberTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finiteCoverLebesgueNumberDecodeBHist
        (finiteCoverLebesgueNumberEncodeBHist h) = h) ∧
      (∀ x : FiniteCoverLebesgueNumberUp,
        finiteCoverLebesgueNumberFromEventFlow
          (finiteCoverLebesgueNumberToEventFlow x) = some x) ∧
        (∀ x y : FiniteCoverLebesgueNumberUp,
          finiteCoverLebesgueNumberToEventFlow x =
            finiteCoverLebesgueNumberToEventFlow y →
              x = y) ∧
          finiteCoverLebesgueNumberEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨finiteCoverLebesgueNumber_decode_encode_bhist,
      finiteCoverLebesgueNumber_round_trip,
      (fun _ _ heq => finiteCoverLebesgueNumberToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FiniteCoverLebesgueNumberUp.TasteGate
