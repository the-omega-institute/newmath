import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DedekindLocatedIntervalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DedekindLocatedIntervalUp : Type where
  | mk
      (locatedInterval rationalBracket dyadicTolerance streamWindow regularReadback
        realSeal locatedSpace transport replay provenance localName : BHist) :
      DedekindLocatedIntervalUp
  deriving DecidableEq

def dedekindLocatedIntervalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dedekindLocatedIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dedekindLocatedIntervalEncodeBHist h

def dedekindLocatedIntervalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dedekindLocatedIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dedekindLocatedIntervalDecodeBHist tail)

private theorem dedekindLocatedInterval_decode_encode_bhist :
    ∀ h : BHist,
      dedekindLocatedIntervalDecodeBHist (dedekindLocatedIntervalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dedekindLocatedIntervalFields : DedekindLocatedIntervalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DedekindLocatedIntervalUp.mk locatedInterval rationalBracket dyadicTolerance
      streamWindow regularReadback realSeal locatedSpace transport replay provenance localName =>
      [locatedInterval, rationalBracket, dyadicTolerance, streamWindow, regularReadback,
        realSeal, locatedSpace, transport, replay, provenance, localName]

def dedekindLocatedIntervalToEventFlow : DedekindLocatedIntervalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dedekindLocatedIntervalFields x).map dedekindLocatedIntervalEncodeBHist

private def dedekindLocatedIntervalEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dedekindLocatedIntervalEventAtDefault index rest

def dedekindLocatedIntervalFromEventFlow : EventFlow → Option DedekindLocatedIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (DedekindLocatedIntervalUp.mk
        (dedekindLocatedIntervalDecodeBHist (dedekindLocatedIntervalEventAtDefault 0 ef))
        (dedekindLocatedIntervalDecodeBHist (dedekindLocatedIntervalEventAtDefault 1 ef))
        (dedekindLocatedIntervalDecodeBHist (dedekindLocatedIntervalEventAtDefault 2 ef))
        (dedekindLocatedIntervalDecodeBHist (dedekindLocatedIntervalEventAtDefault 3 ef))
        (dedekindLocatedIntervalDecodeBHist (dedekindLocatedIntervalEventAtDefault 4 ef))
        (dedekindLocatedIntervalDecodeBHist (dedekindLocatedIntervalEventAtDefault 5 ef))
        (dedekindLocatedIntervalDecodeBHist (dedekindLocatedIntervalEventAtDefault 6 ef))
        (dedekindLocatedIntervalDecodeBHist (dedekindLocatedIntervalEventAtDefault 7 ef))
        (dedekindLocatedIntervalDecodeBHist (dedekindLocatedIntervalEventAtDefault 8 ef))
        (dedekindLocatedIntervalDecodeBHist (dedekindLocatedIntervalEventAtDefault 9 ef))
        (dedekindLocatedIntervalDecodeBHist (dedekindLocatedIntervalEventAtDefault 10 ef)))

private theorem dedekindLocatedInterval_round_trip :
    ∀ x : DedekindLocatedIntervalUp,
      dedekindLocatedIntervalFromEventFlow
          (dedekindLocatedIntervalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk locatedInterval rationalBracket dyadicTolerance streamWindow regularReadback realSeal
      locatedSpace transport replay provenance localName =>
      change
        some
          (DedekindLocatedIntervalUp.mk
            (dedekindLocatedIntervalDecodeBHist
              (dedekindLocatedIntervalEncodeBHist locatedInterval))
            (dedekindLocatedIntervalDecodeBHist
              (dedekindLocatedIntervalEncodeBHist rationalBracket))
            (dedekindLocatedIntervalDecodeBHist
              (dedekindLocatedIntervalEncodeBHist dyadicTolerance))
            (dedekindLocatedIntervalDecodeBHist
              (dedekindLocatedIntervalEncodeBHist streamWindow))
            (dedekindLocatedIntervalDecodeBHist
              (dedekindLocatedIntervalEncodeBHist regularReadback))
            (dedekindLocatedIntervalDecodeBHist
              (dedekindLocatedIntervalEncodeBHist realSeal))
            (dedekindLocatedIntervalDecodeBHist
              (dedekindLocatedIntervalEncodeBHist locatedSpace))
            (dedekindLocatedIntervalDecodeBHist
              (dedekindLocatedIntervalEncodeBHist transport))
            (dedekindLocatedIntervalDecodeBHist
              (dedekindLocatedIntervalEncodeBHist replay))
            (dedekindLocatedIntervalDecodeBHist
              (dedekindLocatedIntervalEncodeBHist provenance))
            (dedekindLocatedIntervalDecodeBHist
              (dedekindLocatedIntervalEncodeBHist localName))) =
          some
            (DedekindLocatedIntervalUp.mk locatedInterval rationalBracket dyadicTolerance
              streamWindow regularReadback realSeal locatedSpace transport replay provenance
              localName)
      rw [dedekindLocatedInterval_decode_encode_bhist locatedInterval,
        dedekindLocatedInterval_decode_encode_bhist rationalBracket,
        dedekindLocatedInterval_decode_encode_bhist dyadicTolerance,
        dedekindLocatedInterval_decode_encode_bhist streamWindow,
        dedekindLocatedInterval_decode_encode_bhist regularReadback,
        dedekindLocatedInterval_decode_encode_bhist realSeal,
        dedekindLocatedInterval_decode_encode_bhist locatedSpace,
        dedekindLocatedInterval_decode_encode_bhist transport,
        dedekindLocatedInterval_decode_encode_bhist replay,
        dedekindLocatedInterval_decode_encode_bhist provenance,
        dedekindLocatedInterval_decode_encode_bhist localName]

private theorem dedekindLocatedIntervalToEventFlow_injective {x y : DedekindLocatedIntervalUp} :
    dedekindLocatedIntervalToEventFlow x = dedekindLocatedIntervalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dedekindLocatedIntervalFromEventFlow (dedekindLocatedIntervalToEventFlow x) =
        dedekindLocatedIntervalFromEventFlow (dedekindLocatedIntervalToEventFlow y) :=
    congrArg dedekindLocatedIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dedekindLocatedInterval_round_trip x).symm
      (Eq.trans hread (dedekindLocatedInterval_round_trip y)))

private theorem dedekindLocatedInterval_field_faithful :
    ∀ x y : DedekindLocatedIntervalUp, dedekindLocatedIntervalFields x =
      dedekindLocatedIntervalFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk locatedInterval₁ rationalBracket₁ dyadicTolerance₁ streamWindow₁ regularReadback₁
      realSeal₁ locatedSpace₁ transport₁ replay₁ provenance₁ localName₁ =>
      cases y with
      | mk locatedInterval₂ rationalBracket₂ dyadicTolerance₂ streamWindow₂ regularReadback₂
          realSeal₂ locatedSpace₂ transport₂ replay₂ provenance₂ localName₂ =>
          cases hfields
          rfl

instance dedekindLocatedIntervalBHistCarrier : BHistCarrier DedekindLocatedIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dedekindLocatedIntervalToEventFlow
  fromEventFlow := dedekindLocatedIntervalFromEventFlow

instance dedekindLocatedIntervalChapterTasteGate :
    ChapterTasteGate DedekindLocatedIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dedekindLocatedIntervalFromEventFlow (dedekindLocatedIntervalToEventFlow x) = some x
    exact dedekindLocatedInterval_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dedekindLocatedIntervalToEventFlow_injective heq)

instance dedekindLocatedIntervalFieldFaithful :
    FieldFaithful DedekindLocatedIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dedekindLocatedIntervalFields
  field_faithful := dedekindLocatedInterval_field_faithful

def taste_gate : ChapterTasteGate DedekindLocatedIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dedekindLocatedIntervalChapterTasteGate

theorem DedekindLocatedIntervalTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      dedekindLocatedIntervalDecodeBHist (dedekindLocatedIntervalEncodeBHist h) = h) ∧
      (∀ x : DedekindLocatedIntervalUp,
        dedekindLocatedIntervalFromEventFlow
          (dedekindLocatedIntervalToEventFlow x) = some x) ∧
        (∀ x y : DedekindLocatedIntervalUp,
          dedekindLocatedIntervalToEventFlow x = dedekindLocatedIntervalToEventFlow y →
            x = y) ∧
          dedekindLocatedIntervalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨dedekindLocatedInterval_decode_encode_bhist,
      dedekindLocatedInterval_round_trip,
      (fun _ _ heq => dedekindLocatedIntervalToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DedekindLocatedIntervalUp
