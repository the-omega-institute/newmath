import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactRegularCauchySubsequenceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactRegularCauchySubsequenceUp : Type where
  | mk
      (compactSource sourceWindow subsequenceLedger selectedWindow dyadicTolerance
        rationalReadback realSeal transport replay provenance localName : BHist) :
      CompactRegularCauchySubsequenceUp
  deriving DecidableEq

def compactRegularCauchySubsequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactRegularCauchySubsequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactRegularCauchySubsequenceEncodeBHist h

def compactRegularCauchySubsequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactRegularCauchySubsequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactRegularCauchySubsequenceDecodeBHist tail)

private theorem compactRegularCauchySubsequence_decode_encode_bhist :
    ∀ h : BHist,
      compactRegularCauchySubsequenceDecodeBHist
        (compactRegularCauchySubsequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactRegularCauchySubsequenceFields :
    CompactRegularCauchySubsequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactRegularCauchySubsequenceUp.mk compactSource sourceWindow subsequenceLedger
      selectedWindow dyadicTolerance rationalReadback realSeal transport replay provenance
        localName =>
      [compactSource, sourceWindow, subsequenceLedger, selectedWindow, dyadicTolerance,
        rationalReadback, realSeal, transport, replay, provenance, localName]

def compactRegularCauchySubsequenceToEventFlow :
    CompactRegularCauchySubsequenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (compactRegularCauchySubsequenceFields x).map compactRegularCauchySubsequenceEncodeBHist

private def compactRegularCauchySubsequenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactRegularCauchySubsequenceEventAtDefault index rest

def compactRegularCauchySubsequenceFromEventFlow :
    EventFlow → Option CompactRegularCauchySubsequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CompactRegularCauchySubsequenceUp.mk
        (compactRegularCauchySubsequenceDecodeBHist
          (compactRegularCauchySubsequenceEventAtDefault 0 ef))
        (compactRegularCauchySubsequenceDecodeBHist
          (compactRegularCauchySubsequenceEventAtDefault 1 ef))
        (compactRegularCauchySubsequenceDecodeBHist
          (compactRegularCauchySubsequenceEventAtDefault 2 ef))
        (compactRegularCauchySubsequenceDecodeBHist
          (compactRegularCauchySubsequenceEventAtDefault 3 ef))
        (compactRegularCauchySubsequenceDecodeBHist
          (compactRegularCauchySubsequenceEventAtDefault 4 ef))
        (compactRegularCauchySubsequenceDecodeBHist
          (compactRegularCauchySubsequenceEventAtDefault 5 ef))
        (compactRegularCauchySubsequenceDecodeBHist
          (compactRegularCauchySubsequenceEventAtDefault 6 ef))
        (compactRegularCauchySubsequenceDecodeBHist
          (compactRegularCauchySubsequenceEventAtDefault 7 ef))
        (compactRegularCauchySubsequenceDecodeBHist
          (compactRegularCauchySubsequenceEventAtDefault 8 ef))
        (compactRegularCauchySubsequenceDecodeBHist
          (compactRegularCauchySubsequenceEventAtDefault 9 ef))
        (compactRegularCauchySubsequenceDecodeBHist
          (compactRegularCauchySubsequenceEventAtDefault 10 ef)))

instance compactRegularCauchySubsequenceBHistCarrier :
    BHistCarrier CompactRegularCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactRegularCauchySubsequenceToEventFlow
  fromEventFlow := compactRegularCauchySubsequenceFromEventFlow

private theorem compactRegularCauchySubsequence_round_trip :
    ∀ x : CompactRegularCauchySubsequenceUp,
      compactRegularCauchySubsequenceFromEventFlow
        (compactRegularCauchySubsequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk compactSource sourceWindow subsequenceLedger selectedWindow dyadicTolerance
      rationalReadback realSeal transport replay provenance localName =>
      change
        some
            (CompactRegularCauchySubsequenceUp.mk
              (compactRegularCauchySubsequenceDecodeBHist
                (compactRegularCauchySubsequenceEncodeBHist compactSource))
              (compactRegularCauchySubsequenceDecodeBHist
                (compactRegularCauchySubsequenceEncodeBHist sourceWindow))
              (compactRegularCauchySubsequenceDecodeBHist
                (compactRegularCauchySubsequenceEncodeBHist subsequenceLedger))
              (compactRegularCauchySubsequenceDecodeBHist
                (compactRegularCauchySubsequenceEncodeBHist selectedWindow))
              (compactRegularCauchySubsequenceDecodeBHist
                (compactRegularCauchySubsequenceEncodeBHist dyadicTolerance))
              (compactRegularCauchySubsequenceDecodeBHist
                (compactRegularCauchySubsequenceEncodeBHist rationalReadback))
              (compactRegularCauchySubsequenceDecodeBHist
                (compactRegularCauchySubsequenceEncodeBHist realSeal))
              (compactRegularCauchySubsequenceDecodeBHist
                (compactRegularCauchySubsequenceEncodeBHist transport))
              (compactRegularCauchySubsequenceDecodeBHist
                (compactRegularCauchySubsequenceEncodeBHist replay))
              (compactRegularCauchySubsequenceDecodeBHist
                (compactRegularCauchySubsequenceEncodeBHist provenance))
              (compactRegularCauchySubsequenceDecodeBHist
                (compactRegularCauchySubsequenceEncodeBHist localName))) =
          some
            (CompactRegularCauchySubsequenceUp.mk compactSource sourceWindow
              subsequenceLedger selectedWindow dyadicTolerance rationalReadback realSeal
              transport replay provenance localName)
      rw [compactRegularCauchySubsequence_decode_encode_bhist compactSource]
      rw [compactRegularCauchySubsequence_decode_encode_bhist sourceWindow]
      rw [compactRegularCauchySubsequence_decode_encode_bhist subsequenceLedger]
      rw [compactRegularCauchySubsequence_decode_encode_bhist selectedWindow]
      rw [compactRegularCauchySubsequence_decode_encode_bhist dyadicTolerance]
      rw [compactRegularCauchySubsequence_decode_encode_bhist rationalReadback]
      rw [compactRegularCauchySubsequence_decode_encode_bhist realSeal]
      rw [compactRegularCauchySubsequence_decode_encode_bhist transport]
      rw [compactRegularCauchySubsequence_decode_encode_bhist replay]
      rw [compactRegularCauchySubsequence_decode_encode_bhist provenance]
      rw [compactRegularCauchySubsequence_decode_encode_bhist localName]

private theorem compactRegularCauchySubsequenceToEventFlow_injective
    {x y : CompactRegularCauchySubsequenceUp} :
    compactRegularCauchySubsequenceToEventFlow x =
      compactRegularCauchySubsequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          compactRegularCauchySubsequenceFromEventFlow
            (compactRegularCauchySubsequenceToEventFlow x) :=
        (compactRegularCauchySubsequence_round_trip x).symm
      _ =
          compactRegularCauchySubsequenceFromEventFlow
            (compactRegularCauchySubsequenceToEventFlow y) :=
        congrArg compactRegularCauchySubsequenceFromEventFlow hxy
      _ = some y := compactRegularCauchySubsequence_round_trip y
  exact Option.some.inj optionEq

instance compactRegularCauchySubsequenceChapterTasteGate :
    ChapterTasteGate CompactRegularCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactRegularCauchySubsequenceFromEventFlow
        (compactRegularCauchySubsequenceToEventFlow x) = some x
    exact compactRegularCauchySubsequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactRegularCauchySubsequenceToEventFlow_injective heq)

theorem CompactRegularCauchySubsequenceTasteGate_single_carrier_alignment :
    (forall h : BHist,
      compactRegularCauchySubsequenceDecodeBHist
        (compactRegularCauchySubsequenceEncodeBHist h) = h) /\
      (forall x : CompactRegularCauchySubsequenceUp,
        compactRegularCauchySubsequenceFromEventFlow
          (compactRegularCauchySubsequenceToEventFlow x) = some x) /\
      (forall x y : CompactRegularCauchySubsequenceUp,
        compactRegularCauchySubsequenceToEventFlow x =
          compactRegularCauchySubsequenceToEventFlow y -> x = y) /\
      compactRegularCauchySubsequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨compactRegularCauchySubsequence_decode_encode_bhist,
      ⟨compactRegularCauchySubsequence_round_trip,
        ⟨fun _ _ h => compactRegularCauchySubsequenceToEventFlow_injective h, rfl⟩⟩⟩

end BEDC.Derived.CompactRegularCauchySubsequenceUp.TasteGate
