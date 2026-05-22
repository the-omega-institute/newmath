import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CantorCompletenessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CantorCompletenessUp : Type where
  | mk
      (nestedIntervals locatedEndpoints diameterLedger dyadicTolerances streamWindows
        regularReadback realSeal transports replay provenance localNameCert : BHist) :
      CantorCompletenessUp
  deriving DecidableEq

def cantorCompletenessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cantorCompletenessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cantorCompletenessEncodeBHist h

def cantorCompletenessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cantorCompletenessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cantorCompletenessDecodeBHist tail)

private theorem cantorCompleteness_decode_encode_bhist :
    ∀ h : BHist, cantorCompletenessDecodeBHist (cantorCompletenessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cantorCompletenessFields : CantorCompletenessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CantorCompletenessUp.mk nestedIntervals locatedEndpoints diameterLedger dyadicTolerances
      streamWindows regularReadback realSeal transports replay provenance localNameCert =>
      [nestedIntervals, locatedEndpoints, diameterLedger, dyadicTolerances, streamWindows,
        regularReadback, realSeal, transports, replay, provenance, localNameCert]

def cantorCompletenessToEventFlow : CantorCompletenessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cantorCompletenessFields x).map cantorCompletenessEncodeBHist

private def cantorCompletenessEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cantorCompletenessEventAtDefault index rest

def cantorCompletenessFromEventFlow : EventFlow → Option CantorCompletenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CantorCompletenessUp.mk
        (cantorCompletenessDecodeBHist (cantorCompletenessEventAtDefault 0 ef))
        (cantorCompletenessDecodeBHist (cantorCompletenessEventAtDefault 1 ef))
        (cantorCompletenessDecodeBHist (cantorCompletenessEventAtDefault 2 ef))
        (cantorCompletenessDecodeBHist (cantorCompletenessEventAtDefault 3 ef))
        (cantorCompletenessDecodeBHist (cantorCompletenessEventAtDefault 4 ef))
        (cantorCompletenessDecodeBHist (cantorCompletenessEventAtDefault 5 ef))
        (cantorCompletenessDecodeBHist (cantorCompletenessEventAtDefault 6 ef))
        (cantorCompletenessDecodeBHist (cantorCompletenessEventAtDefault 7 ef))
        (cantorCompletenessDecodeBHist (cantorCompletenessEventAtDefault 8 ef))
        (cantorCompletenessDecodeBHist (cantorCompletenessEventAtDefault 9 ef))
        (cantorCompletenessDecodeBHist (cantorCompletenessEventAtDefault 10 ef)))

private theorem cantorCompleteness_round_trip :
    ∀ x : CantorCompletenessUp,
      cantorCompletenessFromEventFlow (cantorCompletenessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk nestedIntervals locatedEndpoints diameterLedger dyadicTolerances streamWindows
      regularReadback realSeal transports replay provenance localNameCert =>
      change
        some
          (CantorCompletenessUp.mk
            (cantorCompletenessDecodeBHist
              (cantorCompletenessEncodeBHist nestedIntervals))
            (cantorCompletenessDecodeBHist
              (cantorCompletenessEncodeBHist locatedEndpoints))
            (cantorCompletenessDecodeBHist
              (cantorCompletenessEncodeBHist diameterLedger))
            (cantorCompletenessDecodeBHist
              (cantorCompletenessEncodeBHist dyadicTolerances))
            (cantorCompletenessDecodeBHist
              (cantorCompletenessEncodeBHist streamWindows))
            (cantorCompletenessDecodeBHist
              (cantorCompletenessEncodeBHist regularReadback))
            (cantorCompletenessDecodeBHist
              (cantorCompletenessEncodeBHist realSeal))
            (cantorCompletenessDecodeBHist
              (cantorCompletenessEncodeBHist transports))
            (cantorCompletenessDecodeBHist
              (cantorCompletenessEncodeBHist replay))
            (cantorCompletenessDecodeBHist
              (cantorCompletenessEncodeBHist provenance))
            (cantorCompletenessDecodeBHist
              (cantorCompletenessEncodeBHist localNameCert))) =
          some
            (CantorCompletenessUp.mk nestedIntervals locatedEndpoints diameterLedger
              dyadicTolerances streamWindows regularReadback realSeal transports replay provenance
              localNameCert)
      rw [cantorCompleteness_decode_encode_bhist nestedIntervals,
        cantorCompleteness_decode_encode_bhist locatedEndpoints,
        cantorCompleteness_decode_encode_bhist diameterLedger,
        cantorCompleteness_decode_encode_bhist dyadicTolerances,
        cantorCompleteness_decode_encode_bhist streamWindows,
        cantorCompleteness_decode_encode_bhist regularReadback,
        cantorCompleteness_decode_encode_bhist realSeal,
        cantorCompleteness_decode_encode_bhist transports,
        cantorCompleteness_decode_encode_bhist replay,
        cantorCompleteness_decode_encode_bhist provenance,
        cantorCompleteness_decode_encode_bhist localNameCert]

private theorem cantorCompletenessToEventFlow_injective {x y : CantorCompletenessUp} :
    cantorCompletenessToEventFlow x = cantorCompletenessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cantorCompletenessFromEventFlow (cantorCompletenessToEventFlow x) =
        cantorCompletenessFromEventFlow (cantorCompletenessToEventFlow y) :=
    congrArg cantorCompletenessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cantorCompleteness_round_trip x).symm
      (Eq.trans hread (cantorCompleteness_round_trip y)))

private theorem cantorCompleteness_field_faithful :
    ∀ x y : CantorCompletenessUp, cantorCompletenessFields x =
      cantorCompletenessFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk nestedIntervals₁ locatedEndpoints₁ diameterLedger₁ dyadicTolerances₁ streamWindows₁
      regularReadback₁ realSeal₁ transports₁ replay₁ provenance₁ localNameCert₁ =>
      cases y with
      | mk nestedIntervals₂ locatedEndpoints₂ diameterLedger₂ dyadicTolerances₂ streamWindows₂
          regularReadback₂ realSeal₂ transports₂ replay₂ provenance₂ localNameCert₂ =>
          cases hfields
          rfl

instance cantorCompletenessBHistCarrier : BHistCarrier CantorCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cantorCompletenessToEventFlow
  fromEventFlow := cantorCompletenessFromEventFlow

instance cantorCompletenessChapterTasteGate : ChapterTasteGate CantorCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cantorCompletenessFromEventFlow (cantorCompletenessToEventFlow x) = some x
    exact cantorCompleteness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cantorCompletenessToEventFlow_injective heq)

instance cantorCompletenessFieldFaithful : FieldFaithful CantorCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cantorCompletenessFields
  field_faithful := cantorCompleteness_field_faithful

instance cantorCompletenessNontrivial : Nontrivial CantorCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CantorCompletenessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CantorCompletenessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CantorCompletenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cantorCompletenessChapterTasteGate

theorem CantorCompletenessTasteGate_single_carrier_alignment :
    (∀ h : BHist, cantorCompletenessDecodeBHist (cantorCompletenessEncodeBHist h) = h) ∧
      (∀ x : CantorCompletenessUp,
        cantorCompletenessFromEventFlow (cantorCompletenessToEventFlow x) = some x) ∧
        (∀ x y : CantorCompletenessUp,
          cantorCompletenessToEventFlow x = cantorCompletenessToEventFlow y → x = y) ∧
          cantorCompletenessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨cantorCompleteness_decode_encode_bhist,
      cantorCompleteness_round_trip,
      (fun _ _ heq => cantorCompletenessToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CantorCompletenessUp
