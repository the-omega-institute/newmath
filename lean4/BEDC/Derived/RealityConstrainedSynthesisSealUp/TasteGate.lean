import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealityConstrainedSynthesisSealUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealityConstrainedSynthesisSealUp : Type where
  | mk :
      (audit openFit objectivity observation explanation tower ledger failure transport replay
        provenance nameRow : BHist) →
      RealityConstrainedSynthesisSealUp
  deriving DecidableEq

def realityConstrainedSynthesisSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realityConstrainedSynthesisSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realityConstrainedSynthesisSealEncodeBHist h

def realityConstrainedSynthesisSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realityConstrainedSynthesisSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realityConstrainedSynthesisSealDecodeBHist tail)

private theorem RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      realityConstrainedSynthesisSealDecodeBHist
        (realityConstrainedSynthesisSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realityConstrainedSynthesisSealFields :
    RealityConstrainedSynthesisSealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedSynthesisSealUp.mk audit openFit objectivity observation explanation
      tower ledger failure transport replay provenance nameRow =>
      [audit, openFit, objectivity, observation, explanation, tower, ledger, failure,
        transport, replay, provenance, nameRow]

def realityConstrainedSynthesisSealToEventFlow :
    RealityConstrainedSynthesisSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedSynthesisSealUp.mk audit openFit objectivity observation explanation
      tower ledger failure transport replay provenance nameRow =>
      [[BMark.b0],
        realityConstrainedSynthesisSealEncodeBHist audit,
        [BMark.b1, BMark.b0],
        realityConstrainedSynthesisSealEncodeBHist openFit,
        [BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedSynthesisSealEncodeBHist objectivity,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedSynthesisSealEncodeBHist observation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedSynthesisSealEncodeBHist explanation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedSynthesisSealEncodeBHist tower,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedSynthesisSealEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realityConstrainedSynthesisSealEncodeBHist failure,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realityConstrainedSynthesisSealEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedSynthesisSealEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedSynthesisSealEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedSynthesisSealEncodeBHist nameRow]

private def RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_eventAtDefault
        index rest

def realityConstrainedSynthesisSealFromEventFlow
    (ef : EventFlow) : Option RealityConstrainedSynthesisSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealityConstrainedSynthesisSealUp.mk
      (realityConstrainedSynthesisSealDecodeBHist
        (RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (realityConstrainedSynthesisSealDecodeBHist
        (RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (realityConstrainedSynthesisSealDecodeBHist
        (RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (realityConstrainedSynthesisSealDecodeBHist
        (RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (realityConstrainedSynthesisSealDecodeBHist
        (RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
      (realityConstrainedSynthesisSealDecodeBHist
        (RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_eventAtDefault 11 ef))
      (realityConstrainedSynthesisSealDecodeBHist
        (RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_eventAtDefault 13 ef))
      (realityConstrainedSynthesisSealDecodeBHist
        (RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_eventAtDefault 15 ef))
      (realityConstrainedSynthesisSealDecodeBHist
        (RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_eventAtDefault 17 ef))
      (realityConstrainedSynthesisSealDecodeBHist
        (RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_eventAtDefault 19 ef))
      (realityConstrainedSynthesisSealDecodeBHist
        (RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_eventAtDefault 21 ef))
      (realityConstrainedSynthesisSealDecodeBHist
        (RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_eventAtDefault 23 ef)))

private theorem RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealityConstrainedSynthesisSealUp,
      realityConstrainedSynthesisSealFromEventFlow
        (realityConstrainedSynthesisSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk audit openFit objectivity observation explanation tower ledger failure transport replay
      provenance nameRow =>
      change
        some
          (RealityConstrainedSynthesisSealUp.mk
            (realityConstrainedSynthesisSealDecodeBHist
              (realityConstrainedSynthesisSealEncodeBHist audit))
            (realityConstrainedSynthesisSealDecodeBHist
              (realityConstrainedSynthesisSealEncodeBHist openFit))
            (realityConstrainedSynthesisSealDecodeBHist
              (realityConstrainedSynthesisSealEncodeBHist objectivity))
            (realityConstrainedSynthesisSealDecodeBHist
              (realityConstrainedSynthesisSealEncodeBHist observation))
            (realityConstrainedSynthesisSealDecodeBHist
              (realityConstrainedSynthesisSealEncodeBHist explanation))
            (realityConstrainedSynthesisSealDecodeBHist
              (realityConstrainedSynthesisSealEncodeBHist tower))
            (realityConstrainedSynthesisSealDecodeBHist
              (realityConstrainedSynthesisSealEncodeBHist ledger))
            (realityConstrainedSynthesisSealDecodeBHist
              (realityConstrainedSynthesisSealEncodeBHist failure))
            (realityConstrainedSynthesisSealDecodeBHist
              (realityConstrainedSynthesisSealEncodeBHist transport))
            (realityConstrainedSynthesisSealDecodeBHist
              (realityConstrainedSynthesisSealEncodeBHist replay))
            (realityConstrainedSynthesisSealDecodeBHist
              (realityConstrainedSynthesisSealEncodeBHist provenance))
            (realityConstrainedSynthesisSealDecodeBHist
              (realityConstrainedSynthesisSealEncodeBHist nameRow))) =
          some
            (RealityConstrainedSynthesisSealUp.mk audit openFit objectivity observation
              explanation tower ledger failure transport replay provenance nameRow)
      rw [RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_decode audit,
        RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_decode openFit,
        RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_decode objectivity,
        RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_decode observation,
        RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_decode explanation,
        RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_decode tower,
        RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_decode ledger,
        RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_decode failure,
        RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_decode transport,
        RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_decode replay,
        RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_decode provenance,
        RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_decode nameRow]

private theorem RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_injective
    {x y : RealityConstrainedSynthesisSealUp} :
    realityConstrainedSynthesisSealToEventFlow x =
      realityConstrainedSynthesisSealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realityConstrainedSynthesisSealFromEventFlow
          (realityConstrainedSynthesisSealToEventFlow x) =
        realityConstrainedSynthesisSealFromEventFlow
          (realityConstrainedSynthesisSealToEventFlow y) :=
    congrArg realityConstrainedSynthesisSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_fields :
    ∀ x y : RealityConstrainedSynthesisSealUp,
      realityConstrainedSynthesisSealFields x = realityConstrainedSynthesisSealFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk audit₁ openFit₁ objectivity₁ observation₁ explanation₁ tower₁ ledger₁ failure₁
      transport₁ replay₁ provenance₁ nameRow₁ =>
      cases y with
      | mk audit₂ openFit₂ objectivity₂ observation₂ explanation₂ tower₂ ledger₂ failure₂
          transport₂ replay₂ provenance₂ nameRow₂ =>
          cases hfields
          rfl

instance realityConstrainedSynthesisSealBHistCarrier :
    BHistCarrier RealityConstrainedSynthesisSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realityConstrainedSynthesisSealToEventFlow
  fromEventFlow := realityConstrainedSynthesisSealFromEventFlow

instance realityConstrainedSynthesisSealChapterTasteGate :
    ChapterTasteGate RealityConstrainedSynthesisSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realityConstrainedSynthesisSealFromEventFlow
        (realityConstrainedSynthesisSealToEventFlow x) = some x
    exact RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_injective heq)

instance realityConstrainedSynthesisSealFieldFaithful :
    FieldFaithful RealityConstrainedSynthesisSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realityConstrainedSynthesisSealFields
  field_faithful :=
    RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_fields

instance realityConstrainedSynthesisSealNontrivial :
    Nontrivial RealityConstrainedSynthesisSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealityConstrainedSynthesisSealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      RealityConstrainedSynthesisSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealityConstrainedSynthesisSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realityConstrainedSynthesisSealChapterTasteGate

theorem RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realityConstrainedSynthesisSealDecodeBHist
        (realityConstrainedSynthesisSealEncodeBHist h) = h) ∧
      (∀ x : RealityConstrainedSynthesisSealUp,
        realityConstrainedSynthesisSealFromEventFlow
          (realityConstrainedSynthesisSealToEventFlow x) = some x) ∧
        (∀ x y : RealityConstrainedSynthesisSealUp,
          realityConstrainedSynthesisSealToEventFlow x =
            realityConstrainedSynthesisSealToEventFlow y → x = y) ∧
          realityConstrainedSynthesisSealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_decode
  · constructor
    · exact RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.RealityConstrainedSynthesisSealUp.TasteGate
