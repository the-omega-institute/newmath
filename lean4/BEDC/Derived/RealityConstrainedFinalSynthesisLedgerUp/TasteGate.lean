import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealityConstrainedFinalSynthesisLedgerUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealityConstrainedFinalSynthesisLedgerUp : Type where
  | mk :
      (truth truthCert methodology failure boundary observer synthesis transport replay provenance
        name : BHist) →
        RealityConstrainedFinalSynthesisLedgerUp
  deriving DecidableEq

def realityConstrainedFinalSynthesisLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realityConstrainedFinalSynthesisLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realityConstrainedFinalSynthesisLedgerEncodeBHist h

def realityConstrainedFinalSynthesisLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realityConstrainedFinalSynthesisLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realityConstrainedFinalSynthesisLedgerDecodeBHist tail)

private theorem realityConstrainedFinalSynthesisLedger_decode_encode_bhist :
    ∀ h : BHist,
      realityConstrainedFinalSynthesisLedgerDecodeBHist
        (realityConstrainedFinalSynthesisLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realityConstrainedFinalSynthesisLedgerFields :
    RealityConstrainedFinalSynthesisLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedFinalSynthesisLedgerUp.mk truth truthCert methodology failure boundary
      observer synthesis transport replay provenance name =>
      [truth, truthCert, methodology, failure, boundary, observer, synthesis, transport, replay,
        provenance, name]

def realityConstrainedFinalSynthesisLedgerToEventFlow :
    RealityConstrainedFinalSynthesisLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedFinalSynthesisLedgerUp.mk truth truthCert methodology failure boundary
      observer synthesis transport replay provenance name =>
      [[BMark.b0],
        realityConstrainedFinalSynthesisLedgerEncodeBHist truth,
        [BMark.b1, BMark.b0],
        realityConstrainedFinalSynthesisLedgerEncodeBHist truthCert,
        [BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedFinalSynthesisLedgerEncodeBHist methodology,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedFinalSynthesisLedgerEncodeBHist failure,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedFinalSynthesisLedgerEncodeBHist boundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedFinalSynthesisLedgerEncodeBHist observer,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedFinalSynthesisLedgerEncodeBHist synthesis,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realityConstrainedFinalSynthesisLedgerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realityConstrainedFinalSynthesisLedgerEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedFinalSynthesisLedgerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedFinalSynthesisLedgerEncodeBHist name]

private def realityConstrainedFinalSynthesisLedgerEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      realityConstrainedFinalSynthesisLedgerEventAtDefault index rest

def realityConstrainedFinalSynthesisLedgerFromEventFlow
    (ef : EventFlow) : Option RealityConstrainedFinalSynthesisLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealityConstrainedFinalSynthesisLedgerUp.mk
      (realityConstrainedFinalSynthesisLedgerDecodeBHist
        (realityConstrainedFinalSynthesisLedgerEventAtDefault 1 ef))
      (realityConstrainedFinalSynthesisLedgerDecodeBHist
        (realityConstrainedFinalSynthesisLedgerEventAtDefault 3 ef))
      (realityConstrainedFinalSynthesisLedgerDecodeBHist
        (realityConstrainedFinalSynthesisLedgerEventAtDefault 5 ef))
      (realityConstrainedFinalSynthesisLedgerDecodeBHist
        (realityConstrainedFinalSynthesisLedgerEventAtDefault 7 ef))
      (realityConstrainedFinalSynthesisLedgerDecodeBHist
        (realityConstrainedFinalSynthesisLedgerEventAtDefault 9 ef))
      (realityConstrainedFinalSynthesisLedgerDecodeBHist
        (realityConstrainedFinalSynthesisLedgerEventAtDefault 11 ef))
      (realityConstrainedFinalSynthesisLedgerDecodeBHist
        (realityConstrainedFinalSynthesisLedgerEventAtDefault 13 ef))
      (realityConstrainedFinalSynthesisLedgerDecodeBHist
        (realityConstrainedFinalSynthesisLedgerEventAtDefault 15 ef))
      (realityConstrainedFinalSynthesisLedgerDecodeBHist
        (realityConstrainedFinalSynthesisLedgerEventAtDefault 17 ef))
      (realityConstrainedFinalSynthesisLedgerDecodeBHist
        (realityConstrainedFinalSynthesisLedgerEventAtDefault 19 ef))
      (realityConstrainedFinalSynthesisLedgerDecodeBHist
        (realityConstrainedFinalSynthesisLedgerEventAtDefault 21 ef)))

private theorem realityConstrainedFinalSynthesisLedger_round_trip :
    ∀ x : RealityConstrainedFinalSynthesisLedgerUp,
      realityConstrainedFinalSynthesisLedgerFromEventFlow
        (realityConstrainedFinalSynthesisLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk truth truthCert methodology failure boundary observer synthesis transport replay provenance
      name =>
      change
        some
          (RealityConstrainedFinalSynthesisLedgerUp.mk
            (realityConstrainedFinalSynthesisLedgerDecodeBHist
              (realityConstrainedFinalSynthesisLedgerEncodeBHist truth))
            (realityConstrainedFinalSynthesisLedgerDecodeBHist
              (realityConstrainedFinalSynthesisLedgerEncodeBHist truthCert))
            (realityConstrainedFinalSynthesisLedgerDecodeBHist
              (realityConstrainedFinalSynthesisLedgerEncodeBHist methodology))
            (realityConstrainedFinalSynthesisLedgerDecodeBHist
              (realityConstrainedFinalSynthesisLedgerEncodeBHist failure))
            (realityConstrainedFinalSynthesisLedgerDecodeBHist
              (realityConstrainedFinalSynthesisLedgerEncodeBHist boundary))
            (realityConstrainedFinalSynthesisLedgerDecodeBHist
              (realityConstrainedFinalSynthesisLedgerEncodeBHist observer))
            (realityConstrainedFinalSynthesisLedgerDecodeBHist
              (realityConstrainedFinalSynthesisLedgerEncodeBHist synthesis))
            (realityConstrainedFinalSynthesisLedgerDecodeBHist
              (realityConstrainedFinalSynthesisLedgerEncodeBHist transport))
            (realityConstrainedFinalSynthesisLedgerDecodeBHist
              (realityConstrainedFinalSynthesisLedgerEncodeBHist replay))
            (realityConstrainedFinalSynthesisLedgerDecodeBHist
              (realityConstrainedFinalSynthesisLedgerEncodeBHist provenance))
            (realityConstrainedFinalSynthesisLedgerDecodeBHist
              (realityConstrainedFinalSynthesisLedgerEncodeBHist name))) =
          some
            (RealityConstrainedFinalSynthesisLedgerUp.mk truth truthCert methodology failure
              boundary observer synthesis transport replay provenance name)
      rw [realityConstrainedFinalSynthesisLedger_decode_encode_bhist truth,
        realityConstrainedFinalSynthesisLedger_decode_encode_bhist truthCert,
        realityConstrainedFinalSynthesisLedger_decode_encode_bhist methodology,
        realityConstrainedFinalSynthesisLedger_decode_encode_bhist failure,
        realityConstrainedFinalSynthesisLedger_decode_encode_bhist boundary,
        realityConstrainedFinalSynthesisLedger_decode_encode_bhist observer,
        realityConstrainedFinalSynthesisLedger_decode_encode_bhist synthesis,
        realityConstrainedFinalSynthesisLedger_decode_encode_bhist transport,
        realityConstrainedFinalSynthesisLedger_decode_encode_bhist replay,
        realityConstrainedFinalSynthesisLedger_decode_encode_bhist provenance,
        realityConstrainedFinalSynthesisLedger_decode_encode_bhist name]

private theorem realityConstrainedFinalSynthesisLedgerToEventFlow_injective
    {x y : RealityConstrainedFinalSynthesisLedgerUp} :
    realityConstrainedFinalSynthesisLedgerToEventFlow x =
      realityConstrainedFinalSynthesisLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realityConstrainedFinalSynthesisLedgerFromEventFlow
          (realityConstrainedFinalSynthesisLedgerToEventFlow x) =
        realityConstrainedFinalSynthesisLedgerFromEventFlow
          (realityConstrainedFinalSynthesisLedgerToEventFlow y) :=
    congrArg realityConstrainedFinalSynthesisLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realityConstrainedFinalSynthesisLedger_round_trip x).symm
      (Eq.trans hread (realityConstrainedFinalSynthesisLedger_round_trip y)))

private theorem realityConstrainedFinalSynthesisLedger_field_faithful :
    ∀ x y : RealityConstrainedFinalSynthesisLedgerUp,
      realityConstrainedFinalSynthesisLedgerFields x =
        realityConstrainedFinalSynthesisLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk truth truthCert methodology failure boundary observer synthesis transport replay provenance
      name =>
      cases y with
      | mk truth' truthCert' methodology' failure' boundary' observer' synthesis' transport'
          replay' provenance' name' =>
          cases hfields
          rfl

instance realityConstrainedFinalSynthesisLedgerBHistCarrier :
    BHistCarrier RealityConstrainedFinalSynthesisLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realityConstrainedFinalSynthesisLedgerToEventFlow
  fromEventFlow := realityConstrainedFinalSynthesisLedgerFromEventFlow

instance realityConstrainedFinalSynthesisLedgerChapterTasteGate :
    ChapterTasteGate RealityConstrainedFinalSynthesisLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realityConstrainedFinalSynthesisLedgerFromEventFlow
        (realityConstrainedFinalSynthesisLedgerToEventFlow x) = some x
    exact realityConstrainedFinalSynthesisLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realityConstrainedFinalSynthesisLedgerToEventFlow_injective heq)

instance realityConstrainedFinalSynthesisLedgerFieldFaithful :
    FieldFaithful RealityConstrainedFinalSynthesisLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realityConstrainedFinalSynthesisLedgerFields
  field_faithful := realityConstrainedFinalSynthesisLedger_field_faithful

instance realityConstrainedFinalSynthesisLedgerNontrivial :
    Nontrivial RealityConstrainedFinalSynthesisLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealityConstrainedFinalSynthesisLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      RealityConstrainedFinalSynthesisLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealityConstrainedFinalSynthesisLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realityConstrainedFinalSynthesisLedgerChapterTasteGate

theorem RealityConstrainedFinalSynthesisLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realityConstrainedFinalSynthesisLedgerDecodeBHist
        (realityConstrainedFinalSynthesisLedgerEncodeBHist h) = h) ∧
      Nonempty (Nontrivial RealityConstrainedFinalSynthesisLedgerUp) ∧
        Nonempty (ChapterTasteGate RealityConstrainedFinalSynthesisLedgerUp) ∧
          Nonempty (FieldFaithful RealityConstrainedFinalSynthesisLedgerUp) ∧
            realityConstrainedFinalSynthesisLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact realityConstrainedFinalSynthesisLedger_decode_encode_bhist
  · constructor
    · exact ⟨realityConstrainedFinalSynthesisLedgerNontrivial⟩
    · constructor
      · exact ⟨realityConstrainedFinalSynthesisLedgerChapterTasteGate⟩
      · constructor
        · exact ⟨realityConstrainedFinalSynthesisLedgerFieldFaithful⟩
        · rfl

end BEDC.Derived.RealityConstrainedFinalSynthesisLedgerUp.TasteGate
