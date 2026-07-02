import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCompletionWitnessLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealCompletionWitnessLedgerUp : Type where
  | mk (stream regseq dyadic handoff sealRow transportRow replay audit provenance localName :
      BHist) :
      RealCompletionWitnessLedgerUp
  deriving DecidableEq

def realCompletionWitnessLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCompletionWitnessLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCompletionWitnessLedgerEncodeBHist h

def realCompletionWitnessLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCompletionWitnessLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCompletionWitnessLedgerDecodeBHist tail)

private theorem realCompletionWitnessLedgerDecodeEncodeBHist :
    ∀ h : BHist,
      realCompletionWitnessLedgerDecodeBHist
          (realCompletionWitnessLedgerEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realCompletionWitnessLedgerFields :
    RealCompletionWitnessLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealCompletionWitnessLedgerUp.mk stream regseq dyadic handoff sealRow transportRow replay audit
      provenance localName =>
      [stream, regseq, dyadic, handoff, sealRow, transportRow, replay, audit, provenance,
        localName]

def realCompletionWitnessLedgerToEventFlow :
    RealCompletionWitnessLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realCompletionWitnessLedgerFields x).map realCompletionWitnessLedgerEncodeBHist

private def realCompletionWitnessLedgerEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realCompletionWitnessLedgerEventAtDefault index rest

def realCompletionWitnessLedgerFromEventFlow :
    EventFlow → Option RealCompletionWitnessLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | eventFlow =>
      some
        (RealCompletionWitnessLedgerUp.mk
          (realCompletionWitnessLedgerDecodeBHist
            (realCompletionWitnessLedgerEventAtDefault 0 eventFlow))
          (realCompletionWitnessLedgerDecodeBHist
            (realCompletionWitnessLedgerEventAtDefault 1 eventFlow))
          (realCompletionWitnessLedgerDecodeBHist
            (realCompletionWitnessLedgerEventAtDefault 2 eventFlow))
          (realCompletionWitnessLedgerDecodeBHist
            (realCompletionWitnessLedgerEventAtDefault 3 eventFlow))
          (realCompletionWitnessLedgerDecodeBHist
            (realCompletionWitnessLedgerEventAtDefault 4 eventFlow))
          (realCompletionWitnessLedgerDecodeBHist
            (realCompletionWitnessLedgerEventAtDefault 5 eventFlow))
          (realCompletionWitnessLedgerDecodeBHist
            (realCompletionWitnessLedgerEventAtDefault 6 eventFlow))
          (realCompletionWitnessLedgerDecodeBHist
            (realCompletionWitnessLedgerEventAtDefault 7 eventFlow))
          (realCompletionWitnessLedgerDecodeBHist
            (realCompletionWitnessLedgerEventAtDefault 8 eventFlow))
          (realCompletionWitnessLedgerDecodeBHist
            (realCompletionWitnessLedgerEventAtDefault 9 eventFlow)))

private theorem realCompletionWitnessLedger_round_trip :
    ∀ x : RealCompletionWitnessLedgerUp,
      realCompletionWitnessLedgerFromEventFlow
          (realCompletionWitnessLedgerToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk stream regseq dyadic handoff sealRow transportRow replay audit provenance localName =>
      change
        some
            (RealCompletionWitnessLedgerUp.mk
              (realCompletionWitnessLedgerDecodeBHist
                (realCompletionWitnessLedgerEncodeBHist stream))
              (realCompletionWitnessLedgerDecodeBHist
                (realCompletionWitnessLedgerEncodeBHist regseq))
              (realCompletionWitnessLedgerDecodeBHist
                (realCompletionWitnessLedgerEncodeBHist dyadic))
              (realCompletionWitnessLedgerDecodeBHist
                (realCompletionWitnessLedgerEncodeBHist handoff))
              (realCompletionWitnessLedgerDecodeBHist
                (realCompletionWitnessLedgerEncodeBHist sealRow))
              (realCompletionWitnessLedgerDecodeBHist
                (realCompletionWitnessLedgerEncodeBHist transportRow))
              (realCompletionWitnessLedgerDecodeBHist
                (realCompletionWitnessLedgerEncodeBHist replay))
              (realCompletionWitnessLedgerDecodeBHist
                (realCompletionWitnessLedgerEncodeBHist audit))
              (realCompletionWitnessLedgerDecodeBHist
                (realCompletionWitnessLedgerEncodeBHist provenance))
              (realCompletionWitnessLedgerDecodeBHist
                (realCompletionWitnessLedgerEncodeBHist localName))) =
          some
            (RealCompletionWitnessLedgerUp.mk stream regseq dyadic handoff sealRow transportRow
              replay audit provenance localName)
      rw [realCompletionWitnessLedgerDecodeEncodeBHist stream]
      rw [realCompletionWitnessLedgerDecodeEncodeBHist regseq]
      rw [realCompletionWitnessLedgerDecodeEncodeBHist dyadic]
      rw [realCompletionWitnessLedgerDecodeEncodeBHist handoff]
      rw [realCompletionWitnessLedgerDecodeEncodeBHist sealRow]
      rw [realCompletionWitnessLedgerDecodeEncodeBHist transportRow]
      rw [realCompletionWitnessLedgerDecodeEncodeBHist replay]
      rw [realCompletionWitnessLedgerDecodeEncodeBHist audit]
      rw [realCompletionWitnessLedgerDecodeEncodeBHist provenance]
      rw [realCompletionWitnessLedgerDecodeEncodeBHist localName]

private theorem realCompletionWitnessLedgerToEventFlow_injective
    {x y : RealCompletionWitnessLedgerUp} :
    realCompletionWitnessLedgerToEventFlow x =
        realCompletionWitnessLedgerToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCompletionWitnessLedgerFromEventFlow
          (realCompletionWitnessLedgerToEventFlow x) =
        realCompletionWitnessLedgerFromEventFlow
          (realCompletionWitnessLedgerToEventFlow y) :=
    congrArg realCompletionWitnessLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realCompletionWitnessLedger_round_trip x).symm
      (Eq.trans hread (realCompletionWitnessLedger_round_trip y)))

private theorem realCompletionWitnessLedger_fields_faithful :
    ∀ x y : RealCompletionWitnessLedgerUp,
      realCompletionWitnessLedgerFields x = realCompletionWitnessLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk stream₁ regseq₁ dyadic₁ handoff₁ sealRow₁ transportRow₁ replay₁ audit₁ provenance₁
      localName₁ =>
      cases y with
      | mk stream₂ regseq₂ dyadic₂ handoff₂ sealRow₂ transportRow₂ replay₂ audit₂ provenance₂
          localName₂ =>
          injection hfields with hstream tail0
          injection tail0 with hregseq tail1
          injection tail1 with hdyadic tail2
          injection tail2 with hhandoff tail3
          injection tail3 with hseal tail4
          injection tail4 with htransport tail5
          injection tail5 with hreplay tail6
          injection tail6 with haudit tail7
          injection tail7 with hprovenance tail8
          injection tail8 with hlocalName _
          subst hstream
          subst hregseq
          subst hdyadic
          subst hhandoff
          subst hseal
          subst htransport
          subst hreplay
          subst haudit
          subst hprovenance
          subst hlocalName
          rfl

instance realCompletionWitnessLedgerBHistCarrier :
    BHistCarrier RealCompletionWitnessLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realCompletionWitnessLedgerToEventFlow
  fromEventFlow := realCompletionWitnessLedgerFromEventFlow

instance realCompletionWitnessLedgerChapterTasteGate :
    ChapterTasteGate RealCompletionWitnessLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realCompletionWitnessLedgerFromEventFlow
          (realCompletionWitnessLedgerToEventFlow x) =
        some x
    exact realCompletionWitnessLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realCompletionWitnessLedgerToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealCompletionWitnessLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realCompletionWitnessLedgerFromEventFlow
          (realCompletionWitnessLedgerToEventFlow x) =
        some x
    exact realCompletionWitnessLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realCompletionWitnessLedgerToEventFlow_injective heq)

instance realCompletionWitnessLedgerFieldFaithful :
    FieldFaithful RealCompletionWitnessLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realCompletionWitnessLedgerFields
  field_faithful := realCompletionWitnessLedger_fields_faithful

instance realCompletionWitnessLedgerNontrivial :
    Nontrivial RealCompletionWitnessLedgerUp where
  witness_pair :=
    ⟨RealCompletionWitnessLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealCompletionWitnessLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

theorem RealCompletionWitnessLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realCompletionWitnessLedgerDecodeBHist
          (realCompletionWitnessLedgerEncodeBHist h) =
        h) ∧
      (∀ x : RealCompletionWitnessLedgerUp,
        realCompletionWitnessLedgerFromEventFlow
            (realCompletionWitnessLedgerToEventFlow x) =
          some x) ∧
        (∀ x y : RealCompletionWitnessLedgerUp,
          realCompletionWitnessLedgerToEventFlow x =
              realCompletionWitnessLedgerToEventFlow y →
            x = y) ∧
          Nonempty (BHistCarrier RealCompletionWitnessLedgerUp) ∧
            Nonempty (ChapterTasteGate RealCompletionWitnessLedgerUp) ∧
              Nonempty (FieldFaithful RealCompletionWitnessLedgerUp) ∧
                realCompletionWitnessLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨realCompletionWitnessLedgerDecodeEncodeBHist,
      ⟨realCompletionWitnessLedger_round_trip,
        ⟨fun _x _y heq => realCompletionWitnessLedgerToEventFlow_injective heq,
          ⟨⟨realCompletionWitnessLedgerBHistCarrier⟩,
            ⟨realCompletionWitnessLedgerChapterTasteGate⟩,
            ⟨realCompletionWitnessLedgerFieldFaithful⟩,
            rfl⟩⟩⟩⟩

end BEDC.Derived.RealCompletionWitnessLedgerUp
