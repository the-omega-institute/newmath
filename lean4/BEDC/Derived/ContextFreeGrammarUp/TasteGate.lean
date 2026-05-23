import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContextFreeGrammarUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContextFreeGrammarUp : Type where
  | mk
      (terminal nonterminal start production yield derivation readback transport route provenance
        name : BHist) : ContextFreeGrammarUp
  deriving DecidableEq

def contextFreeGrammarEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: contextFreeGrammarEncodeBHist h
  | BHist.e1 h => BMark.b1 :: contextFreeGrammarEncodeBHist h

def contextFreeGrammarDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (contextFreeGrammarDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (contextFreeGrammarDecodeBHist tail)

private theorem ContextFreeGrammarTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, contextFreeGrammarDecodeBHist (contextFreeGrammarEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def contextFreeGrammarFields : ContextFreeGrammarUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ContextFreeGrammarUp.mk terminal nonterminal start production yield derivation readback
      transport route provenance name =>
      [terminal, nonterminal, start, production, yield, derivation, readback, transport, route,
        provenance, name]

def contextFreeGrammarToEventFlow : ContextFreeGrammarUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => [BMark.b1, BMark.b0, BMark.b0, BMark.b1] ::
      (contextFreeGrammarFields x).map contextFreeGrammarEncodeBHist

private def contextFreeGrammarEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => contextFreeGrammarEventAtDefault index rest

def contextFreeGrammarFromEventFlow (ef : EventFlow) : Option ContextFreeGrammarUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ContextFreeGrammarUp.mk
      (contextFreeGrammarDecodeBHist (contextFreeGrammarEventAtDefault 1 ef))
      (contextFreeGrammarDecodeBHist (contextFreeGrammarEventAtDefault 2 ef))
      (contextFreeGrammarDecodeBHist (contextFreeGrammarEventAtDefault 3 ef))
      (contextFreeGrammarDecodeBHist (contextFreeGrammarEventAtDefault 4 ef))
      (contextFreeGrammarDecodeBHist (contextFreeGrammarEventAtDefault 5 ef))
      (contextFreeGrammarDecodeBHist (contextFreeGrammarEventAtDefault 6 ef))
      (contextFreeGrammarDecodeBHist (contextFreeGrammarEventAtDefault 7 ef))
      (contextFreeGrammarDecodeBHist (contextFreeGrammarEventAtDefault 8 ef))
      (contextFreeGrammarDecodeBHist (contextFreeGrammarEventAtDefault 9 ef))
      (contextFreeGrammarDecodeBHist (contextFreeGrammarEventAtDefault 10 ef))
      (contextFreeGrammarDecodeBHist (contextFreeGrammarEventAtDefault 11 ef)))

private theorem ContextFreeGrammarTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ContextFreeGrammarUp,
      contextFreeGrammarFromEventFlow (contextFreeGrammarToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk terminal nonterminal start production yield derivation readback transport route provenance
      name =>
      change
        some
          (ContextFreeGrammarUp.mk
            (contextFreeGrammarDecodeBHist (contextFreeGrammarEncodeBHist terminal))
            (contextFreeGrammarDecodeBHist (contextFreeGrammarEncodeBHist nonterminal))
            (contextFreeGrammarDecodeBHist (contextFreeGrammarEncodeBHist start))
            (contextFreeGrammarDecodeBHist (contextFreeGrammarEncodeBHist production))
            (contextFreeGrammarDecodeBHist (contextFreeGrammarEncodeBHist yield))
            (contextFreeGrammarDecodeBHist (contextFreeGrammarEncodeBHist derivation))
            (contextFreeGrammarDecodeBHist (contextFreeGrammarEncodeBHist readback))
            (contextFreeGrammarDecodeBHist (contextFreeGrammarEncodeBHist transport))
            (contextFreeGrammarDecodeBHist (contextFreeGrammarEncodeBHist route))
            (contextFreeGrammarDecodeBHist (contextFreeGrammarEncodeBHist provenance))
            (contextFreeGrammarDecodeBHist (contextFreeGrammarEncodeBHist name))) =
          some
            (ContextFreeGrammarUp.mk terminal nonterminal start production yield derivation
              readback transport route provenance name)
      rw [ContextFreeGrammarTasteGate_single_carrier_alignment_decode terminal,
        ContextFreeGrammarTasteGate_single_carrier_alignment_decode nonterminal,
        ContextFreeGrammarTasteGate_single_carrier_alignment_decode start,
        ContextFreeGrammarTasteGate_single_carrier_alignment_decode production,
        ContextFreeGrammarTasteGate_single_carrier_alignment_decode yield,
        ContextFreeGrammarTasteGate_single_carrier_alignment_decode derivation,
        ContextFreeGrammarTasteGate_single_carrier_alignment_decode readback,
        ContextFreeGrammarTasteGate_single_carrier_alignment_decode transport,
        ContextFreeGrammarTasteGate_single_carrier_alignment_decode route,
        ContextFreeGrammarTasteGate_single_carrier_alignment_decode provenance,
        ContextFreeGrammarTasteGate_single_carrier_alignment_decode name]

private theorem ContextFreeGrammarTasteGate_single_carrier_alignment_injective
    {x y : ContextFreeGrammarUp} :
    contextFreeGrammarToEventFlow x = contextFreeGrammarToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      contextFreeGrammarFromEventFlow (contextFreeGrammarToEventFlow x) =
        contextFreeGrammarFromEventFlow (contextFreeGrammarToEventFlow y) :=
    congrArg contextFreeGrammarFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ContextFreeGrammarTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ContextFreeGrammarTasteGate_single_carrier_alignment_round_trip y)))

private theorem ContextFreeGrammarTasteGate_single_carrier_alignment_fields :
    ∀ x y : ContextFreeGrammarUp,
      contextFreeGrammarFields x = contextFreeGrammarFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk terminal1 nonterminal1 start1 production1 yield1 derivation1 readback1 transport1
      route1 provenance1 name1 =>
      cases y with
      | mk terminal2 nonterminal2 start2 production2 yield2 derivation2 readback2 transport2
          route2 provenance2 name2 =>
          cases hfields
          rfl

instance contextFreeGrammarBHistCarrier : BHistCarrier ContextFreeGrammarUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := contextFreeGrammarToEventFlow
  fromEventFlow := contextFreeGrammarFromEventFlow

instance contextFreeGrammarChapterTasteGate : ChapterTasteGate ContextFreeGrammarUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change contextFreeGrammarFromEventFlow (contextFreeGrammarToEventFlow x) = some x
    exact ContextFreeGrammarTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ContextFreeGrammarTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate ContextFreeGrammarUp :=
  -- BEDC touchpoint anchor: BHist BMark
  contextFreeGrammarChapterTasteGate

instance contextFreeGrammarFieldFaithful : FieldFaithful ContextFreeGrammarUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := contextFreeGrammarFields
  field_faithful := ContextFreeGrammarTasteGate_single_carrier_alignment_fields

instance contextFreeGrammarNontrivial : Nontrivial ContextFreeGrammarUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ContextFreeGrammarUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ContextFreeGrammarUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem ContextFreeGrammarTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ContextFreeGrammarUp) ∧
      (∀ x : ContextFreeGrammarUp,
        BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
        (BHistCarrier.toEventFlow
            (ContextFreeGrammarUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty) =
          [[BMark.b1, BMark.b0, BMark.b0, BMark.b1], [], [], [], [], [], [], [], [], [], [],
            []]) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact ⟨contextFreeGrammarChapterTasteGate⟩
  · constructor
    · intro x
      change contextFreeGrammarFromEventFlow (contextFreeGrammarToEventFlow x) = some x
      exact ContextFreeGrammarTasteGate_single_carrier_alignment_round_trip x
    · rfl

end BEDC.Derived.ContextFreeGrammarUp
