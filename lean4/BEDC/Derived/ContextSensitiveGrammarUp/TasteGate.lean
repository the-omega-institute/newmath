import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContextSensitiveGrammarUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContextSensitiveGrammarUp : Type where
  | mk (A R W D L Q M H C P N : BHist) : ContextSensitiveGrammarUp
  deriving DecidableEq

def contextSensitiveGrammarEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: contextSensitiveGrammarEncodeBHist h
  | BHist.e1 h => BMark.b1 :: contextSensitiveGrammarEncodeBHist h

def contextSensitiveGrammarDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (contextSensitiveGrammarDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (contextSensitiveGrammarDecodeBHist tail)

private theorem ContextSensitiveGrammarTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      contextSensitiveGrammarDecodeBHist (contextSensitiveGrammarEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def contextSensitiveGrammarFields : ContextSensitiveGrammarUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ContextSensitiveGrammarUp.mk A R W D L Q M H C P N => [A, R, W, D, L, Q, M, H, C, P, N]

def contextSensitiveGrammarToEventFlow : ContextSensitiveGrammarUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (contextSensitiveGrammarFields x).map contextSensitiveGrammarEncodeBHist

private def contextSensitiveGrammarEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => contextSensitiveGrammarEventAtDefault index rest

def contextSensitiveGrammarFromEventFlow (ef : EventFlow) : Option ContextSensitiveGrammarUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ContextSensitiveGrammarUp.mk
      (contextSensitiveGrammarDecodeBHist (contextSensitiveGrammarEventAtDefault 0 ef))
      (contextSensitiveGrammarDecodeBHist (contextSensitiveGrammarEventAtDefault 1 ef))
      (contextSensitiveGrammarDecodeBHist (contextSensitiveGrammarEventAtDefault 2 ef))
      (contextSensitiveGrammarDecodeBHist (contextSensitiveGrammarEventAtDefault 3 ef))
      (contextSensitiveGrammarDecodeBHist (contextSensitiveGrammarEventAtDefault 4 ef))
      (contextSensitiveGrammarDecodeBHist (contextSensitiveGrammarEventAtDefault 5 ef))
      (contextSensitiveGrammarDecodeBHist (contextSensitiveGrammarEventAtDefault 6 ef))
      (contextSensitiveGrammarDecodeBHist (contextSensitiveGrammarEventAtDefault 7 ef))
      (contextSensitiveGrammarDecodeBHist (contextSensitiveGrammarEventAtDefault 8 ef))
      (contextSensitiveGrammarDecodeBHist (contextSensitiveGrammarEventAtDefault 9 ef))
      (contextSensitiveGrammarDecodeBHist (contextSensitiveGrammarEventAtDefault 10 ef)))

private theorem ContextSensitiveGrammarTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ContextSensitiveGrammarUp,
      contextSensitiveGrammarFromEventFlow (contextSensitiveGrammarToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A R W D L Q M H C P N =>
      change
        some
          (ContextSensitiveGrammarUp.mk
            (contextSensitiveGrammarDecodeBHist (contextSensitiveGrammarEncodeBHist A))
            (contextSensitiveGrammarDecodeBHist (contextSensitiveGrammarEncodeBHist R))
            (contextSensitiveGrammarDecodeBHist (contextSensitiveGrammarEncodeBHist W))
            (contextSensitiveGrammarDecodeBHist (contextSensitiveGrammarEncodeBHist D))
            (contextSensitiveGrammarDecodeBHist (contextSensitiveGrammarEncodeBHist L))
            (contextSensitiveGrammarDecodeBHist (contextSensitiveGrammarEncodeBHist Q))
            (contextSensitiveGrammarDecodeBHist (contextSensitiveGrammarEncodeBHist M))
            (contextSensitiveGrammarDecodeBHist (contextSensitiveGrammarEncodeBHist H))
            (contextSensitiveGrammarDecodeBHist (contextSensitiveGrammarEncodeBHist C))
            (contextSensitiveGrammarDecodeBHist (contextSensitiveGrammarEncodeBHist P))
            (contextSensitiveGrammarDecodeBHist (contextSensitiveGrammarEncodeBHist N))) =
          some (ContextSensitiveGrammarUp.mk A R W D L Q M H C P N)
      rw [ContextSensitiveGrammarTasteGate_single_carrier_alignment_decode A,
        ContextSensitiveGrammarTasteGate_single_carrier_alignment_decode R,
        ContextSensitiveGrammarTasteGate_single_carrier_alignment_decode W,
        ContextSensitiveGrammarTasteGate_single_carrier_alignment_decode D,
        ContextSensitiveGrammarTasteGate_single_carrier_alignment_decode L,
        ContextSensitiveGrammarTasteGate_single_carrier_alignment_decode Q,
        ContextSensitiveGrammarTasteGate_single_carrier_alignment_decode M,
        ContextSensitiveGrammarTasteGate_single_carrier_alignment_decode H,
        ContextSensitiveGrammarTasteGate_single_carrier_alignment_decode C,
        ContextSensitiveGrammarTasteGate_single_carrier_alignment_decode P,
        ContextSensitiveGrammarTasteGate_single_carrier_alignment_decode N]

private theorem ContextSensitiveGrammarToEventFlow_injective {x y : ContextSensitiveGrammarUp} :
    contextSensitiveGrammarToEventFlow x = contextSensitiveGrammarToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      contextSensitiveGrammarFromEventFlow (contextSensitiveGrammarToEventFlow x) =
        contextSensitiveGrammarFromEventFlow (contextSensitiveGrammarToEventFlow y) :=
    congrArg contextSensitiveGrammarFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ContextSensitiveGrammarTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ContextSensitiveGrammarTasteGate_single_carrier_alignment_round_trip y)))

private theorem ContextSensitiveGrammarTasteGate_single_carrier_alignment_fields :
    ∀ x y : ContextSensitiveGrammarUp,
      contextSensitiveGrammarFields x = contextSensitiveGrammarFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A1 R1 W1 D1 L1 Q1 M1 H1 C1 P1 N1 =>
      cases y with
      | mk A2 R2 W2 D2 L2 Q2 M2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance contextSensitiveGrammarBHistCarrier : BHistCarrier ContextSensitiveGrammarUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := contextSensitiveGrammarToEventFlow
  fromEventFlow := contextSensitiveGrammarFromEventFlow

instance contextSensitiveGrammarChapterTasteGate : ChapterTasteGate ContextSensitiveGrammarUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change contextSensitiveGrammarFromEventFlow (contextSensitiveGrammarToEventFlow x) = some x
    exact ContextSensitiveGrammarTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ContextSensitiveGrammarToEventFlow_injective heq)

instance contextSensitiveGrammarFieldFaithful : FieldFaithful ContextSensitiveGrammarUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := contextSensitiveGrammarFields
  field_faithful := ContextSensitiveGrammarTasteGate_single_carrier_alignment_fields

instance contextSensitiveGrammarNontrivial : Nontrivial ContextSensitiveGrammarUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ContextSensitiveGrammarUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ContextSensitiveGrammarUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem ContextSensitiveGrammarTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ContextSensitiveGrammarUp) ∧
      Nonempty (FieldFaithful ContextSensitiveGrammarUp) ∧
        Nonempty (Nontrivial ContextSensitiveGrammarUp) ∧
          (∀ h : BHist,
            contextSensitiveGrammarDecodeBHist (contextSensitiveGrammarEncodeBHist h) = h) ∧
            contextSensitiveGrammarEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨contextSensitiveGrammarChapterTasteGate⟩,
      ⟨contextSensitiveGrammarFieldFaithful⟩,
      ⟨contextSensitiveGrammarNontrivial⟩,
      ContextSensitiveGrammarTasteGate_single_carrier_alignment_decode,
      rfl⟩

end BEDC.Derived.ContextSensitiveGrammarUp.TasteGate
