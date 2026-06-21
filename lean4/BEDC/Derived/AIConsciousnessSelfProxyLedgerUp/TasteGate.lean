import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AIConsciousnessSelfProxyLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AIConsciousnessSelfProxyLedgerUp : Type where
  | mk (L K O S Nc H C P G N : BHist) : AIConsciousnessSelfProxyLedgerUp
  deriving DecidableEq

def aiConsciousnessSelfProxyLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: aiConsciousnessSelfProxyLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: aiConsciousnessSelfProxyLedgerEncodeBHist h

def aiConsciousnessSelfProxyLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (aiConsciousnessSelfProxyLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (aiConsciousnessSelfProxyLedgerDecodeBHist tail)

private theorem aiConsciousnessSelfProxyLedgerDecode_encode_bhist :
    ∀ h : BHist,
      aiConsciousnessSelfProxyLedgerDecodeBHist
        (aiConsciousnessSelfProxyLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def aiConsciousnessSelfProxyLedgerFields :
    AIConsciousnessSelfProxyLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AIConsciousnessSelfProxyLedgerUp.mk L K O S Nc H C P G N =>
      [L, K, O, S, Nc, H, C, P, G, N]

def aiConsciousnessSelfProxyLedgerToEventFlow :
    AIConsciousnessSelfProxyLedgerUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (aiConsciousnessSelfProxyLedgerFields x).map
    aiConsciousnessSelfProxyLedgerEncodeBHist

private def aiConsciousnessSelfProxyLedgerEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      aiConsciousnessSelfProxyLedgerEventAtDefault index rest

def aiConsciousnessSelfProxyLedgerFromEventFlow :
    EventFlow → Option AIConsciousnessSelfProxyLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (AIConsciousnessSelfProxyLedgerUp.mk
          (aiConsciousnessSelfProxyLedgerDecodeBHist
            (aiConsciousnessSelfProxyLedgerEventAtDefault 0 ef))
          (aiConsciousnessSelfProxyLedgerDecodeBHist
            (aiConsciousnessSelfProxyLedgerEventAtDefault 1 ef))
          (aiConsciousnessSelfProxyLedgerDecodeBHist
            (aiConsciousnessSelfProxyLedgerEventAtDefault 2 ef))
          (aiConsciousnessSelfProxyLedgerDecodeBHist
            (aiConsciousnessSelfProxyLedgerEventAtDefault 3 ef))
          (aiConsciousnessSelfProxyLedgerDecodeBHist
            (aiConsciousnessSelfProxyLedgerEventAtDefault 4 ef))
          (aiConsciousnessSelfProxyLedgerDecodeBHist
            (aiConsciousnessSelfProxyLedgerEventAtDefault 5 ef))
          (aiConsciousnessSelfProxyLedgerDecodeBHist
            (aiConsciousnessSelfProxyLedgerEventAtDefault 6 ef))
          (aiConsciousnessSelfProxyLedgerDecodeBHist
            (aiConsciousnessSelfProxyLedgerEventAtDefault 7 ef))
          (aiConsciousnessSelfProxyLedgerDecodeBHist
            (aiConsciousnessSelfProxyLedgerEventAtDefault 8 ef))
          (aiConsciousnessSelfProxyLedgerDecodeBHist
            (aiConsciousnessSelfProxyLedgerEventAtDefault 9 ef)))

private theorem aiConsciousnessSelfProxyLedger_round_trip :
    ∀ x : AIConsciousnessSelfProxyLedgerUp,
      aiConsciousnessSelfProxyLedgerFromEventFlow
        (aiConsciousnessSelfProxyLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L K O S Nc H C P G N =>
      change
        some
          (AIConsciousnessSelfProxyLedgerUp.mk
            (aiConsciousnessSelfProxyLedgerDecodeBHist
              (aiConsciousnessSelfProxyLedgerEncodeBHist L))
            (aiConsciousnessSelfProxyLedgerDecodeBHist
              (aiConsciousnessSelfProxyLedgerEncodeBHist K))
            (aiConsciousnessSelfProxyLedgerDecodeBHist
              (aiConsciousnessSelfProxyLedgerEncodeBHist O))
            (aiConsciousnessSelfProxyLedgerDecodeBHist
              (aiConsciousnessSelfProxyLedgerEncodeBHist S))
            (aiConsciousnessSelfProxyLedgerDecodeBHist
              (aiConsciousnessSelfProxyLedgerEncodeBHist Nc))
            (aiConsciousnessSelfProxyLedgerDecodeBHist
              (aiConsciousnessSelfProxyLedgerEncodeBHist H))
            (aiConsciousnessSelfProxyLedgerDecodeBHist
              (aiConsciousnessSelfProxyLedgerEncodeBHist C))
            (aiConsciousnessSelfProxyLedgerDecodeBHist
              (aiConsciousnessSelfProxyLedgerEncodeBHist P))
            (aiConsciousnessSelfProxyLedgerDecodeBHist
              (aiConsciousnessSelfProxyLedgerEncodeBHist G))
            (aiConsciousnessSelfProxyLedgerDecodeBHist
              (aiConsciousnessSelfProxyLedgerEncodeBHist N))) =
          some (AIConsciousnessSelfProxyLedgerUp.mk L K O S Nc H C P G N)
      rw [aiConsciousnessSelfProxyLedgerDecode_encode_bhist L,
        aiConsciousnessSelfProxyLedgerDecode_encode_bhist K,
        aiConsciousnessSelfProxyLedgerDecode_encode_bhist O,
        aiConsciousnessSelfProxyLedgerDecode_encode_bhist S,
        aiConsciousnessSelfProxyLedgerDecode_encode_bhist Nc,
        aiConsciousnessSelfProxyLedgerDecode_encode_bhist H,
        aiConsciousnessSelfProxyLedgerDecode_encode_bhist C,
        aiConsciousnessSelfProxyLedgerDecode_encode_bhist P,
        aiConsciousnessSelfProxyLedgerDecode_encode_bhist G,
        aiConsciousnessSelfProxyLedgerDecode_encode_bhist N]

private theorem aiConsciousnessSelfProxyLedgerToEventFlow_injective
    {x y : AIConsciousnessSelfProxyLedgerUp} :
    aiConsciousnessSelfProxyLedgerToEventFlow x =
        aiConsciousnessSelfProxyLedgerToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      aiConsciousnessSelfProxyLedgerFromEventFlow
          (aiConsciousnessSelfProxyLedgerToEventFlow x) =
        aiConsciousnessSelfProxyLedgerFromEventFlow
          (aiConsciousnessSelfProxyLedgerToEventFlow y) :=
    congrArg aiConsciousnessSelfProxyLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (aiConsciousnessSelfProxyLedger_round_trip x).symm
      (Eq.trans hread (aiConsciousnessSelfProxyLedger_round_trip y)))

private theorem aiConsciousnessSelfProxyLedgerFieldFaithfulProof :
    ∀ x y : AIConsciousnessSelfProxyLedgerUp,
      aiConsciousnessSelfProxyLedgerFields x =
          aiConsciousnessSelfProxyLedgerFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L K O S Nc H C P G N =>
      cases y with
      | mk L' K' O' S' Nc' H' C' P' G' N' =>
          cases hfields
          rfl

instance aiConsciousnessSelfProxyLedgerBHistCarrier :
    BHistCarrier AIConsciousnessSelfProxyLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := aiConsciousnessSelfProxyLedgerToEventFlow
  fromEventFlow := aiConsciousnessSelfProxyLedgerFromEventFlow

instance aiConsciousnessSelfProxyLedgerChapterTasteGate :
    ChapterTasteGate AIConsciousnessSelfProxyLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      aiConsciousnessSelfProxyLedgerFromEventFlow
        (aiConsciousnessSelfProxyLedgerToEventFlow x) = some x
    exact aiConsciousnessSelfProxyLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (aiConsciousnessSelfProxyLedgerToEventFlow_injective heq)

instance aiConsciousnessSelfProxyLedgerFieldFaithful :
    FieldFaithful AIConsciousnessSelfProxyLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := aiConsciousnessSelfProxyLedgerFields
  field_faithful := aiConsciousnessSelfProxyLedgerFieldFaithfulProof

instance aiConsciousnessSelfProxyLedgerNontrivial :
    Nontrivial AIConsciousnessSelfProxyLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AIConsciousnessSelfProxyLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      AIConsciousnessSelfProxyLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem AIConsciousnessSelfProxyLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        aiConsciousnessSelfProxyLedgerDecodeBHist
          (aiConsciousnessSelfProxyLedgerEncodeBHist h) = h) ∧
      (∀ x : AIConsciousnessSelfProxyLedgerUp,
        aiConsciousnessSelfProxyLedgerFromEventFlow
          (aiConsciousnessSelfProxyLedgerToEventFlow x) = some x) ∧
        (∀ x y : AIConsciousnessSelfProxyLedgerUp,
          aiConsciousnessSelfProxyLedgerToEventFlow x =
              aiConsciousnessSelfProxyLedgerToEventFlow y →
            x = y) ∧
          aiConsciousnessSelfProxyLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact aiConsciousnessSelfProxyLedgerDecode_encode_bhist
  · constructor
    · exact aiConsciousnessSelfProxyLedger_round_trip
    · constructor
      · intro x y heq
        exact aiConsciousnessSelfProxyLedgerToEventFlow_injective heq
      · rfl

end BEDC.Derived.AIConsciousnessSelfProxyLedgerUp
