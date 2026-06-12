import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICCriticalPairLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICCriticalPairLedgerUp : Type where
  | mk (B F D K J E S A H C P N : BHist) : MetaCICCriticalPairLedgerUp
  deriving DecidableEq

def metaCICCriticalPairLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICCriticalPairLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICCriticalPairLedgerEncodeBHist h

def metaCICCriticalPairLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICCriticalPairLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICCriticalPairLedgerDecodeBHist tail)

private def metaCICCriticalPairLedgerEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metaCICCriticalPairLedgerEventAt index rest

private theorem metaCICCriticalPairLedgerDecode_encode_bhist :
    ∀ h : BHist,
      metaCICCriticalPairLedgerDecodeBHist (metaCICCriticalPairLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metaCICCriticalPairLedgerFields :
    MetaCICCriticalPairLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICCriticalPairLedgerUp.mk B F D K J E S A H C P N =>
      [B, F, D, K, J, E, S, A, H, C, P, N]

def metaCICCriticalPairLedgerToEventFlow :
    MetaCICCriticalPairLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICCriticalPairLedgerUp.mk B F D K J E S A H C P N =>
      [metaCICCriticalPairLedgerEncodeBHist B,
        metaCICCriticalPairLedgerEncodeBHist F,
        metaCICCriticalPairLedgerEncodeBHist D,
        metaCICCriticalPairLedgerEncodeBHist K,
        metaCICCriticalPairLedgerEncodeBHist J,
        metaCICCriticalPairLedgerEncodeBHist E,
        metaCICCriticalPairLedgerEncodeBHist S,
        metaCICCriticalPairLedgerEncodeBHist A,
        metaCICCriticalPairLedgerEncodeBHist H,
        metaCICCriticalPairLedgerEncodeBHist C,
        metaCICCriticalPairLedgerEncodeBHist P,
        metaCICCriticalPairLedgerEncodeBHist N]

def metaCICCriticalPairLedgerFromEventFlow :
    EventFlow → Option MetaCICCriticalPairLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (MetaCICCriticalPairLedgerUp.mk
          (metaCICCriticalPairLedgerDecodeBHist (metaCICCriticalPairLedgerEventAt 0 ef))
          (metaCICCriticalPairLedgerDecodeBHist (metaCICCriticalPairLedgerEventAt 1 ef))
          (metaCICCriticalPairLedgerDecodeBHist (metaCICCriticalPairLedgerEventAt 2 ef))
          (metaCICCriticalPairLedgerDecodeBHist (metaCICCriticalPairLedgerEventAt 3 ef))
          (metaCICCriticalPairLedgerDecodeBHist (metaCICCriticalPairLedgerEventAt 4 ef))
          (metaCICCriticalPairLedgerDecodeBHist (metaCICCriticalPairLedgerEventAt 5 ef))
          (metaCICCriticalPairLedgerDecodeBHist (metaCICCriticalPairLedgerEventAt 6 ef))
          (metaCICCriticalPairLedgerDecodeBHist (metaCICCriticalPairLedgerEventAt 7 ef))
          (metaCICCriticalPairLedgerDecodeBHist (metaCICCriticalPairLedgerEventAt 8 ef))
          (metaCICCriticalPairLedgerDecodeBHist (metaCICCriticalPairLedgerEventAt 9 ef))
          (metaCICCriticalPairLedgerDecodeBHist (metaCICCriticalPairLedgerEventAt 10 ef))
          (metaCICCriticalPairLedgerDecodeBHist (metaCICCriticalPairLedgerEventAt 11 ef)))

private theorem metaCICCriticalPairLedger_round_trip :
    ∀ x : MetaCICCriticalPairLedgerUp,
      metaCICCriticalPairLedgerFromEventFlow
          (metaCICCriticalPairLedgerToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B F D K J E S A H C P N =>
      change
        some
          (MetaCICCriticalPairLedgerUp.mk
            (metaCICCriticalPairLedgerDecodeBHist (metaCICCriticalPairLedgerEncodeBHist B))
            (metaCICCriticalPairLedgerDecodeBHist (metaCICCriticalPairLedgerEncodeBHist F))
            (metaCICCriticalPairLedgerDecodeBHist (metaCICCriticalPairLedgerEncodeBHist D))
            (metaCICCriticalPairLedgerDecodeBHist (metaCICCriticalPairLedgerEncodeBHist K))
            (metaCICCriticalPairLedgerDecodeBHist (metaCICCriticalPairLedgerEncodeBHist J))
            (metaCICCriticalPairLedgerDecodeBHist (metaCICCriticalPairLedgerEncodeBHist E))
            (metaCICCriticalPairLedgerDecodeBHist (metaCICCriticalPairLedgerEncodeBHist S))
            (metaCICCriticalPairLedgerDecodeBHist (metaCICCriticalPairLedgerEncodeBHist A))
            (metaCICCriticalPairLedgerDecodeBHist (metaCICCriticalPairLedgerEncodeBHist H))
            (metaCICCriticalPairLedgerDecodeBHist (metaCICCriticalPairLedgerEncodeBHist C))
            (metaCICCriticalPairLedgerDecodeBHist (metaCICCriticalPairLedgerEncodeBHist P))
            (metaCICCriticalPairLedgerDecodeBHist (metaCICCriticalPairLedgerEncodeBHist N))) =
          some (MetaCICCriticalPairLedgerUp.mk B F D K J E S A H C P N)
      rw [metaCICCriticalPairLedgerDecode_encode_bhist B,
        metaCICCriticalPairLedgerDecode_encode_bhist F,
        metaCICCriticalPairLedgerDecode_encode_bhist D,
        metaCICCriticalPairLedgerDecode_encode_bhist K,
        metaCICCriticalPairLedgerDecode_encode_bhist J,
        metaCICCriticalPairLedgerDecode_encode_bhist E,
        metaCICCriticalPairLedgerDecode_encode_bhist S,
        metaCICCriticalPairLedgerDecode_encode_bhist A,
        metaCICCriticalPairLedgerDecode_encode_bhist H,
        metaCICCriticalPairLedgerDecode_encode_bhist C,
        metaCICCriticalPairLedgerDecode_encode_bhist P,
        metaCICCriticalPairLedgerDecode_encode_bhist N]

private theorem metaCICCriticalPairLedgerToEventFlow_injective
    {x y : MetaCICCriticalPairLedgerUp} :
    metaCICCriticalPairLedgerToEventFlow x =
        metaCICCriticalPairLedgerToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICCriticalPairLedgerFromEventFlow
          (metaCICCriticalPairLedgerToEventFlow x) =
        metaCICCriticalPairLedgerFromEventFlow
          (metaCICCriticalPairLedgerToEventFlow y) :=
    congrArg metaCICCriticalPairLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaCICCriticalPairLedger_round_trip x).symm
      (Eq.trans hread (metaCICCriticalPairLedger_round_trip y)))

private theorem metaCICCriticalPairLedgerFields_faithful :
    ∀ x y : MetaCICCriticalPairLedgerUp,
      metaCICCriticalPairLedgerFields x = metaCICCriticalPairLedgerFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B₁ F₁ D₁ K₁ J₁ E₁ S₁ A₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk B₂ F₂ D₂ K₂ J₂ E₂ S₂ A₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance metaCICCriticalPairLedgerBHistCarrier :
    BHistCarrier MetaCICCriticalPairLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICCriticalPairLedgerToEventFlow
  fromEventFlow := metaCICCriticalPairLedgerFromEventFlow

instance metaCICCriticalPairLedgerChapterTasteGate :
    ChapterTasteGate MetaCICCriticalPairLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICCriticalPairLedgerFromEventFlow
          (metaCICCriticalPairLedgerToEventFlow x) =
        some x
    exact metaCICCriticalPairLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    change
      metaCICCriticalPairLedgerToEventFlow x =
        metaCICCriticalPairLedgerToEventFlow y at heq
    exact hxy (metaCICCriticalPairLedgerToEventFlow_injective heq)

instance metaCICCriticalPairLedgerFieldFaithful :
    FieldFaithful MetaCICCriticalPairLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metaCICCriticalPairLedgerFields
  field_faithful := metaCICCriticalPairLedgerFields_faithful

instance metaCICCriticalPairLedgerNontrivial :
    Nontrivial MetaCICCriticalPairLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICCriticalPairLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      MetaCICCriticalPairLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetaCICCriticalPairLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICCriticalPairLedgerChapterTasteGate

theorem MetaCICCriticalPairLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist, metaCICCriticalPairLedgerDecodeBHist
        (metaCICCriticalPairLedgerEncodeBHist h) = h) ∧
      (∀ x : MetaCICCriticalPairLedgerUp,
        BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
        Nonempty (ChapterTasteGate MetaCICCriticalPairLedgerUp) ∧
          metaCICCriticalPairLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact metaCICCriticalPairLedgerDecode_encode_bhist
  · constructor
    · intro x
      change
        metaCICCriticalPairLedgerFromEventFlow
            (metaCICCriticalPairLedgerToEventFlow x) =
          some x
      exact metaCICCriticalPairLedger_round_trip x
    · constructor
      · exact ⟨metaCICCriticalPairLedgerChapterTasteGate⟩
      · rfl

end BEDC.Derived.MetaCICCriticalPairLedgerUp
