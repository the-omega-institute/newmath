import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EmpiricalRegularityPersistenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EmpiricalRegularityPersistenceUp : Type where
  | mk : (M R K L G A S F H C P N : BHist) → EmpiricalRegularityPersistenceUp
  deriving DecidableEq

def empiricalRegularityPersistenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: empiricalRegularityPersistenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: empiricalRegularityPersistenceEncodeBHist h

def empiricalRegularityPersistenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (empiricalRegularityPersistenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (empiricalRegularityPersistenceDecodeBHist tail)

private theorem empiricalRegularityPersistenceDecode_encode_bhist :
    ∀ h : BHist,
      empiricalRegularityPersistenceDecodeBHist
        (empiricalRegularityPersistenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def empiricalRegularityPersistenceFields :
    EmpiricalRegularityPersistenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EmpiricalRegularityPersistenceUp.mk M R K L G A S F H C P N =>
      [M, R, K, L, G, A, S, F, H, C, P, N]

def empiricalRegularityPersistenceToEventFlow :
    EmpiricalRegularityPersistenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | EmpiricalRegularityPersistenceUp.mk M R K L G A S F H C P N =>
      [[BMark.b0],
        empiricalRegularityPersistenceEncodeBHist M,
        [BMark.b1, BMark.b0],
        empiricalRegularityPersistenceEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b0],
        empiricalRegularityPersistenceEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        empiricalRegularityPersistenceEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        empiricalRegularityPersistenceEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        empiricalRegularityPersistenceEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        empiricalRegularityPersistenceEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        empiricalRegularityPersistenceEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        empiricalRegularityPersistenceEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        empiricalRegularityPersistenceEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        empiricalRegularityPersistenceEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        empiricalRegularityPersistenceEncodeBHist N]

private def empiricalRegularityPersistenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      empiricalRegularityPersistenceEventAtDefault index rest

def empiricalRegularityPersistenceFromEventFlow
    (ef : EventFlow) : Option EmpiricalRegularityPersistenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EmpiricalRegularityPersistenceUp.mk
      (empiricalRegularityPersistenceDecodeBHist
        (empiricalRegularityPersistenceEventAtDefault 1 ef))
      (empiricalRegularityPersistenceDecodeBHist
        (empiricalRegularityPersistenceEventAtDefault 3 ef))
      (empiricalRegularityPersistenceDecodeBHist
        (empiricalRegularityPersistenceEventAtDefault 5 ef))
      (empiricalRegularityPersistenceDecodeBHist
        (empiricalRegularityPersistenceEventAtDefault 7 ef))
      (empiricalRegularityPersistenceDecodeBHist
        (empiricalRegularityPersistenceEventAtDefault 9 ef))
      (empiricalRegularityPersistenceDecodeBHist
        (empiricalRegularityPersistenceEventAtDefault 11 ef))
      (empiricalRegularityPersistenceDecodeBHist
        (empiricalRegularityPersistenceEventAtDefault 13 ef))
      (empiricalRegularityPersistenceDecodeBHist
        (empiricalRegularityPersistenceEventAtDefault 15 ef))
      (empiricalRegularityPersistenceDecodeBHist
        (empiricalRegularityPersistenceEventAtDefault 17 ef))
      (empiricalRegularityPersistenceDecodeBHist
        (empiricalRegularityPersistenceEventAtDefault 19 ef))
      (empiricalRegularityPersistenceDecodeBHist
        (empiricalRegularityPersistenceEventAtDefault 21 ef))
      (empiricalRegularityPersistenceDecodeBHist
        (empiricalRegularityPersistenceEventAtDefault 23 ef)))

private theorem empiricalRegularityPersistence_round_trip :
    ∀ x : EmpiricalRegularityPersistenceUp,
      empiricalRegularityPersistenceFromEventFlow
        (empiricalRegularityPersistenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M R K L G A S F H C P N =>
      change
        some
          (EmpiricalRegularityPersistenceUp.mk
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist M))
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist R))
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist K))
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist L))
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist G))
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist A))
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist S))
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist F))
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist H))
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist C))
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist P))
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist N))) =
          some (EmpiricalRegularityPersistenceUp.mk M R K L G A S F H C P N)
      rw [empiricalRegularityPersistenceDecode_encode_bhist M,
        empiricalRegularityPersistenceDecode_encode_bhist R,
        empiricalRegularityPersistenceDecode_encode_bhist K,
        empiricalRegularityPersistenceDecode_encode_bhist L,
        empiricalRegularityPersistenceDecode_encode_bhist G,
        empiricalRegularityPersistenceDecode_encode_bhist A,
        empiricalRegularityPersistenceDecode_encode_bhist S,
        empiricalRegularityPersistenceDecode_encode_bhist F,
        empiricalRegularityPersistenceDecode_encode_bhist H,
        empiricalRegularityPersistenceDecode_encode_bhist C,
        empiricalRegularityPersistenceDecode_encode_bhist P,
        empiricalRegularityPersistenceDecode_encode_bhist N]

private theorem empiricalRegularityPersistenceToEventFlow_injective
    {x y : EmpiricalRegularityPersistenceUp} :
    empiricalRegularityPersistenceToEventFlow x =
      empiricalRegularityPersistenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      empiricalRegularityPersistenceFromEventFlow
          (empiricalRegularityPersistenceToEventFlow x) =
        empiricalRegularityPersistenceFromEventFlow
          (empiricalRegularityPersistenceToEventFlow y) :=
    congrArg empiricalRegularityPersistenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (empiricalRegularityPersistence_round_trip x).symm
      (Eq.trans hread (empiricalRegularityPersistence_round_trip y)))

private theorem empiricalRegularityPersistence_fields :
    ∀ x y : EmpiricalRegularityPersistenceUp,
      empiricalRegularityPersistenceFields x =
        empiricalRegularityPersistenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ R₁ K₁ L₁ G₁ A₁ S₁ F₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk M₂ R₂ K₂ L₂ G₂ A₂ S₂ F₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance empiricalRegularityPersistenceBHistCarrier :
    BHistCarrier EmpiricalRegularityPersistenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := empiricalRegularityPersistenceToEventFlow
  fromEventFlow := empiricalRegularityPersistenceFromEventFlow

instance empiricalRegularityPersistenceChapterTasteGate :
    ChapterTasteGate EmpiricalRegularityPersistenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      empiricalRegularityPersistenceFromEventFlow
        (empiricalRegularityPersistenceToEventFlow x) = some x
    exact empiricalRegularityPersistence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (empiricalRegularityPersistenceToEventFlow_injective heq)

instance empiricalRegularityPersistenceFieldFaithful :
    FieldFaithful EmpiricalRegularityPersistenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := empiricalRegularityPersistenceFields
  field_faithful := empiricalRegularityPersistence_fields

instance empiricalRegularityPersistenceNontrivial :
    Nontrivial EmpiricalRegularityPersistenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EmpiricalRegularityPersistenceUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      EmpiricalRegularityPersistenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate EmpiricalRegularityPersistenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  empiricalRegularityPersistenceChapterTasteGate

theorem EmpiricalRegularityPersistenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      empiricalRegularityPersistenceDecodeBHist
        (empiricalRegularityPersistenceEncodeBHist h) = h) ∧
      (∀ x : EmpiricalRegularityPersistenceUp,
        empiricalRegularityPersistenceFromEventFlow
          (empiricalRegularityPersistenceToEventFlow x) = some x) ∧
        (∀ x y : EmpiricalRegularityPersistenceUp,
          empiricalRegularityPersistenceToEventFlow x =
            empiricalRegularityPersistenceToEventFlow y → x = y) ∧
          empiricalRegularityPersistenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨empiricalRegularityPersistenceDecode_encode_bhist,
      empiricalRegularityPersistence_round_trip,
      (by
        intro x y heq
        exact empiricalRegularityPersistenceToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.EmpiricalRegularityPersistenceUp
