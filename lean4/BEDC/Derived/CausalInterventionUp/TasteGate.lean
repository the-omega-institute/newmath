import BEDC.Derived.CausalInterventionUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CausalInterventionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CausalInterventionUp : Type where
  | mk (M S T D J R K H C P N : BHist) : CausalInterventionUp
  deriving DecidableEq

def CausalInterventionTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: CausalInterventionTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: CausalInterventionTasteGate_single_carrier_alignment_encodeBHist h

def CausalInterventionTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (CausalInterventionTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (CausalInterventionTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem CausalInterventionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      CausalInterventionTasteGate_single_carrier_alignment_decodeBHist
        (CausalInterventionTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CausalInterventionTasteGate_single_carrier_alignment_fields :
    CausalInterventionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CausalInterventionUp.mk M S T D J R K H C P N => [M, S, T, D, J, R, K, H, C, P, N]

def CausalInterventionTasteGate_single_carrier_alignment_toEventFlow :
    CausalInterventionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | token =>
      (CausalInterventionTasteGate_single_carrier_alignment_fields token).map
        CausalInterventionTasteGate_single_carrier_alignment_encodeBHist

private def CausalInterventionTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CausalInterventionTasteGate_single_carrier_alignment_eventAtDefault index rest

def CausalInterventionTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option CausalInterventionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CausalInterventionUp.mk
      (CausalInterventionTasteGate_single_carrier_alignment_decodeBHist
        (CausalInterventionTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (CausalInterventionTasteGate_single_carrier_alignment_decodeBHist
        (CausalInterventionTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (CausalInterventionTasteGate_single_carrier_alignment_decodeBHist
        (CausalInterventionTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (CausalInterventionTasteGate_single_carrier_alignment_decodeBHist
        (CausalInterventionTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (CausalInterventionTasteGate_single_carrier_alignment_decodeBHist
        (CausalInterventionTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (CausalInterventionTasteGate_single_carrier_alignment_decodeBHist
        (CausalInterventionTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (CausalInterventionTasteGate_single_carrier_alignment_decodeBHist
        (CausalInterventionTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (CausalInterventionTasteGate_single_carrier_alignment_decodeBHist
        (CausalInterventionTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (CausalInterventionTasteGate_single_carrier_alignment_decodeBHist
        (CausalInterventionTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (CausalInterventionTasteGate_single_carrier_alignment_decodeBHist
        (CausalInterventionTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
      (CausalInterventionTasteGate_single_carrier_alignment_decodeBHist
        (CausalInterventionTasteGate_single_carrier_alignment_eventAtDefault 10 ef)))

private theorem CausalInterventionTasteGate_single_carrier_alignment_round_trip :
    ∀ token : CausalInterventionUp,
      CausalInterventionTasteGate_single_carrier_alignment_fromEventFlow
        (CausalInterventionTasteGate_single_carrier_alignment_toEventFlow token) = some token := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk M S T D J R K H C P N =>
      change
        some
          (CausalInterventionUp.mk
            (CausalInterventionTasteGate_single_carrier_alignment_decodeBHist
              (CausalInterventionTasteGate_single_carrier_alignment_encodeBHist M))
            (CausalInterventionTasteGate_single_carrier_alignment_decodeBHist
              (CausalInterventionTasteGate_single_carrier_alignment_encodeBHist S))
            (CausalInterventionTasteGate_single_carrier_alignment_decodeBHist
              (CausalInterventionTasteGate_single_carrier_alignment_encodeBHist T))
            (CausalInterventionTasteGate_single_carrier_alignment_decodeBHist
              (CausalInterventionTasteGate_single_carrier_alignment_encodeBHist D))
            (CausalInterventionTasteGate_single_carrier_alignment_decodeBHist
              (CausalInterventionTasteGate_single_carrier_alignment_encodeBHist J))
            (CausalInterventionTasteGate_single_carrier_alignment_decodeBHist
              (CausalInterventionTasteGate_single_carrier_alignment_encodeBHist R))
            (CausalInterventionTasteGate_single_carrier_alignment_decodeBHist
              (CausalInterventionTasteGate_single_carrier_alignment_encodeBHist K))
            (CausalInterventionTasteGate_single_carrier_alignment_decodeBHist
              (CausalInterventionTasteGate_single_carrier_alignment_encodeBHist H))
            (CausalInterventionTasteGate_single_carrier_alignment_decodeBHist
              (CausalInterventionTasteGate_single_carrier_alignment_encodeBHist C))
            (CausalInterventionTasteGate_single_carrier_alignment_decodeBHist
              (CausalInterventionTasteGate_single_carrier_alignment_encodeBHist P))
            (CausalInterventionTasteGate_single_carrier_alignment_decodeBHist
              (CausalInterventionTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (CausalInterventionUp.mk M S T D J R K H C P N)
      rw [CausalInterventionTasteGate_single_carrier_alignment_decode_encode M,
        CausalInterventionTasteGate_single_carrier_alignment_decode_encode S,
        CausalInterventionTasteGate_single_carrier_alignment_decode_encode T,
        CausalInterventionTasteGate_single_carrier_alignment_decode_encode D,
        CausalInterventionTasteGate_single_carrier_alignment_decode_encode J,
        CausalInterventionTasteGate_single_carrier_alignment_decode_encode R,
        CausalInterventionTasteGate_single_carrier_alignment_decode_encode K,
        CausalInterventionTasteGate_single_carrier_alignment_decode_encode H,
        CausalInterventionTasteGate_single_carrier_alignment_decode_encode C,
        CausalInterventionTasteGate_single_carrier_alignment_decode_encode P,
        CausalInterventionTasteGate_single_carrier_alignment_decode_encode N]

private theorem CausalInterventionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CausalInterventionUp} :
    CausalInterventionTasteGate_single_carrier_alignment_toEventFlow x =
      CausalInterventionTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      CausalInterventionTasteGate_single_carrier_alignment_fromEventFlow
          (CausalInterventionTasteGate_single_carrier_alignment_toEventFlow x) =
        CausalInterventionTasteGate_single_carrier_alignment_fromEventFlow
          (CausalInterventionTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg CausalInterventionTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CausalInterventionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CausalInterventionTasteGate_single_carrier_alignment_round_trip y)))

private theorem CausalInterventionTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : CausalInterventionUp,
      CausalInterventionTasteGate_single_carrier_alignment_fields x =
          CausalInterventionTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 S1 T1 D1 J1 R1 K1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 S2 T2 D2 J2 R2 K2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance causalInterventionBHistCarrier : BHistCarrier CausalInterventionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CausalInterventionTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CausalInterventionTasteGate_single_carrier_alignment_fromEventFlow

instance causalInterventionChapterTasteGate : ChapterTasteGate CausalInterventionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro token
    change
      CausalInterventionTasteGate_single_carrier_alignment_fromEventFlow
        (CausalInterventionTasteGate_single_carrier_alignment_toEventFlow token) = some token
    exact CausalInterventionTasteGate_single_carrier_alignment_round_trip token
  layer_separation := by
    intro x y hxy heq
    exact hxy (CausalInterventionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance causalInterventionFieldFaithful : FieldFaithful CausalInterventionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := CausalInterventionTasteGate_single_carrier_alignment_fields
  field_faithful := CausalInterventionTasteGate_single_carrier_alignment_field_faithful

instance causalInterventionNontrivial : Nontrivial CausalInterventionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CausalInterventionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CausalInterventionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CausalInterventionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  causalInterventionChapterTasteGate

theorem CausalInterventionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CausalInterventionUp) ∧
      Nonempty (FieldFaithful CausalInterventionUp) ∧
        Nonempty (Nontrivial CausalInterventionUp) ∧
          CausalInterventionTasteGate_single_carrier_alignment_encodeBHist BHist.Empty = [] ∧
            CausalInterventionTasteGate_single_carrier_alignment_encodeBHist
              (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨causalInterventionChapterTasteGate⟩,
      ⟨causalInterventionFieldFaithful⟩,
      ⟨causalInterventionNontrivial⟩, rfl, rfl⟩

end BEDC.Derived.CausalInterventionUp
