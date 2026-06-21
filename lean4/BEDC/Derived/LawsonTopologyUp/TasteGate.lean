import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LawsonTopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LawsonTopologyUp : Type where
  | mk (D O K S T H C P N : BHist) : LawsonTopologyUp
  deriving DecidableEq

def lawsonTopologyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lawsonTopologyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lawsonTopologyEncodeBHist h

def lawsonTopologyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lawsonTopologyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lawsonTopologyDecodeBHist tail)

private theorem lawsonTopologyDecode_encode_bhist :
    ∀ h : BHist, lawsonTopologyDecodeBHist (lawsonTopologyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def lawsonTopologyFields : LawsonTopologyUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | LawsonTopologyUp.mk D O K S T H C P N =>
      [D, O, K, S, T, H, C, P, N]

def lawsonTopologyToEventFlow : LawsonTopologyUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | LawsonTopologyUp.mk D O K S T H C P N =>
      [lawsonTopologyEncodeBHist D,
        lawsonTopologyEncodeBHist O,
        lawsonTopologyEncodeBHist K,
        lawsonTopologyEncodeBHist S,
        lawsonTopologyEncodeBHist T,
        lawsonTopologyEncodeBHist H,
        lawsonTopologyEncodeBHist C,
        lawsonTopologyEncodeBHist P,
        lawsonTopologyEncodeBHist N]

private def lawsonTopologyEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => lawsonTopologyEventAtDefault index rest

def lawsonTopologyFromEventFlow : EventFlow → Option LawsonTopologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (LawsonTopologyUp.mk
        (lawsonTopologyDecodeBHist (lawsonTopologyEventAtDefault 0 ef))
        (lawsonTopologyDecodeBHist (lawsonTopologyEventAtDefault 1 ef))
        (lawsonTopologyDecodeBHist (lawsonTopologyEventAtDefault 2 ef))
        (lawsonTopologyDecodeBHist (lawsonTopologyEventAtDefault 3 ef))
        (lawsonTopologyDecodeBHist (lawsonTopologyEventAtDefault 4 ef))
        (lawsonTopologyDecodeBHist (lawsonTopologyEventAtDefault 5 ef))
        (lawsonTopologyDecodeBHist (lawsonTopologyEventAtDefault 6 ef))
        (lawsonTopologyDecodeBHist (lawsonTopologyEventAtDefault 7 ef))
        (lawsonTopologyDecodeBHist (lawsonTopologyEventAtDefault 8 ef)))

private theorem lawsonTopology_round_trip :
    ∀ x : LawsonTopologyUp,
      lawsonTopologyFromEventFlow (lawsonTopologyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D O K S T H C P N =>
      change
        some
          (LawsonTopologyUp.mk
            (lawsonTopologyDecodeBHist (lawsonTopologyEncodeBHist D))
            (lawsonTopologyDecodeBHist (lawsonTopologyEncodeBHist O))
            (lawsonTopologyDecodeBHist (lawsonTopologyEncodeBHist K))
            (lawsonTopologyDecodeBHist (lawsonTopologyEncodeBHist S))
            (lawsonTopologyDecodeBHist (lawsonTopologyEncodeBHist T))
            (lawsonTopologyDecodeBHist (lawsonTopologyEncodeBHist H))
            (lawsonTopologyDecodeBHist (lawsonTopologyEncodeBHist C))
            (lawsonTopologyDecodeBHist (lawsonTopologyEncodeBHist P))
            (lawsonTopologyDecodeBHist (lawsonTopologyEncodeBHist N))) =
          some (LawsonTopologyUp.mk D O K S T H C P N)
      rw [lawsonTopologyDecode_encode_bhist D]
      rw [lawsonTopologyDecode_encode_bhist O]
      rw [lawsonTopologyDecode_encode_bhist K]
      rw [lawsonTopologyDecode_encode_bhist S]
      rw [lawsonTopologyDecode_encode_bhist T]
      rw [lawsonTopologyDecode_encode_bhist H]
      rw [lawsonTopologyDecode_encode_bhist C]
      rw [lawsonTopologyDecode_encode_bhist P]
      rw [lawsonTopologyDecode_encode_bhist N]

private theorem lawsonTopologyToEventFlow_injective {x y : LawsonTopologyUp} :
    lawsonTopologyToEventFlow x = lawsonTopologyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          lawsonTopologyFromEventFlow (lawsonTopologyToEventFlow x) :=
        (lawsonTopology_round_trip x).symm
      _ =
          lawsonTopologyFromEventFlow (lawsonTopologyToEventFlow y) :=
        congrArg lawsonTopologyFromEventFlow hxy
      _ = some y := lawsonTopology_round_trip y
  exact Option.some.inj optionEq

private theorem lawsonTopology_field_faithful :
    ∀ x y : LawsonTopologyUp, lawsonTopologyFields x = lawsonTopologyFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk D1 O1 K1 S1 T1 H1 C1 P1 N1 =>
      cases y with
      | mk D2 O2 K2 S2 T2 H2 C2 P2 N2 =>
          cases h
          rfl

instance lawsonTopologyBHistCarrier : BHistCarrier LawsonTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lawsonTopologyToEventFlow
  fromEventFlow := lawsonTopologyFromEventFlow

instance lawsonTopologyChapterTasteGate : ChapterTasteGate LawsonTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lawsonTopologyFromEventFlow (lawsonTopologyToEventFlow x) = some x
    exact lawsonTopology_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (lawsonTopologyToEventFlow_injective heq)

instance lawsonTopologyFieldFaithful : FieldFaithful LawsonTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := lawsonTopologyFields
  field_faithful := lawsonTopology_field_faithful

instance lawsonTopologyNontrivial :
    BEDC.Meta.TasteGate.Nontrivial LawsonTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LawsonTopologyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LawsonTopologyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LawsonTopologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  lawsonTopologyChapterTasteGate

theorem LawsonTopologyTasteGate_single_carrier_alignment :
    (∀ h : BHist, lawsonTopologyDecodeBHist (lawsonTopologyEncodeBHist h) = h) ∧
      (∀ x : LawsonTopologyUp,
        lawsonTopologyFromEventFlow (lawsonTopologyToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  · intro x
    cases x with
    | mk D O K S T H C P N =>
        change
          some
            (LawsonTopologyUp.mk
              (lawsonTopologyDecodeBHist (lawsonTopologyEncodeBHist D))
              (lawsonTopologyDecodeBHist (lawsonTopologyEncodeBHist O))
              (lawsonTopologyDecodeBHist (lawsonTopologyEncodeBHist K))
              (lawsonTopologyDecodeBHist (lawsonTopologyEncodeBHist S))
              (lawsonTopologyDecodeBHist (lawsonTopologyEncodeBHist T))
              (lawsonTopologyDecodeBHist (lawsonTopologyEncodeBHist H))
              (lawsonTopologyDecodeBHist (lawsonTopologyEncodeBHist C))
              (lawsonTopologyDecodeBHist (lawsonTopologyEncodeBHist P))
              (lawsonTopologyDecodeBHist (lawsonTopologyEncodeBHist N))) =
            some (LawsonTopologyUp.mk D O K S T H C P N)
        rw [lawsonTopologyDecode_encode_bhist D]
        rw [lawsonTopologyDecode_encode_bhist O]
        rw [lawsonTopologyDecode_encode_bhist K]
        rw [lawsonTopologyDecode_encode_bhist S]
        rw [lawsonTopologyDecode_encode_bhist T]
        rw [lawsonTopologyDecode_encode_bhist H]
        rw [lawsonTopologyDecode_encode_bhist C]
        rw [lawsonTopologyDecode_encode_bhist P]
        rw [lawsonTopologyDecode_encode_bhist N]

end BEDC.Derived.LawsonTopologyUp
