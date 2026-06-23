import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICAuditSynthesisPacketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICAuditSynthesisPacketUp : Type where
  | mk : (S C N U D A B H R P L : BHist) → MetaCICAuditSynthesisPacketUp
  deriving DecidableEq

def metaCICAuditSynthesisPacketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICAuditSynthesisPacketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICAuditSynthesisPacketEncodeBHist h

def metaCICAuditSynthesisPacketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICAuditSynthesisPacketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICAuditSynthesisPacketDecodeBHist tail)

private theorem metaCICAuditSynthesisPacketDecode_encode_bhist :
    ∀ h : BHist,
      metaCICAuditSynthesisPacketDecodeBHist
          (metaCICAuditSynthesisPacketEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metaCICAuditSynthesisPacketFields :
    MetaCICAuditSynthesisPacketUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICAuditSynthesisPacketUp.mk S C N U D A B H R P L =>
      [S, C, N, U, D, A, B, H, R, P, L]

def metaCICAuditSynthesisPacketToEventFlow :
    MetaCICAuditSynthesisPacketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (metaCICAuditSynthesisPacketFields x).map metaCICAuditSynthesisPacketEncodeBHist

private def metaCICAuditSynthesisPacketEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      metaCICAuditSynthesisPacketEventAtDefault index rest

def metaCICAuditSynthesisPacketFromEventFlow
    (ef : EventFlow) : Option MetaCICAuditSynthesisPacketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetaCICAuditSynthesisPacketUp.mk
      (metaCICAuditSynthesisPacketDecodeBHist
        (metaCICAuditSynthesisPacketEventAtDefault 0 ef))
      (metaCICAuditSynthesisPacketDecodeBHist
        (metaCICAuditSynthesisPacketEventAtDefault 1 ef))
      (metaCICAuditSynthesisPacketDecodeBHist
        (metaCICAuditSynthesisPacketEventAtDefault 2 ef))
      (metaCICAuditSynthesisPacketDecodeBHist
        (metaCICAuditSynthesisPacketEventAtDefault 3 ef))
      (metaCICAuditSynthesisPacketDecodeBHist
        (metaCICAuditSynthesisPacketEventAtDefault 4 ef))
      (metaCICAuditSynthesisPacketDecodeBHist
        (metaCICAuditSynthesisPacketEventAtDefault 5 ef))
      (metaCICAuditSynthesisPacketDecodeBHist
        (metaCICAuditSynthesisPacketEventAtDefault 6 ef))
      (metaCICAuditSynthesisPacketDecodeBHist
        (metaCICAuditSynthesisPacketEventAtDefault 7 ef))
      (metaCICAuditSynthesisPacketDecodeBHist
        (metaCICAuditSynthesisPacketEventAtDefault 8 ef))
      (metaCICAuditSynthesisPacketDecodeBHist
        (metaCICAuditSynthesisPacketEventAtDefault 9 ef))
      (metaCICAuditSynthesisPacketDecodeBHist
        (metaCICAuditSynthesisPacketEventAtDefault 10 ef)))

private theorem metaCICAuditSynthesisPacket_round_trip :
    ∀ x : MetaCICAuditSynthesisPacketUp,
      metaCICAuditSynthesisPacketFromEventFlow
          (metaCICAuditSynthesisPacketToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S C N U D A B H R P L =>
      change
        some
          (MetaCICAuditSynthesisPacketUp.mk
            (metaCICAuditSynthesisPacketDecodeBHist
              (metaCICAuditSynthesisPacketEncodeBHist S))
            (metaCICAuditSynthesisPacketDecodeBHist
              (metaCICAuditSynthesisPacketEncodeBHist C))
            (metaCICAuditSynthesisPacketDecodeBHist
              (metaCICAuditSynthesisPacketEncodeBHist N))
            (metaCICAuditSynthesisPacketDecodeBHist
              (metaCICAuditSynthesisPacketEncodeBHist U))
            (metaCICAuditSynthesisPacketDecodeBHist
              (metaCICAuditSynthesisPacketEncodeBHist D))
            (metaCICAuditSynthesisPacketDecodeBHist
              (metaCICAuditSynthesisPacketEncodeBHist A))
            (metaCICAuditSynthesisPacketDecodeBHist
              (metaCICAuditSynthesisPacketEncodeBHist B))
            (metaCICAuditSynthesisPacketDecodeBHist
              (metaCICAuditSynthesisPacketEncodeBHist H))
            (metaCICAuditSynthesisPacketDecodeBHist
              (metaCICAuditSynthesisPacketEncodeBHist R))
            (metaCICAuditSynthesisPacketDecodeBHist
              (metaCICAuditSynthesisPacketEncodeBHist P))
            (metaCICAuditSynthesisPacketDecodeBHist
              (metaCICAuditSynthesisPacketEncodeBHist L))) =
          some (MetaCICAuditSynthesisPacketUp.mk S C N U D A B H R P L)
      rw [metaCICAuditSynthesisPacketDecode_encode_bhist S,
        metaCICAuditSynthesisPacketDecode_encode_bhist C,
        metaCICAuditSynthesisPacketDecode_encode_bhist N,
        metaCICAuditSynthesisPacketDecode_encode_bhist U,
        metaCICAuditSynthesisPacketDecode_encode_bhist D,
        metaCICAuditSynthesisPacketDecode_encode_bhist A,
        metaCICAuditSynthesisPacketDecode_encode_bhist B,
        metaCICAuditSynthesisPacketDecode_encode_bhist H,
        metaCICAuditSynthesisPacketDecode_encode_bhist R,
        metaCICAuditSynthesisPacketDecode_encode_bhist P,
        metaCICAuditSynthesisPacketDecode_encode_bhist L]

theorem metaCICAuditSynthesisPacketToEventFlow_injective
    {x y : MetaCICAuditSynthesisPacketUp} :
    metaCICAuditSynthesisPacketToEventFlow x =
      metaCICAuditSynthesisPacketToEventFlow y →
    x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICAuditSynthesisPacketFromEventFlow
          (metaCICAuditSynthesisPacketToEventFlow x) =
        metaCICAuditSynthesisPacketFromEventFlow
          (metaCICAuditSynthesisPacketToEventFlow y) :=
    congrArg metaCICAuditSynthesisPacketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaCICAuditSynthesisPacket_round_trip x).symm
      (Eq.trans hread (metaCICAuditSynthesisPacket_round_trip y)))

instance metaCICAuditSynthesisPacketBHistCarrier :
    BHistCarrier MetaCICAuditSynthesisPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICAuditSynthesisPacketToEventFlow
  fromEventFlow := metaCICAuditSynthesisPacketFromEventFlow

instance metaCICAuditSynthesisPacketChapterTasteGate :
    ChapterTasteGate MetaCICAuditSynthesisPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICAuditSynthesisPacketFromEventFlow
          (metaCICAuditSynthesisPacketToEventFlow x) =
        some x
    exact metaCICAuditSynthesisPacket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICAuditSynthesisPacketToEventFlow_injective heq)

instance metaCICAuditSynthesisPacketFieldFaithful :
    FieldFaithful MetaCICAuditSynthesisPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metaCICAuditSynthesisPacketFields
  field_faithful := by
    intro x y h
    cases x with
    | mk S1 C1 N1 U1 D1 A1 B1 H1 R1 P1 L1 =>
        cases y with
        | mk S2 C2 N2 U2 D2 A2 B2 H2 R2 P2 L2 =>
            cases h
            rfl

instance metaCICAuditSynthesisPacketNontrivial :
    Nontrivial MetaCICAuditSynthesisPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICAuditSynthesisPacketUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      MetaCICAuditSynthesisPacketUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetaCICAuditSynthesisPacketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICAuditSynthesisPacketChapterTasteGate

theorem MetaCICAuditSynthesisPacketTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate MetaCICAuditSynthesisPacketUp) ∧
      Nonempty (FieldFaithful MetaCICAuditSynthesisPacketUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial MetaCICAuditSynthesisPacketUp) ∧
          metaCICAuditSynthesisPacketEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ h : BHist,
              metaCICAuditSynthesisPacketDecodeBHist
                  (metaCICAuditSynthesisPacketEncodeBHist h) =
                h) ∧
              (∀ x : MetaCICAuditSynthesisPacketUp,
                metaCICAuditSynthesisPacketFromEventFlow
                    (metaCICAuditSynthesisPacketToEventFlow x) =
                  some x) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨metaCICAuditSynthesisPacketChapterTasteGate⟩
  · constructor
    · exact ⟨metaCICAuditSynthesisPacketFieldFaithful⟩
    · constructor
      · exact ⟨metaCICAuditSynthesisPacketNontrivial⟩
      · constructor
        · rfl
        · constructor
          · intro h
            exact metaCICAuditSynthesisPacketDecode_encode_bhist h
          · intro x
            exact metaCICAuditSynthesisPacket_round_trip x

end BEDC.Derived.MetaCICAuditSynthesisPacketUp
