import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PhilosophyMapTargetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PhilosophyMapTargetUp : Type where
  | mk (R G K S A X H C P N : BHist) : PhilosophyMapTargetUp
  deriving DecidableEq

def philosophyMapTargetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: philosophyMapTargetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: philosophyMapTargetEncodeBHist h

def philosophyMapTargetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (philosophyMapTargetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (philosophyMapTargetDecodeBHist tail)

private theorem philosophyMapTargetDecode_encode_bhist :
    ∀ h : BHist, philosophyMapTargetDecodeBHist (philosophyMapTargetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def philosophyMapTargetToEventFlow : PhilosophyMapTargetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PhilosophyMapTargetUp.mk R G K S A X H C P N =>
      [[BMark.b0],
        philosophyMapTargetEncodeBHist R,
        [BMark.b1, BMark.b0],
        philosophyMapTargetEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b0],
        philosophyMapTargetEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        philosophyMapTargetEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        philosophyMapTargetEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        philosophyMapTargetEncodeBHist X,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        philosophyMapTargetEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        philosophyMapTargetEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        philosophyMapTargetEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        philosophyMapTargetEncodeBHist N]

private def philosophyMapTargetEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => philosophyMapTargetEventAtDefault index rest

def philosophyMapTargetFromEventFlow (ef : EventFlow) : Option PhilosophyMapTargetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PhilosophyMapTargetUp.mk
      (philosophyMapTargetDecodeBHist (philosophyMapTargetEventAtDefault 1 ef))
      (philosophyMapTargetDecodeBHist (philosophyMapTargetEventAtDefault 3 ef))
      (philosophyMapTargetDecodeBHist (philosophyMapTargetEventAtDefault 5 ef))
      (philosophyMapTargetDecodeBHist (philosophyMapTargetEventAtDefault 7 ef))
      (philosophyMapTargetDecodeBHist (philosophyMapTargetEventAtDefault 9 ef))
      (philosophyMapTargetDecodeBHist (philosophyMapTargetEventAtDefault 11 ef))
      (philosophyMapTargetDecodeBHist (philosophyMapTargetEventAtDefault 13 ef))
      (philosophyMapTargetDecodeBHist (philosophyMapTargetEventAtDefault 15 ef))
      (philosophyMapTargetDecodeBHist (philosophyMapTargetEventAtDefault 17 ef))
      (philosophyMapTargetDecodeBHist (philosophyMapTargetEventAtDefault 19 ef)))

private theorem philosophyMapTarget_round_trip :
    ∀ x : PhilosophyMapTargetUp,
      philosophyMapTargetFromEventFlow (philosophyMapTargetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R G K S A X H C P N =>
      change
        some
          (PhilosophyMapTargetUp.mk
            (philosophyMapTargetDecodeBHist (philosophyMapTargetEncodeBHist R))
            (philosophyMapTargetDecodeBHist (philosophyMapTargetEncodeBHist G))
            (philosophyMapTargetDecodeBHist (philosophyMapTargetEncodeBHist K))
            (philosophyMapTargetDecodeBHist (philosophyMapTargetEncodeBHist S))
            (philosophyMapTargetDecodeBHist (philosophyMapTargetEncodeBHist A))
            (philosophyMapTargetDecodeBHist (philosophyMapTargetEncodeBHist X))
            (philosophyMapTargetDecodeBHist (philosophyMapTargetEncodeBHist H))
            (philosophyMapTargetDecodeBHist (philosophyMapTargetEncodeBHist C))
            (philosophyMapTargetDecodeBHist (philosophyMapTargetEncodeBHist P))
            (philosophyMapTargetDecodeBHist (philosophyMapTargetEncodeBHist N))) =
          some (PhilosophyMapTargetUp.mk R G K S A X H C P N)
      rw [philosophyMapTargetDecode_encode_bhist R,
        philosophyMapTargetDecode_encode_bhist G,
        philosophyMapTargetDecode_encode_bhist K,
        philosophyMapTargetDecode_encode_bhist S,
        philosophyMapTargetDecode_encode_bhist A,
        philosophyMapTargetDecode_encode_bhist X,
        philosophyMapTargetDecode_encode_bhist H,
        philosophyMapTargetDecode_encode_bhist C,
        philosophyMapTargetDecode_encode_bhist P,
        philosophyMapTargetDecode_encode_bhist N]

private theorem philosophyMapTargetToEventFlow_injective {x y : PhilosophyMapTargetUp} :
    philosophyMapTargetToEventFlow x = philosophyMapTargetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      philosophyMapTargetFromEventFlow (philosophyMapTargetToEventFlow x) =
        philosophyMapTargetFromEventFlow (philosophyMapTargetToEventFlow y) :=
    congrArg philosophyMapTargetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (philosophyMapTarget_round_trip x).symm
      (Eq.trans hread (philosophyMapTarget_round_trip y)))

def philosophyMapTargetFields : PhilosophyMapTargetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PhilosophyMapTargetUp.mk R G K S A X H C P N => [R, G, K, S, A, X, H, C, P, N]

private theorem philosophyMapTarget_fields_faithful :
    ∀ x y : PhilosophyMapTargetUp, philosophyMapTargetFields x = philosophyMapTargetFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R1 G1 K1 S1 A1 X1 H1 C1 P1 N1 =>
      cases y with
      | mk R2 G2 K2 S2 A2 X2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance philosophyMapTargetBHistCarrier : BHistCarrier PhilosophyMapTargetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := philosophyMapTargetToEventFlow
  fromEventFlow := philosophyMapTargetFromEventFlow

instance philosophyMapTargetChapterTasteGate : ChapterTasteGate PhilosophyMapTargetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change philosophyMapTargetFromEventFlow (philosophyMapTargetToEventFlow x) = some x
    exact philosophyMapTarget_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (philosophyMapTargetToEventFlow_injective heq)

def taste_gate : ChapterTasteGate PhilosophyMapTargetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  philosophyMapTargetChapterTasteGate

instance philosophyMapTargetFieldFaithful : FieldFaithful PhilosophyMapTargetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := philosophyMapTargetFields
  field_faithful := philosophyMapTarget_fields_faithful

instance philosophyMapTargetNontrivial : Nontrivial PhilosophyMapTargetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PhilosophyMapTargetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PhilosophyMapTargetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem PhilosophyMapTargetTasteGate_single_carrier_alignment :
    (∀ h : BHist, philosophyMapTargetDecodeBHist (philosophyMapTargetEncodeBHist h) = h) ∧
      philosophyMapTargetEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
        (∀ x : PhilosophyMapTargetUp,
          philosophyMapTargetFromEventFlow (philosophyMapTargetToEventFlow x) = some x) ∧
          (∀ x y : PhilosophyMapTargetUp,
            philosophyMapTargetToEventFlow x = philosophyMapTargetToEventFlow y → x = y) ∧
            Nonempty (FieldFaithful PhilosophyMapTargetUp) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨philosophyMapTargetDecode_encode_bhist, rfl, philosophyMapTarget_round_trip,
      (fun _ _ heq => philosophyMapTargetToEventFlow_injective heq),
      ⟨philosophyMapTargetFieldFaithful⟩⟩

namespace TasteGate

theorem PhilosophyMapTargetTasteGate_single_carrier_alignment :
    (∀ h : BHist, philosophyMapTargetDecodeBHist (philosophyMapTargetEncodeBHist h) = h) ∧
      philosophyMapTargetEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
        (∀ x : PhilosophyMapTargetUp,
          philosophyMapTargetFromEventFlow (philosophyMapTargetToEventFlow x) = some x) ∧
          (∀ x y : PhilosophyMapTargetUp,
            philosophyMapTargetToEventFlow x = philosophyMapTargetToEventFlow y → x = y) ∧
            Nonempty (FieldFaithful PhilosophyMapTargetUp) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact BEDC.Derived.PhilosophyMapTargetUp.PhilosophyMapTargetTasteGate_single_carrier_alignment

end TasteGate

end BEDC.Derived.PhilosophyMapTargetUp
