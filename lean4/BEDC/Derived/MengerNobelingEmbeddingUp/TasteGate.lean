import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MengerNobelingEmbeddingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MengerNobelingEmbeddingUp : Type where
  | mk (M K Q F R H C P N : BHist) : MengerNobelingEmbeddingUp
  deriving DecidableEq

def mengerNobelingEmbeddingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: mengerNobelingEmbeddingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: mengerNobelingEmbeddingEncodeBHist h

def mengerNobelingEmbeddingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (mengerNobelingEmbeddingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (mengerNobelingEmbeddingDecodeBHist tail)

private theorem MengerNobelingEmbeddingTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      mengerNobelingEmbeddingDecodeBHist (mengerNobelingEmbeddingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def mengerNobelingEmbeddingFields : MengerNobelingEmbeddingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MengerNobelingEmbeddingUp.mk M K Q F R H C P N => [M, K, Q, F, R, H, C, P, N]

def mengerNobelingEmbeddingToEventFlow : MengerNobelingEmbeddingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (mengerNobelingEmbeddingFields x).map mengerNobelingEmbeddingEncodeBHist

private def mengerNobelingEmbeddingEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => mengerNobelingEmbeddingEventAtDefault index rest

def mengerNobelingEmbeddingFromEventFlow :
    EventFlow → Option MengerNobelingEmbeddingUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (MengerNobelingEmbeddingUp.mk
          (mengerNobelingEmbeddingDecodeBHist (mengerNobelingEmbeddingEventAtDefault 0 ef))
          (mengerNobelingEmbeddingDecodeBHist (mengerNobelingEmbeddingEventAtDefault 1 ef))
          (mengerNobelingEmbeddingDecodeBHist (mengerNobelingEmbeddingEventAtDefault 2 ef))
          (mengerNobelingEmbeddingDecodeBHist (mengerNobelingEmbeddingEventAtDefault 3 ef))
          (mengerNobelingEmbeddingDecodeBHist (mengerNobelingEmbeddingEventAtDefault 4 ef))
          (mengerNobelingEmbeddingDecodeBHist (mengerNobelingEmbeddingEventAtDefault 5 ef))
          (mengerNobelingEmbeddingDecodeBHist (mengerNobelingEmbeddingEventAtDefault 6 ef))
          (mengerNobelingEmbeddingDecodeBHist (mengerNobelingEmbeddingEventAtDefault 7 ef))
          (mengerNobelingEmbeddingDecodeBHist (mengerNobelingEmbeddingEventAtDefault 8 ef)))

private theorem MengerNobelingEmbeddingTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MengerNobelingEmbeddingUp,
      mengerNobelingEmbeddingFromEventFlow (mengerNobelingEmbeddingToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M K Q F R H C P N =>
      change
        some
          (MengerNobelingEmbeddingUp.mk
            (mengerNobelingEmbeddingDecodeBHist (mengerNobelingEmbeddingEncodeBHist M))
            (mengerNobelingEmbeddingDecodeBHist (mengerNobelingEmbeddingEncodeBHist K))
            (mengerNobelingEmbeddingDecodeBHist (mengerNobelingEmbeddingEncodeBHist Q))
            (mengerNobelingEmbeddingDecodeBHist (mengerNobelingEmbeddingEncodeBHist F))
            (mengerNobelingEmbeddingDecodeBHist (mengerNobelingEmbeddingEncodeBHist R))
            (mengerNobelingEmbeddingDecodeBHist (mengerNobelingEmbeddingEncodeBHist H))
            (mengerNobelingEmbeddingDecodeBHist (mengerNobelingEmbeddingEncodeBHist C))
            (mengerNobelingEmbeddingDecodeBHist (mengerNobelingEmbeddingEncodeBHist P))
            (mengerNobelingEmbeddingDecodeBHist (mengerNobelingEmbeddingEncodeBHist N))) =
          some (MengerNobelingEmbeddingUp.mk M K Q F R H C P N)
      rw [MengerNobelingEmbeddingTasteGate_single_carrier_alignment_decode M,
        MengerNobelingEmbeddingTasteGate_single_carrier_alignment_decode K,
        MengerNobelingEmbeddingTasteGate_single_carrier_alignment_decode Q,
        MengerNobelingEmbeddingTasteGate_single_carrier_alignment_decode F,
        MengerNobelingEmbeddingTasteGate_single_carrier_alignment_decode R,
        MengerNobelingEmbeddingTasteGate_single_carrier_alignment_decode H,
        MengerNobelingEmbeddingTasteGate_single_carrier_alignment_decode C,
        MengerNobelingEmbeddingTasteGate_single_carrier_alignment_decode P,
        MengerNobelingEmbeddingTasteGate_single_carrier_alignment_decode N]

private theorem MengerNobelingEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MengerNobelingEmbeddingUp} :
    mengerNobelingEmbeddingToEventFlow x = mengerNobelingEmbeddingToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      mengerNobelingEmbeddingFromEventFlow (mengerNobelingEmbeddingToEventFlow x) =
        mengerNobelingEmbeddingFromEventFlow (mengerNobelingEmbeddingToEventFlow y) :=
    congrArg mengerNobelingEmbeddingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MengerNobelingEmbeddingTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MengerNobelingEmbeddingTasteGate_single_carrier_alignment_round_trip y)))

private theorem MengerNobelingEmbeddingTasteGate_single_carrier_alignment_fields :
    ∀ x y : MengerNobelingEmbeddingUp,
      mengerNobelingEmbeddingFields x = mengerNobelingEmbeddingFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 K1 Q1 F1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 K2 Q2 F2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance mengerNobelingEmbeddingBHistCarrier :
    BHistCarrier MengerNobelingEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := mengerNobelingEmbeddingToEventFlow
  fromEventFlow := mengerNobelingEmbeddingFromEventFlow

instance mengerNobelingEmbeddingChapterTasteGate :
    ChapterTasteGate MengerNobelingEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change mengerNobelingEmbeddingFromEventFlow (mengerNobelingEmbeddingToEventFlow x) =
      some x
    exact MengerNobelingEmbeddingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MengerNobelingEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance mengerNobelingEmbeddingFieldFaithful :
    FieldFaithful MengerNobelingEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := mengerNobelingEmbeddingFields
  field_faithful := MengerNobelingEmbeddingTasteGate_single_carrier_alignment_fields

instance mengerNobelingEmbeddingNontrivial :
    Nontrivial MengerNobelingEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MengerNobelingEmbeddingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MengerNobelingEmbeddingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MengerNobelingEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  mengerNobelingEmbeddingChapterTasteGate

theorem MengerNobelingEmbeddingTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      mengerNobelingEmbeddingDecodeBHist (mengerNobelingEmbeddingEncodeBHist h) =
        h) ∧
      (∀ x : MengerNobelingEmbeddingUp,
        mengerNobelingEmbeddingFromEventFlow (mengerNobelingEmbeddingToEventFlow x) =
          some x) ∧
        (∀ x y : MengerNobelingEmbeddingUp,
          mengerNobelingEmbeddingToEventFlow x = mengerNobelingEmbeddingToEventFlow y →
            x = y) ∧
          mengerNobelingEmbeddingEncodeBHist BHist.Empty = ([] : RawEvent) ∧
            mengerNobelingEmbeddingEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨MengerNobelingEmbeddingTasteGate_single_carrier_alignment_decode,
      MengerNobelingEmbeddingTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        MengerNobelingEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl,
      rfl⟩

end BEDC.Derived.MengerNobelingEmbeddingUp
