import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KanExtensionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KanExtensionUp : Type where
  | mk (C D E J F L eta U V H R P N : BHist) : KanExtensionUp
  deriving DecidableEq

def kanExtensionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kanExtensionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kanExtensionEncodeBHist h

def kanExtensionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kanExtensionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kanExtensionDecodeBHist tail)

private theorem kanExtensionDecode_encode :
    ∀ h : BHist, kanExtensionDecodeBHist (kanExtensionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kanExtensionFields : KanExtensionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KanExtensionUp.mk C D E J F L eta U V H R P N =>
      [C, D, E, J, F, L, eta, U, V, H, R, P, N]

def kanExtensionToEventFlow : KanExtensionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => [BMark.b1, BMark.b0, BMark.b1, BMark.b1] ::
      (kanExtensionFields x).map kanExtensionEncodeBHist

private def kanExtensionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => kanExtensionEventAtDefault index rest

def kanExtensionFromEventFlow : EventFlow → Option KanExtensionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (KanExtensionUp.mk
        (kanExtensionDecodeBHist (kanExtensionEventAtDefault 1 ef))
        (kanExtensionDecodeBHist (kanExtensionEventAtDefault 2 ef))
        (kanExtensionDecodeBHist (kanExtensionEventAtDefault 3 ef))
        (kanExtensionDecodeBHist (kanExtensionEventAtDefault 4 ef))
        (kanExtensionDecodeBHist (kanExtensionEventAtDefault 5 ef))
        (kanExtensionDecodeBHist (kanExtensionEventAtDefault 6 ef))
        (kanExtensionDecodeBHist (kanExtensionEventAtDefault 7 ef))
        (kanExtensionDecodeBHist (kanExtensionEventAtDefault 8 ef))
        (kanExtensionDecodeBHist (kanExtensionEventAtDefault 9 ef))
        (kanExtensionDecodeBHist (kanExtensionEventAtDefault 10 ef))
        (kanExtensionDecodeBHist (kanExtensionEventAtDefault 11 ef))
        (kanExtensionDecodeBHist (kanExtensionEventAtDefault 12 ef))
        (kanExtensionDecodeBHist (kanExtensionEventAtDefault 13 ef)))

private theorem kanExtension_round_trip :
    ∀ x : KanExtensionUp,
      kanExtensionFromEventFlow (kanExtensionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk C D E J F L eta U V H R P N =>
      change
        some
          (KanExtensionUp.mk
            (kanExtensionDecodeBHist (kanExtensionEncodeBHist C))
            (kanExtensionDecodeBHist (kanExtensionEncodeBHist D))
            (kanExtensionDecodeBHist (kanExtensionEncodeBHist E))
            (kanExtensionDecodeBHist (kanExtensionEncodeBHist J))
            (kanExtensionDecodeBHist (kanExtensionEncodeBHist F))
            (kanExtensionDecodeBHist (kanExtensionEncodeBHist L))
            (kanExtensionDecodeBHist (kanExtensionEncodeBHist eta))
            (kanExtensionDecodeBHist (kanExtensionEncodeBHist U))
            (kanExtensionDecodeBHist (kanExtensionEncodeBHist V))
            (kanExtensionDecodeBHist (kanExtensionEncodeBHist H))
            (kanExtensionDecodeBHist (kanExtensionEncodeBHist R))
            (kanExtensionDecodeBHist (kanExtensionEncodeBHist P))
            (kanExtensionDecodeBHist (kanExtensionEncodeBHist N))) =
          some (KanExtensionUp.mk C D E J F L eta U V H R P N)
      rw [kanExtensionDecode_encode C,
        kanExtensionDecode_encode D,
        kanExtensionDecode_encode E,
        kanExtensionDecode_encode J,
        kanExtensionDecode_encode F,
        kanExtensionDecode_encode L,
        kanExtensionDecode_encode eta,
        kanExtensionDecode_encode U,
        kanExtensionDecode_encode V,
        kanExtensionDecode_encode H,
        kanExtensionDecode_encode R,
        kanExtensionDecode_encode P,
        kanExtensionDecode_encode N]

private theorem kanExtensionToEventFlow_injective {x y : KanExtensionUp} :
    kanExtensionToEventFlow x = kanExtensionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kanExtensionFromEventFlow (kanExtensionToEventFlow x) =
        kanExtensionFromEventFlow (kanExtensionToEventFlow y) :=
    congrArg kanExtensionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (kanExtension_round_trip x).symm
      (Eq.trans hread (kanExtension_round_trip y)))

private theorem kanExtension_field_faithful :
    ∀ x y : KanExtensionUp, kanExtensionFields x = kanExtensionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk C1 D1 E1 J1 F1 L1 eta1 U1 V1 H1 R1 P1 N1 =>
      cases y with
      | mk C2 D2 E2 J2 F2 L2 eta2 U2 V2 H2 R2 P2 N2 =>
          cases hfields
          rfl

instance kanExtensionBHistCarrier : BHistCarrier KanExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kanExtensionToEventFlow
  fromEventFlow := kanExtensionFromEventFlow

instance kanExtensionChapterTasteGate : ChapterTasteGate KanExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kanExtensionFromEventFlow (kanExtensionToEventFlow x) = some x
    exact kanExtension_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (kanExtensionToEventFlow_injective heq)

instance kanExtensionFieldFaithful : FieldFaithful KanExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := kanExtensionFields
  field_faithful := kanExtension_field_faithful

instance kanExtensionNontrivial : Nontrivial KanExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨KanExtensionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      KanExtensionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        injection h with hC
        cases hC⟩

def taste_gate : ChapterTasteGate KanExtensionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  kanExtensionChapterTasteGate

def taste_gate_witness : FieldFaithful KanExtensionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  kanExtensionFieldFaithful

theorem KanExtensionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate KanExtensionUp) ∧
      Nonempty (FieldFaithful KanExtensionUp) ∧
        Nonempty (Nontrivial KanExtensionUp) ∧
          (∀ h : BHist, kanExtensionDecodeBHist (kanExtensionEncodeBHist h) = h) ∧
            (∀ x : KanExtensionUp,
              kanExtensionFromEventFlow (kanExtensionToEventFlow x) = some x) ∧
              (∀ x y : KanExtensionUp,
                kanExtensionToEventFlow x = kanExtensionToEventFlow y → x = y) ∧
                kanExtensionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨Nonempty.intro kanExtensionChapterTasteGate,
      Nonempty.intro kanExtensionFieldFaithful,
      Nonempty.intro kanExtensionNontrivial,
      kanExtensionDecode_encode,
      kanExtension_round_trip,
      fun _ _ heq => kanExtensionToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.KanExtensionUp.TasteGate
