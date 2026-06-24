import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HyperbolicPhaseObserverExpansionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HyperbolicPhaseObserverExpansionUp : Type where
  | mk (F D S B G P H C N : BHist) : HyperbolicPhaseObserverExpansionUp
  deriving DecidableEq

def hyperbolicPhaseObserverExpansionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hyperbolicPhaseObserverExpansionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hyperbolicPhaseObserverExpansionEncodeBHist h

def hyperbolicPhaseObserverExpansionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hyperbolicPhaseObserverExpansionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hyperbolicPhaseObserverExpansionDecodeBHist tail)

private theorem HyperbolicPhaseObserverExpansionTasteGate_decode_encode :
    ∀ h : BHist,
      hyperbolicPhaseObserverExpansionDecodeBHist
          (hyperbolicPhaseObserverExpansionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hyperbolicPhaseObserverExpansionFields :
    HyperbolicPhaseObserverExpansionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HyperbolicPhaseObserverExpansionUp.mk F D S B G P H C N =>
      [F, D, S, B, G, P, H, C, N]

def hyperbolicPhaseObserverExpansionToEventFlow :
    HyperbolicPhaseObserverExpansionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (hyperbolicPhaseObserverExpansionFields x).map
        hyperbolicPhaseObserverExpansionEncodeBHist

private def hyperbolicPhaseObserverExpansionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      hyperbolicPhaseObserverExpansionEventAt index rest

def hyperbolicPhaseObserverExpansionFromEventFlow
    (ef : EventFlow) : Option HyperbolicPhaseObserverExpansionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HyperbolicPhaseObserverExpansionUp.mk
      (hyperbolicPhaseObserverExpansionDecodeBHist
        (hyperbolicPhaseObserverExpansionEventAt 0 ef))
      (hyperbolicPhaseObserverExpansionDecodeBHist
        (hyperbolicPhaseObserverExpansionEventAt 1 ef))
      (hyperbolicPhaseObserverExpansionDecodeBHist
        (hyperbolicPhaseObserverExpansionEventAt 2 ef))
      (hyperbolicPhaseObserverExpansionDecodeBHist
        (hyperbolicPhaseObserverExpansionEventAt 3 ef))
      (hyperbolicPhaseObserverExpansionDecodeBHist
        (hyperbolicPhaseObserverExpansionEventAt 4 ef))
      (hyperbolicPhaseObserverExpansionDecodeBHist
        (hyperbolicPhaseObserverExpansionEventAt 5 ef))
      (hyperbolicPhaseObserverExpansionDecodeBHist
        (hyperbolicPhaseObserverExpansionEventAt 6 ef))
      (hyperbolicPhaseObserverExpansionDecodeBHist
        (hyperbolicPhaseObserverExpansionEventAt 7 ef))
      (hyperbolicPhaseObserverExpansionDecodeBHist
        (hyperbolicPhaseObserverExpansionEventAt 8 ef)))

private theorem HyperbolicPhaseObserverExpansionTasteGate_round_trip :
    ∀ x : HyperbolicPhaseObserverExpansionUp,
      hyperbolicPhaseObserverExpansionFromEventFlow
          (hyperbolicPhaseObserverExpansionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F D S B G P H C N =>
      change
        some
          (HyperbolicPhaseObserverExpansionUp.mk
            (hyperbolicPhaseObserverExpansionDecodeBHist
              (hyperbolicPhaseObserverExpansionEncodeBHist F))
            (hyperbolicPhaseObserverExpansionDecodeBHist
              (hyperbolicPhaseObserverExpansionEncodeBHist D))
            (hyperbolicPhaseObserverExpansionDecodeBHist
              (hyperbolicPhaseObserverExpansionEncodeBHist S))
            (hyperbolicPhaseObserverExpansionDecodeBHist
              (hyperbolicPhaseObserverExpansionEncodeBHist B))
            (hyperbolicPhaseObserverExpansionDecodeBHist
              (hyperbolicPhaseObserverExpansionEncodeBHist G))
            (hyperbolicPhaseObserverExpansionDecodeBHist
              (hyperbolicPhaseObserverExpansionEncodeBHist P))
            (hyperbolicPhaseObserverExpansionDecodeBHist
              (hyperbolicPhaseObserverExpansionEncodeBHist H))
            (hyperbolicPhaseObserverExpansionDecodeBHist
              (hyperbolicPhaseObserverExpansionEncodeBHist C))
            (hyperbolicPhaseObserverExpansionDecodeBHist
              (hyperbolicPhaseObserverExpansionEncodeBHist N))) =
          some (HyperbolicPhaseObserverExpansionUp.mk F D S B G P H C N)
      rw [HyperbolicPhaseObserverExpansionTasteGate_decode_encode F,
        HyperbolicPhaseObserverExpansionTasteGate_decode_encode D,
        HyperbolicPhaseObserverExpansionTasteGate_decode_encode S,
        HyperbolicPhaseObserverExpansionTasteGate_decode_encode B,
        HyperbolicPhaseObserverExpansionTasteGate_decode_encode G,
        HyperbolicPhaseObserverExpansionTasteGate_decode_encode P,
        HyperbolicPhaseObserverExpansionTasteGate_decode_encode H,
        HyperbolicPhaseObserverExpansionTasteGate_decode_encode C,
        HyperbolicPhaseObserverExpansionTasteGate_decode_encode N]

private theorem HyperbolicPhaseObserverExpansionTasteGate_toEventFlow_injective
    {x y : HyperbolicPhaseObserverExpansionUp} :
    hyperbolicPhaseObserverExpansionToEventFlow x =
        hyperbolicPhaseObserverExpansionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hyperbolicPhaseObserverExpansionFromEventFlow
          (hyperbolicPhaseObserverExpansionToEventFlow x) =
        hyperbolicPhaseObserverExpansionFromEventFlow
          (hyperbolicPhaseObserverExpansionToEventFlow y) :=
    congrArg hyperbolicPhaseObserverExpansionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HyperbolicPhaseObserverExpansionTasteGate_round_trip x).symm
      (Eq.trans hread (HyperbolicPhaseObserverExpansionTasteGate_round_trip y)))

private theorem HyperbolicPhaseObserverExpansionTasteGate_fields_faithful :
    ∀ x y : HyperbolicPhaseObserverExpansionUp,
      hyperbolicPhaseObserverExpansionFields x =
          hyperbolicPhaseObserverExpansionFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 D1 S1 B1 G1 P1 H1 C1 N1 =>
      cases y with
      | mk F2 D2 S2 B2 G2 P2 H2 C2 N2 =>
          cases hfields
          rfl

instance hyperbolicPhaseObserverExpansionBHistCarrier :
    BHistCarrier HyperbolicPhaseObserverExpansionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hyperbolicPhaseObserverExpansionToEventFlow
  fromEventFlow := hyperbolicPhaseObserverExpansionFromEventFlow

instance hyperbolicPhaseObserverExpansionChapterTasteGate :
    ChapterTasteGate HyperbolicPhaseObserverExpansionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hyperbolicPhaseObserverExpansionFromEventFlow
          (hyperbolicPhaseObserverExpansionToEventFlow x) =
        some x
    exact HyperbolicPhaseObserverExpansionTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HyperbolicPhaseObserverExpansionTasteGate_toEventFlow_injective heq)

instance hyperbolicPhaseObserverExpansionFieldFaithful :
    FieldFaithful HyperbolicPhaseObserverExpansionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hyperbolicPhaseObserverExpansionFields
  field_faithful := HyperbolicPhaseObserverExpansionTasteGate_fields_faithful

instance hyperbolicPhaseObserverExpansionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial HyperbolicPhaseObserverExpansionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HyperbolicPhaseObserverExpansionUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      HyperbolicPhaseObserverExpansionUp.mk (BHist.e1 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HyperbolicPhaseObserverExpansionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hyperbolicPhaseObserverExpansionChapterTasteGate

theorem HyperbolicPhaseObserverExpansionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      hyperbolicPhaseObserverExpansionDecodeBHist
          (hyperbolicPhaseObserverExpansionEncodeBHist h) =
        h) ∧
      (∀ x : HyperbolicPhaseObserverExpansionUp,
        hyperbolicPhaseObserverExpansionFromEventFlow
            (hyperbolicPhaseObserverExpansionToEventFlow x) =
          some x) ∧
        (∀ x y : HyperbolicPhaseObserverExpansionUp,
          hyperbolicPhaseObserverExpansionToEventFlow x =
              hyperbolicPhaseObserverExpansionToEventFlow y →
            x = y) ∧
          hyperbolicPhaseObserverExpansionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨HyperbolicPhaseObserverExpansionTasteGate_decode_encode,
      HyperbolicPhaseObserverExpansionTasteGate_round_trip,
      (fun _ _ heq => HyperbolicPhaseObserverExpansionTasteGate_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.HyperbolicPhaseObserverExpansionUp
