import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompletionAdjointUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompletionAdjointUp : Type where
  | mk (R F U V S Q D E H C P N : BHist) : CompletionAdjointUp
  deriving DecidableEq

def completionAdjointEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completionAdjointEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completionAdjointEncodeBHist h

def completionAdjointDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completionAdjointDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completionAdjointDecodeBHist tail)

private theorem CompletionAdjointTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, completionAdjointDecodeBHist (completionAdjointEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def completionAdjointFields : CompletionAdjointUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompletionAdjointUp.mk R F U V S Q D E H C P N => [R, F, U, V, S, Q, D, E, H, C, P, N]

def completionAdjointToEventFlow : CompletionAdjointUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (completionAdjointFields x).map completionAdjointEncodeBHist

private def completionAdjointEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => completionAdjointEventAtDefault index rest

def completionAdjointFromEventFlow (ef : EventFlow) : Option CompletionAdjointUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompletionAdjointUp.mk
      (completionAdjointDecodeBHist (completionAdjointEventAtDefault 0 ef))
      (completionAdjointDecodeBHist (completionAdjointEventAtDefault 1 ef))
      (completionAdjointDecodeBHist (completionAdjointEventAtDefault 2 ef))
      (completionAdjointDecodeBHist (completionAdjointEventAtDefault 3 ef))
      (completionAdjointDecodeBHist (completionAdjointEventAtDefault 4 ef))
      (completionAdjointDecodeBHist (completionAdjointEventAtDefault 5 ef))
      (completionAdjointDecodeBHist (completionAdjointEventAtDefault 6 ef))
      (completionAdjointDecodeBHist (completionAdjointEventAtDefault 7 ef))
      (completionAdjointDecodeBHist (completionAdjointEventAtDefault 8 ef))
      (completionAdjointDecodeBHist (completionAdjointEventAtDefault 9 ef))
      (completionAdjointDecodeBHist (completionAdjointEventAtDefault 10 ef))
      (completionAdjointDecodeBHist (completionAdjointEventAtDefault 11 ef)))

private theorem CompletionAdjointTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompletionAdjointUp,
      completionAdjointFromEventFlow (completionAdjointToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk R F U V S Q D E H C P N =>
      change
        some
          (CompletionAdjointUp.mk
            (completionAdjointDecodeBHist (completionAdjointEncodeBHist R))
            (completionAdjointDecodeBHist (completionAdjointEncodeBHist F))
            (completionAdjointDecodeBHist (completionAdjointEncodeBHist U))
            (completionAdjointDecodeBHist (completionAdjointEncodeBHist V))
            (completionAdjointDecodeBHist (completionAdjointEncodeBHist S))
            (completionAdjointDecodeBHist (completionAdjointEncodeBHist Q))
            (completionAdjointDecodeBHist (completionAdjointEncodeBHist D))
            (completionAdjointDecodeBHist (completionAdjointEncodeBHist E))
            (completionAdjointDecodeBHist (completionAdjointEncodeBHist H))
            (completionAdjointDecodeBHist (completionAdjointEncodeBHist C))
            (completionAdjointDecodeBHist (completionAdjointEncodeBHist P))
            (completionAdjointDecodeBHist (completionAdjointEncodeBHist N))) =
          some (CompletionAdjointUp.mk R F U V S Q D E H C P N)
      rw [CompletionAdjointTasteGate_single_carrier_alignment_decode R,
        CompletionAdjointTasteGate_single_carrier_alignment_decode F,
        CompletionAdjointTasteGate_single_carrier_alignment_decode U,
        CompletionAdjointTasteGate_single_carrier_alignment_decode V,
        CompletionAdjointTasteGate_single_carrier_alignment_decode S,
        CompletionAdjointTasteGate_single_carrier_alignment_decode Q,
        CompletionAdjointTasteGate_single_carrier_alignment_decode D,
        CompletionAdjointTasteGate_single_carrier_alignment_decode E,
        CompletionAdjointTasteGate_single_carrier_alignment_decode H,
        CompletionAdjointTasteGate_single_carrier_alignment_decode C,
        CompletionAdjointTasteGate_single_carrier_alignment_decode P,
        CompletionAdjointTasteGate_single_carrier_alignment_decode N]

private theorem CompletionAdjointTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompletionAdjointUp} :
    completionAdjointToEventFlow x = completionAdjointToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completionAdjointFromEventFlow (completionAdjointToEventFlow x) =
        completionAdjointFromEventFlow (completionAdjointToEventFlow y) :=
    congrArg completionAdjointFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CompletionAdjointTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CompletionAdjointTasteGate_single_carrier_alignment_round_trip y)))

private theorem CompletionAdjointTasteGate_single_carrier_alignment_fields :
    ∀ x y : CompletionAdjointUp, completionAdjointFields x = completionAdjointFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R1 F1 U1 V1 S1 Q1 D1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk R2 F2 U2 V2 S2 Q2 D2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance completionAdjointBHistCarrier : BHistCarrier CompletionAdjointUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completionAdjointToEventFlow
  fromEventFlow := completionAdjointFromEventFlow

instance completionAdjointChapterTasteGate : ChapterTasteGate CompletionAdjointUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change completionAdjointFromEventFlow (completionAdjointToEventFlow x) = some x
    exact CompletionAdjointTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompletionAdjointTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance completionAdjointFieldFaithful : FieldFaithful CompletionAdjointUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := completionAdjointFields
  field_faithful := CompletionAdjointTasteGate_single_carrier_alignment_fields

instance completionAdjointNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CompletionAdjointUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompletionAdjointUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompletionAdjointUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CompletionAdjointUp :=
  -- BEDC touchpoint anchor: BHist BMark
  completionAdjointChapterTasteGate

theorem CompletionAdjointTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CompletionAdjointUp) ∧
      Nonempty (FieldFaithful CompletionAdjointUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CompletionAdjointUp) ∧
          (∀ h : BHist, completionAdjointDecodeBHist (completionAdjointEncodeBHist h) = h) ∧
            (∀ x : CompletionAdjointUp,
              completionAdjointFromEventFlow (completionAdjointToEventFlow x) = some x) ∧
              (∀ x y : CompletionAdjointUp,
                completionAdjointToEventFlow x = completionAdjointToEventFlow y -> x = y) ∧
                completionAdjointEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨completionAdjointChapterTasteGate⟩,
      ⟨completionAdjointFieldFaithful⟩,
      ⟨completionAdjointNontrivial⟩,
      CompletionAdjointTasteGate_single_carrier_alignment_decode,
      CompletionAdjointTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CompletionAdjointTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompletionAdjointUp
