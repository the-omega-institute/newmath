import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompletionTowerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompletionTowerUp : Type where
  | mk (M F S D I Q R H C P N : BHist) : CompletionTowerUp
  deriving DecidableEq

def completionTowerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completionTowerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completionTowerEncodeBHist h

def completionTowerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completionTowerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completionTowerDecodeBHist tail)

private theorem CompletionTowerTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, completionTowerDecodeBHist (completionTowerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def completionTowerFields : CompletionTowerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompletionTowerUp.mk M F S D I Q R H C P N => [M, F, S, D, I, Q, R, H, C, P, N]

def completionTowerToEventFlow : CompletionTowerUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (completionTowerFields x).map completionTowerEncodeBHist

private def completionTowerEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => completionTowerEventAtDefault index rest

def completionTowerFromEventFlow (ef : EventFlow) : Option CompletionTowerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompletionTowerUp.mk
      (completionTowerDecodeBHist (completionTowerEventAtDefault 0 ef))
      (completionTowerDecodeBHist (completionTowerEventAtDefault 1 ef))
      (completionTowerDecodeBHist (completionTowerEventAtDefault 2 ef))
      (completionTowerDecodeBHist (completionTowerEventAtDefault 3 ef))
      (completionTowerDecodeBHist (completionTowerEventAtDefault 4 ef))
      (completionTowerDecodeBHist (completionTowerEventAtDefault 5 ef))
      (completionTowerDecodeBHist (completionTowerEventAtDefault 6 ef))
      (completionTowerDecodeBHist (completionTowerEventAtDefault 7 ef))
      (completionTowerDecodeBHist (completionTowerEventAtDefault 8 ef))
      (completionTowerDecodeBHist (completionTowerEventAtDefault 9 ef))
      (completionTowerDecodeBHist (completionTowerEventAtDefault 10 ef)))

private theorem CompletionTowerTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompletionTowerUp,
      completionTowerFromEventFlow (completionTowerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M F S D I Q R H C P N =>
      change
        some
          (CompletionTowerUp.mk
            (completionTowerDecodeBHist (completionTowerEncodeBHist M))
            (completionTowerDecodeBHist (completionTowerEncodeBHist F))
            (completionTowerDecodeBHist (completionTowerEncodeBHist S))
            (completionTowerDecodeBHist (completionTowerEncodeBHist D))
            (completionTowerDecodeBHist (completionTowerEncodeBHist I))
            (completionTowerDecodeBHist (completionTowerEncodeBHist Q))
            (completionTowerDecodeBHist (completionTowerEncodeBHist R))
            (completionTowerDecodeBHist (completionTowerEncodeBHist H))
            (completionTowerDecodeBHist (completionTowerEncodeBHist C))
            (completionTowerDecodeBHist (completionTowerEncodeBHist P))
            (completionTowerDecodeBHist (completionTowerEncodeBHist N))) =
          some (CompletionTowerUp.mk M F S D I Q R H C P N)
      rw [CompletionTowerTasteGate_single_carrier_alignment_decode M,
        CompletionTowerTasteGate_single_carrier_alignment_decode F,
        CompletionTowerTasteGate_single_carrier_alignment_decode S,
        CompletionTowerTasteGate_single_carrier_alignment_decode D,
        CompletionTowerTasteGate_single_carrier_alignment_decode I,
        CompletionTowerTasteGate_single_carrier_alignment_decode Q,
        CompletionTowerTasteGate_single_carrier_alignment_decode R,
        CompletionTowerTasteGate_single_carrier_alignment_decode H,
        CompletionTowerTasteGate_single_carrier_alignment_decode C,
        CompletionTowerTasteGate_single_carrier_alignment_decode P,
        CompletionTowerTasteGate_single_carrier_alignment_decode N]

private theorem CompletionTowerTasteGate_single_carrier_alignment_injective
    {x y : CompletionTowerUp} :
    completionTowerToEventFlow x = completionTowerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completionTowerFromEventFlow (completionTowerToEventFlow x) =
        completionTowerFromEventFlow (completionTowerToEventFlow y) :=
    congrArg completionTowerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompletionTowerTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CompletionTowerTasteGate_single_carrier_alignment_round_trip y)))

private theorem CompletionTowerTasteGate_single_carrier_alignment_fields :
    ∀ x y : CompletionTowerUp, completionTowerFields x = completionTowerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 F1 S1 D1 I1 Q1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 F2 S2 D2 I2 Q2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance completionTowerBHistCarrier : BHistCarrier CompletionTowerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completionTowerToEventFlow
  fromEventFlow := completionTowerFromEventFlow

instance completionTowerChapterTasteGate : ChapterTasteGate CompletionTowerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change completionTowerFromEventFlow (completionTowerToEventFlow x) = some x
    exact CompletionTowerTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompletionTowerTasteGate_single_carrier_alignment_injective heq)

instance completionTowerFieldFaithful : FieldFaithful CompletionTowerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := completionTowerFields
  field_faithful := CompletionTowerTasteGate_single_carrier_alignment_fields

instance completionTowerNontrivial : Nontrivial CompletionTowerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompletionTowerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompletionTowerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CompletionTowerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  completionTowerChapterTasteGate

theorem CompletionTowerTasteGate_single_carrier_alignment :
    (∀ h : BHist, completionTowerDecodeBHist (completionTowerEncodeBHist h) = h) ∧
      (∀ x : CompletionTowerUp,
        completionTowerFromEventFlow (completionTowerToEventFlow x) = some x) ∧
        (∀ x y : CompletionTowerUp,
          completionTowerToEventFlow x = completionTowerToEventFlow y → x = y) ∧
          completionTowerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨CompletionTowerTasteGate_single_carrier_alignment_decode,
      CompletionTowerTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => CompletionTowerTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.CompletionTowerUp
