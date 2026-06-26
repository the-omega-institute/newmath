import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConstantCauchyNameUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConstantCauchyNameUp : Type where
  | mk (D W Q R E H C P N : BHist) : ConstantCauchyNameUp
  deriving DecidableEq

def constantCauchyNameEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: constantCauchyNameEncodeBHist h
  | BHist.e1 h => BMark.b1 :: constantCauchyNameEncodeBHist h

def constantCauchyNameDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (constantCauchyNameDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (constantCauchyNameDecodeBHist tail)

private theorem ConstantCauchyNameTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, constantCauchyNameDecodeBHist (constantCauchyNameEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def constantCauchyNameToEventFlow : ConstantCauchyNameUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ConstantCauchyNameUp.mk D W Q R E H C P N =>
      [[BMark.b0],
        constantCauchyNameEncodeBHist D,
        [BMark.b1, BMark.b0],
        constantCauchyNameEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b0],
        constantCauchyNameEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        constantCauchyNameEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        constantCauchyNameEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        constantCauchyNameEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        constantCauchyNameEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        constantCauchyNameEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        constantCauchyNameEncodeBHist N]

private def constantCauchyNameEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => constantCauchyNameEventAtDefault index rest

def constantCauchyNameFromEventFlow (ef : EventFlow) : Option ConstantCauchyNameUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ConstantCauchyNameUp.mk
      (constantCauchyNameDecodeBHist (constantCauchyNameEventAtDefault 1 ef))
      (constantCauchyNameDecodeBHist (constantCauchyNameEventAtDefault 3 ef))
      (constantCauchyNameDecodeBHist (constantCauchyNameEventAtDefault 5 ef))
      (constantCauchyNameDecodeBHist (constantCauchyNameEventAtDefault 7 ef))
      (constantCauchyNameDecodeBHist (constantCauchyNameEventAtDefault 9 ef))
      (constantCauchyNameDecodeBHist (constantCauchyNameEventAtDefault 11 ef))
      (constantCauchyNameDecodeBHist (constantCauchyNameEventAtDefault 13 ef))
      (constantCauchyNameDecodeBHist (constantCauchyNameEventAtDefault 15 ef))
      (constantCauchyNameDecodeBHist (constantCauchyNameEventAtDefault 17 ef)))

private theorem ConstantCauchyNameTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ConstantCauchyNameUp,
      constantCauchyNameFromEventFlow (constantCauchyNameToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D W Q R E H C P N =>
      change
        some
          (ConstantCauchyNameUp.mk
            (constantCauchyNameDecodeBHist (constantCauchyNameEncodeBHist D))
            (constantCauchyNameDecodeBHist (constantCauchyNameEncodeBHist W))
            (constantCauchyNameDecodeBHist (constantCauchyNameEncodeBHist Q))
            (constantCauchyNameDecodeBHist (constantCauchyNameEncodeBHist R))
            (constantCauchyNameDecodeBHist (constantCauchyNameEncodeBHist E))
            (constantCauchyNameDecodeBHist (constantCauchyNameEncodeBHist H))
            (constantCauchyNameDecodeBHist (constantCauchyNameEncodeBHist C))
            (constantCauchyNameDecodeBHist (constantCauchyNameEncodeBHist P))
            (constantCauchyNameDecodeBHist (constantCauchyNameEncodeBHist N))) =
          some (ConstantCauchyNameUp.mk D W Q R E H C P N)
      rw [ConstantCauchyNameTasteGate_single_carrier_alignment_decode D,
        ConstantCauchyNameTasteGate_single_carrier_alignment_decode W,
        ConstantCauchyNameTasteGate_single_carrier_alignment_decode Q,
        ConstantCauchyNameTasteGate_single_carrier_alignment_decode R,
        ConstantCauchyNameTasteGate_single_carrier_alignment_decode E,
        ConstantCauchyNameTasteGate_single_carrier_alignment_decode H,
        ConstantCauchyNameTasteGate_single_carrier_alignment_decode C,
        ConstantCauchyNameTasteGate_single_carrier_alignment_decode P,
        ConstantCauchyNameTasteGate_single_carrier_alignment_decode N]

private theorem ConstantCauchyNameTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ConstantCauchyNameUp} :
    constantCauchyNameToEventFlow x = constantCauchyNameToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      constantCauchyNameFromEventFlow (constantCauchyNameToEventFlow x) =
        constantCauchyNameFromEventFlow (constantCauchyNameToEventFlow y) :=
    congrArg constantCauchyNameFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ConstantCauchyNameTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ConstantCauchyNameTasteGate_single_carrier_alignment_round_trip y)))

private def constantCauchyNameFields : ConstantCauchyNameUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConstantCauchyNameUp.mk D W Q R E H C P N => [D, W, Q, R, E, H, C, P, N]

private theorem ConstantCauchyNameTasteGate_single_carrier_alignment_fields :
    ∀ x y : ConstantCauchyNameUp, constantCauchyNameFields x = constantCauchyNameFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D1 W1 Q1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk D2 W2 Q2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance constantCauchyNameBHistCarrier : BHistCarrier ConstantCauchyNameUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := constantCauchyNameToEventFlow
  fromEventFlow := constantCauchyNameFromEventFlow

instance constantCauchyNameChapterTasteGate : ChapterTasteGate ConstantCauchyNameUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change constantCauchyNameFromEventFlow (constantCauchyNameToEventFlow x) = some x
    exact ConstantCauchyNameTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ConstantCauchyNameTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance constantCauchyNameFieldFaithful : FieldFaithful ConstantCauchyNameUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := constantCauchyNameFields
  field_faithful := ConstantCauchyNameTasteGate_single_carrier_alignment_fields

instance constantCauchyNameNontrivial : Nontrivial ConstantCauchyNameUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ConstantCauchyNameUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ConstantCauchyNameUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ConstantCauchyNameUp :=
  -- BEDC touchpoint anchor: BHist BMark
  constantCauchyNameChapterTasteGate

theorem ConstantCauchyNameTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ConstantCauchyNameUp) ∧
      Nonempty (FieldFaithful ConstantCauchyNameUp) ∧
        Nonempty (Nontrivial ConstantCauchyNameUp) ∧
          (∀ h : BHist,
            constantCauchyNameDecodeBHist (constantCauchyNameEncodeBHist h) = h) ∧
            (∀ x : ConstantCauchyNameUp,
              constantCauchyNameFromEventFlow (constantCauchyNameToEventFlow x) =
                some x) ∧
              (∀ x y : ConstantCauchyNameUp,
                constantCauchyNameToEventFlow x = constantCauchyNameToEventFlow y →
                  x = y) ∧
                constantCauchyNameEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨constantCauchyNameChapterTasteGate⟩,
      ⟨constantCauchyNameFieldFaithful⟩,
      ⟨constantCauchyNameNontrivial⟩,
      ConstantCauchyNameTasteGate_single_carrier_alignment_decode,
      ConstantCauchyNameTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        ConstantCauchyNameTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ConstantCauchyNameUp
