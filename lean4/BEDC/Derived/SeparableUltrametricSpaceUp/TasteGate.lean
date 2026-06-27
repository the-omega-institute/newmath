import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SeparableUltrametricSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SeparableUltrametricSpaceUp : Type where
  | mk (D U B S H C P N : BHist) : SeparableUltrametricSpaceUp
  deriving DecidableEq

def separableUltrametricSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: separableUltrametricSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: separableUltrametricSpaceEncodeBHist h

def separableUltrametricSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (separableUltrametricSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (separableUltrametricSpaceDecodeBHist tail)

private theorem SeparableUltrametricSpaceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      separableUltrametricSpaceDecodeBHist
        (separableUltrametricSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def separableUltrametricSpaceFields : SeparableUltrametricSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SeparableUltrametricSpaceUp.mk D U B S H C P N => [D, U, B, S, H, C, P, N]

def separableUltrametricSpaceToEventFlow : SeparableUltrametricSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (separableUltrametricSpaceFields x).map separableUltrametricSpaceEncodeBHist

private def separableUltrametricSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => separableUltrametricSpaceEventAtDefault index rest

def separableUltrametricSpaceFromEventFlow
    (ef : EventFlow) : Option SeparableUltrametricSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SeparableUltrametricSpaceUp.mk
      (separableUltrametricSpaceDecodeBHist (separableUltrametricSpaceEventAtDefault 0 ef))
      (separableUltrametricSpaceDecodeBHist (separableUltrametricSpaceEventAtDefault 1 ef))
      (separableUltrametricSpaceDecodeBHist (separableUltrametricSpaceEventAtDefault 2 ef))
      (separableUltrametricSpaceDecodeBHist (separableUltrametricSpaceEventAtDefault 3 ef))
      (separableUltrametricSpaceDecodeBHist (separableUltrametricSpaceEventAtDefault 4 ef))
      (separableUltrametricSpaceDecodeBHist (separableUltrametricSpaceEventAtDefault 5 ef))
      (separableUltrametricSpaceDecodeBHist (separableUltrametricSpaceEventAtDefault 6 ef))
      (separableUltrametricSpaceDecodeBHist (separableUltrametricSpaceEventAtDefault 7 ef)))

private theorem SeparableUltrametricSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SeparableUltrametricSpaceUp,
      separableUltrametricSpaceFromEventFlow
        (separableUltrametricSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D U B S H C P N =>
      change
        some
          (SeparableUltrametricSpaceUp.mk
            (separableUltrametricSpaceDecodeBHist
              (separableUltrametricSpaceEncodeBHist D))
            (separableUltrametricSpaceDecodeBHist
              (separableUltrametricSpaceEncodeBHist U))
            (separableUltrametricSpaceDecodeBHist
              (separableUltrametricSpaceEncodeBHist B))
            (separableUltrametricSpaceDecodeBHist
              (separableUltrametricSpaceEncodeBHist S))
            (separableUltrametricSpaceDecodeBHist
              (separableUltrametricSpaceEncodeBHist H))
            (separableUltrametricSpaceDecodeBHist
              (separableUltrametricSpaceEncodeBHist C))
            (separableUltrametricSpaceDecodeBHist
              (separableUltrametricSpaceEncodeBHist P))
            (separableUltrametricSpaceDecodeBHist
              (separableUltrametricSpaceEncodeBHist N))) =
          some (SeparableUltrametricSpaceUp.mk D U B S H C P N)
      rw [SeparableUltrametricSpaceTasteGate_single_carrier_alignment_decode D,
        SeparableUltrametricSpaceTasteGate_single_carrier_alignment_decode U,
        SeparableUltrametricSpaceTasteGate_single_carrier_alignment_decode B,
        SeparableUltrametricSpaceTasteGate_single_carrier_alignment_decode S,
        SeparableUltrametricSpaceTasteGate_single_carrier_alignment_decode H,
        SeparableUltrametricSpaceTasteGate_single_carrier_alignment_decode C,
        SeparableUltrametricSpaceTasteGate_single_carrier_alignment_decode P,
        SeparableUltrametricSpaceTasteGate_single_carrier_alignment_decode N]

private theorem SeparableUltrametricSpaceTasteGate_single_carrier_alignment_injective
    {x y : SeparableUltrametricSpaceUp} :
    separableUltrametricSpaceToEventFlow x =
      separableUltrametricSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      separableUltrametricSpaceFromEventFlow
          (separableUltrametricSpaceToEventFlow x) =
        separableUltrametricSpaceFromEventFlow
          (separableUltrametricSpaceToEventFlow y) :=
    congrArg separableUltrametricSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SeparableUltrametricSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SeparableUltrametricSpaceTasteGate_single_carrier_alignment_round_trip y)))

private theorem SeparableUltrametricSpaceTasteGate_single_carrier_alignment_fields :
    ∀ x y : SeparableUltrametricSpaceUp,
      separableUltrametricSpaceFields x = separableUltrametricSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D1 U1 B1 S1 H1 C1 P1 N1 =>
      cases y with
      | mk D2 U2 B2 S2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance separableUltrametricSpaceBHistCarrier :
    BHistCarrier SeparableUltrametricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := separableUltrametricSpaceToEventFlow
  fromEventFlow := separableUltrametricSpaceFromEventFlow

instance separableUltrametricSpaceChapterTasteGate :
    ChapterTasteGate SeparableUltrametricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      separableUltrametricSpaceFromEventFlow
        (separableUltrametricSpaceToEventFlow x) = some x
    exact SeparableUltrametricSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SeparableUltrametricSpaceTasteGate_single_carrier_alignment_injective heq)

instance separableUltrametricSpaceFieldFaithful :
    FieldFaithful SeparableUltrametricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := separableUltrametricSpaceFields
  field_faithful := SeparableUltrametricSpaceTasteGate_single_carrier_alignment_fields

instance separableUltrametricSpaceNontrivial :
    Nontrivial SeparableUltrametricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SeparableUltrametricSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SeparableUltrametricSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem SeparableUltrametricSpaceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate SeparableUltrametricSpaceUp) ∧
      Nonempty (FieldFaithful SeparableUltrametricSpaceUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial SeparableUltrametricSpaceUp) ∧
          (∀ h : BHist,
            separableUltrametricSpaceDecodeBHist
              (separableUltrametricSpaceEncodeBHist h) = h) ∧
            separableUltrametricSpaceEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
              (∀ x : SeparableUltrametricSpaceUp,
                separableUltrametricSpaceFromEventFlow
                  (separableUltrametricSpaceToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨separableUltrametricSpaceChapterTasteGate⟩,
      ⟨separableUltrametricSpaceFieldFaithful⟩,
      ⟨separableUltrametricSpaceNontrivial⟩,
      SeparableUltrametricSpaceTasteGate_single_carrier_alignment_decode,
      rfl,
      SeparableUltrametricSpaceTasteGate_single_carrier_alignment_round_trip⟩

end BEDC.Derived.SeparableUltrametricSpaceUp
