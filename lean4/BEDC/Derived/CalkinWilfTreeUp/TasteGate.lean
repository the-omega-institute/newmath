import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CalkinWilfTreeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CalkinWilfTreeUp : Type where
  | mk (A Q L R S F H C P N : BHist) : CalkinWilfTreeUp
  deriving DecidableEq

def calkinWilfTreeEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: calkinWilfTreeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: calkinWilfTreeEncodeBHist h

def calkinWilfTreeDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (calkinWilfTreeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (calkinWilfTreeDecodeBHist tail)

private theorem CalkinWilfTreeTasteGate_single_carrier_alignment_decode :
    forall h : BHist, calkinWilfTreeDecodeBHist (calkinWilfTreeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def calkinWilfTreeToEventFlow : CalkinWilfTreeUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CalkinWilfTreeUp.mk A Q L R S F H C P N =>
      [[BMark.b0],
        calkinWilfTreeEncodeBHist A,
        [BMark.b1, BMark.b0],
        calkinWilfTreeEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b0],
        calkinWilfTreeEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        calkinWilfTreeEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        calkinWilfTreeEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        calkinWilfTreeEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        calkinWilfTreeEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        calkinWilfTreeEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        calkinWilfTreeEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        calkinWilfTreeEncodeBHist N]

private def calkinWilfTreeEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => calkinWilfTreeEventAtDefault index rest

def calkinWilfTreeFromEventFlow (ef : EventFlow) : Option CalkinWilfTreeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CalkinWilfTreeUp.mk
      (calkinWilfTreeDecodeBHist (calkinWilfTreeEventAtDefault 1 ef))
      (calkinWilfTreeDecodeBHist (calkinWilfTreeEventAtDefault 3 ef))
      (calkinWilfTreeDecodeBHist (calkinWilfTreeEventAtDefault 5 ef))
      (calkinWilfTreeDecodeBHist (calkinWilfTreeEventAtDefault 7 ef))
      (calkinWilfTreeDecodeBHist (calkinWilfTreeEventAtDefault 9 ef))
      (calkinWilfTreeDecodeBHist (calkinWilfTreeEventAtDefault 11 ef))
      (calkinWilfTreeDecodeBHist (calkinWilfTreeEventAtDefault 13 ef))
      (calkinWilfTreeDecodeBHist (calkinWilfTreeEventAtDefault 15 ef))
      (calkinWilfTreeDecodeBHist (calkinWilfTreeEventAtDefault 17 ef))
      (calkinWilfTreeDecodeBHist (calkinWilfTreeEventAtDefault 19 ef)))

private theorem CalkinWilfTreeTasteGate_single_carrier_alignment_round_trip :
    forall x : CalkinWilfTreeUp,
      calkinWilfTreeFromEventFlow (calkinWilfTreeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A Q L R S F H C P N =>
      change
        some
          (CalkinWilfTreeUp.mk
            (calkinWilfTreeDecodeBHist (calkinWilfTreeEncodeBHist A))
            (calkinWilfTreeDecodeBHist (calkinWilfTreeEncodeBHist Q))
            (calkinWilfTreeDecodeBHist (calkinWilfTreeEncodeBHist L))
            (calkinWilfTreeDecodeBHist (calkinWilfTreeEncodeBHist R))
            (calkinWilfTreeDecodeBHist (calkinWilfTreeEncodeBHist S))
            (calkinWilfTreeDecodeBHist (calkinWilfTreeEncodeBHist F))
            (calkinWilfTreeDecodeBHist (calkinWilfTreeEncodeBHist H))
            (calkinWilfTreeDecodeBHist (calkinWilfTreeEncodeBHist C))
            (calkinWilfTreeDecodeBHist (calkinWilfTreeEncodeBHist P))
            (calkinWilfTreeDecodeBHist (calkinWilfTreeEncodeBHist N))) =
          some (CalkinWilfTreeUp.mk A Q L R S F H C P N)
      rw [CalkinWilfTreeTasteGate_single_carrier_alignment_decode A,
        CalkinWilfTreeTasteGate_single_carrier_alignment_decode Q,
        CalkinWilfTreeTasteGate_single_carrier_alignment_decode L,
        CalkinWilfTreeTasteGate_single_carrier_alignment_decode R,
        CalkinWilfTreeTasteGate_single_carrier_alignment_decode S,
        CalkinWilfTreeTasteGate_single_carrier_alignment_decode F,
        CalkinWilfTreeTasteGate_single_carrier_alignment_decode H,
        CalkinWilfTreeTasteGate_single_carrier_alignment_decode C,
        CalkinWilfTreeTasteGate_single_carrier_alignment_decode P,
        CalkinWilfTreeTasteGate_single_carrier_alignment_decode N]

private theorem CalkinWilfTreeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CalkinWilfTreeUp} :
    calkinWilfTreeToEventFlow x = calkinWilfTreeToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      calkinWilfTreeFromEventFlow (calkinWilfTreeToEventFlow x) =
        calkinWilfTreeFromEventFlow (calkinWilfTreeToEventFlow y) :=
    congrArg calkinWilfTreeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CalkinWilfTreeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CalkinWilfTreeTasteGate_single_carrier_alignment_round_trip y)))

private def calkinWilfTreeFields : CalkinWilfTreeUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CalkinWilfTreeUp.mk A Q L R S F H C P N => [A, Q, L, R, S, F, H, C, P, N]

private theorem CalkinWilfTreeTasteGate_single_carrier_alignment_fields :
    forall x y : CalkinWilfTreeUp, calkinWilfTreeFields x = calkinWilfTreeFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A1 Q1 L1 R1 S1 F1 H1 C1 P1 N1 =>
      cases y with
      | mk A2 Q2 L2 R2 S2 F2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance calkinWilfTreeBHistCarrier : BHistCarrier CalkinWilfTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := calkinWilfTreeToEventFlow
  fromEventFlow := calkinWilfTreeFromEventFlow

instance calkinWilfTreeChapterTasteGate : ChapterTasteGate CalkinWilfTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change calkinWilfTreeFromEventFlow (calkinWilfTreeToEventFlow x) = some x
    exact CalkinWilfTreeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CalkinWilfTreeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance calkinWilfTreeFieldFaithful : FieldFaithful CalkinWilfTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := calkinWilfTreeFields
  field_faithful := CalkinWilfTreeTasteGate_single_carrier_alignment_fields

instance calkinWilfTreeNontrivial : Nontrivial CalkinWilfTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CalkinWilfTreeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CalkinWilfTreeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CalkinWilfTreeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  calkinWilfTreeChapterTasteGate

theorem CalkinWilfTreeTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CalkinWilfTreeUp) ∧
      Nonempty (FieldFaithful CalkinWilfTreeUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CalkinWilfTreeUp) ∧
          (∀ h : BHist, calkinWilfTreeDecodeBHist (calkinWilfTreeEncodeBHist h) = h) ∧
            calkinWilfTreeEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨calkinWilfTreeChapterTasteGate⟩,
      ⟨calkinWilfTreeFieldFaithful⟩,
      ⟨calkinWilfTreeNontrivial⟩,
      CalkinWilfTreeTasteGate_single_carrier_alignment_decode,
      rfl⟩

end BEDC.Derived.CalkinWilfTreeUp
