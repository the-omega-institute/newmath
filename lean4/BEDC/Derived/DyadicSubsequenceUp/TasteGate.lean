import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicSubsequenceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicSubsequenceUp : Type where
  | mk (A W D I O R E H C P N : BHist) : DyadicSubsequenceUp
  deriving DecidableEq

def dyadicSubsequenceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicSubsequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicSubsequenceEncodeBHist h

def dyadicSubsequenceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicSubsequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicSubsequenceDecodeBHist tail)

private theorem DyadicSubsequenceTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      dyadicSubsequenceDecodeBHist (dyadicSubsequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicSubsequenceFields : DyadicSubsequenceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicSubsequenceUp.mk A W D I O R E H C P N => [A, W, D, I, O, R, E, H, C, P, N]

def dyadicSubsequenceToEventFlow : DyadicSubsequenceUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicSubsequenceFields x).map dyadicSubsequenceEncodeBHist

private def dyadicSubsequenceEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicSubsequenceEventAtDefault index rest

def dyadicSubsequenceFromEventFlow : EventFlow -> Option DyadicSubsequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (DyadicSubsequenceUp.mk
          (dyadicSubsequenceDecodeBHist (dyadicSubsequenceEventAtDefault 0 ef))
          (dyadicSubsequenceDecodeBHist (dyadicSubsequenceEventAtDefault 1 ef))
          (dyadicSubsequenceDecodeBHist (dyadicSubsequenceEventAtDefault 2 ef))
          (dyadicSubsequenceDecodeBHist (dyadicSubsequenceEventAtDefault 3 ef))
          (dyadicSubsequenceDecodeBHist (dyadicSubsequenceEventAtDefault 4 ef))
          (dyadicSubsequenceDecodeBHist (dyadicSubsequenceEventAtDefault 5 ef))
          (dyadicSubsequenceDecodeBHist (dyadicSubsequenceEventAtDefault 6 ef))
          (dyadicSubsequenceDecodeBHist (dyadicSubsequenceEventAtDefault 7 ef))
          (dyadicSubsequenceDecodeBHist (dyadicSubsequenceEventAtDefault 8 ef))
          (dyadicSubsequenceDecodeBHist (dyadicSubsequenceEventAtDefault 9 ef))
          (dyadicSubsequenceDecodeBHist (dyadicSubsequenceEventAtDefault 10 ef)))

private theorem DyadicSubsequenceTasteGate_single_carrier_alignment_round_trip :
    forall x : DyadicSubsequenceUp,
      dyadicSubsequenceFromEventFlow (dyadicSubsequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A W D I O R E H C P N =>
      change
        some
          (DyadicSubsequenceUp.mk
            (dyadicSubsequenceDecodeBHist (dyadicSubsequenceEncodeBHist A))
            (dyadicSubsequenceDecodeBHist (dyadicSubsequenceEncodeBHist W))
            (dyadicSubsequenceDecodeBHist (dyadicSubsequenceEncodeBHist D))
            (dyadicSubsequenceDecodeBHist (dyadicSubsequenceEncodeBHist I))
            (dyadicSubsequenceDecodeBHist (dyadicSubsequenceEncodeBHist O))
            (dyadicSubsequenceDecodeBHist (dyadicSubsequenceEncodeBHist R))
            (dyadicSubsequenceDecodeBHist (dyadicSubsequenceEncodeBHist E))
            (dyadicSubsequenceDecodeBHist (dyadicSubsequenceEncodeBHist H))
            (dyadicSubsequenceDecodeBHist (dyadicSubsequenceEncodeBHist C))
            (dyadicSubsequenceDecodeBHist (dyadicSubsequenceEncodeBHist P))
            (dyadicSubsequenceDecodeBHist (dyadicSubsequenceEncodeBHist N))) =
          some (DyadicSubsequenceUp.mk A W D I O R E H C P N)
      rw [DyadicSubsequenceTasteGate_single_carrier_alignment_decode_encode A,
        DyadicSubsequenceTasteGate_single_carrier_alignment_decode_encode W,
        DyadicSubsequenceTasteGate_single_carrier_alignment_decode_encode D,
        DyadicSubsequenceTasteGate_single_carrier_alignment_decode_encode I,
        DyadicSubsequenceTasteGate_single_carrier_alignment_decode_encode O,
        DyadicSubsequenceTasteGate_single_carrier_alignment_decode_encode R,
        DyadicSubsequenceTasteGate_single_carrier_alignment_decode_encode E,
        DyadicSubsequenceTasteGate_single_carrier_alignment_decode_encode H,
        DyadicSubsequenceTasteGate_single_carrier_alignment_decode_encode C,
        DyadicSubsequenceTasteGate_single_carrier_alignment_decode_encode P,
        DyadicSubsequenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem DyadicSubsequenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicSubsequenceUp} :
    dyadicSubsequenceToEventFlow x = dyadicSubsequenceToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicSubsequenceFromEventFlow (dyadicSubsequenceToEventFlow x) =
        dyadicSubsequenceFromEventFlow (dyadicSubsequenceToEventFlow y) :=
    congrArg dyadicSubsequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DyadicSubsequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DyadicSubsequenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem DyadicSubsequenceTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : DyadicSubsequenceUp,
      dyadicSubsequenceFields x = dyadicSubsequenceFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A1 W1 D1 I1 O1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk A2 W2 D2 I2 O2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance dyadicSubsequenceBHistCarrier : BHistCarrier DyadicSubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicSubsequenceToEventFlow
  fromEventFlow := dyadicSubsequenceFromEventFlow

instance dyadicSubsequenceChapterTasteGate :
    ChapterTasteGate DyadicSubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicSubsequenceFromEventFlow (dyadicSubsequenceToEventFlow x) = some x
    exact DyadicSubsequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicSubsequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance dyadicSubsequenceFieldFaithful :
    FieldFaithful DyadicSubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicSubsequenceFields
  field_faithful := DyadicSubsequenceTasteGate_single_carrier_alignment_fields_faithful

instance dyadicSubsequenceNontrivial :
    BEDC.Meta.TasteGate.Nontrivial DyadicSubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicSubsequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DyadicSubsequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DyadicSubsequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicSubsequenceChapterTasteGate

theorem DyadicSubsequenceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DyadicSubsequenceUp) ∧
      Nonempty (FieldFaithful DyadicSubsequenceUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial DyadicSubsequenceUp) ∧
          (∀ h : BHist, dyadicSubsequenceDecodeBHist (dyadicSubsequenceEncodeBHist h) = h) ∧
            (∀ x : DyadicSubsequenceUp,
              dyadicSubsequenceFromEventFlow (dyadicSubsequenceToEventFlow x) = some x) ∧
              (∀ x y : DyadicSubsequenceUp,
                dyadicSubsequenceToEventFlow x = dyadicSubsequenceToEventFlow y -> x = y) ∧
                dyadicSubsequenceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨dyadicSubsequenceChapterTasteGate⟩,
      ⟨⟨dyadicSubsequenceFieldFaithful⟩,
        ⟨⟨dyadicSubsequenceNontrivial⟩,
          ⟨DyadicSubsequenceTasteGate_single_carrier_alignment_decode_encode,
            ⟨DyadicSubsequenceTasteGate_single_carrier_alignment_round_trip,
              ⟨(fun _ _ heq =>
                DyadicSubsequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
                rfl⟩⟩⟩⟩⟩⟩

end BEDC.Derived.DyadicSubsequenceUp.TasteGate
