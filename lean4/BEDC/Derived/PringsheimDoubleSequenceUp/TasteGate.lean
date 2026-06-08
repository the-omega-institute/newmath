import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PringsheimDoubleSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PringsheimDoubleSequenceUp : Type where
  | mk (I J W T Q E H C P N : BHist) : PringsheimDoubleSequenceUp
  deriving DecidableEq

def pringsheimDoubleSequenceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: pringsheimDoubleSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: pringsheimDoubleSequenceEncodeBHist h

def pringsheimDoubleSequenceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (pringsheimDoubleSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (pringsheimDoubleSequenceDecodeBHist tail)

private theorem PringsheimDoubleSequenceTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      pringsheimDoubleSequenceDecodeBHist (pringsheimDoubleSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def pringsheimDoubleSequenceToEventFlow : PringsheimDoubleSequenceUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PringsheimDoubleSequenceUp.mk I J W T Q E H C P N =>
      [[BMark.b0],
        pringsheimDoubleSequenceEncodeBHist I,
        [BMark.b1, BMark.b0],
        pringsheimDoubleSequenceEncodeBHist J,
        [BMark.b1, BMark.b1, BMark.b0],
        pringsheimDoubleSequenceEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        pringsheimDoubleSequenceEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        pringsheimDoubleSequenceEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        pringsheimDoubleSequenceEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        pringsheimDoubleSequenceEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        pringsheimDoubleSequenceEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        pringsheimDoubleSequenceEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        pringsheimDoubleSequenceEncodeBHist N]

private def pringsheimDoubleSequenceEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => pringsheimDoubleSequenceEventAtDefault index rest

def pringsheimDoubleSequenceFromEventFlow (ef : EventFlow) :
    Option PringsheimDoubleSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PringsheimDoubleSequenceUp.mk
      (pringsheimDoubleSequenceDecodeBHist (pringsheimDoubleSequenceEventAtDefault 1 ef))
      (pringsheimDoubleSequenceDecodeBHist (pringsheimDoubleSequenceEventAtDefault 3 ef))
      (pringsheimDoubleSequenceDecodeBHist (pringsheimDoubleSequenceEventAtDefault 5 ef))
      (pringsheimDoubleSequenceDecodeBHist (pringsheimDoubleSequenceEventAtDefault 7 ef))
      (pringsheimDoubleSequenceDecodeBHist (pringsheimDoubleSequenceEventAtDefault 9 ef))
      (pringsheimDoubleSequenceDecodeBHist (pringsheimDoubleSequenceEventAtDefault 11 ef))
      (pringsheimDoubleSequenceDecodeBHist (pringsheimDoubleSequenceEventAtDefault 13 ef))
      (pringsheimDoubleSequenceDecodeBHist (pringsheimDoubleSequenceEventAtDefault 15 ef))
      (pringsheimDoubleSequenceDecodeBHist (pringsheimDoubleSequenceEventAtDefault 17 ef))
      (pringsheimDoubleSequenceDecodeBHist (pringsheimDoubleSequenceEventAtDefault 19 ef)))

private theorem PringsheimDoubleSequenceTasteGate_single_carrier_alignment_round_trip :
    forall x : PringsheimDoubleSequenceUp,
      pringsheimDoubleSequenceFromEventFlow (pringsheimDoubleSequenceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I J W T Q E H C P N =>
      change
        some
          (PringsheimDoubleSequenceUp.mk
            (pringsheimDoubleSequenceDecodeBHist (pringsheimDoubleSequenceEncodeBHist I))
            (pringsheimDoubleSequenceDecodeBHist (pringsheimDoubleSequenceEncodeBHist J))
            (pringsheimDoubleSequenceDecodeBHist (pringsheimDoubleSequenceEncodeBHist W))
            (pringsheimDoubleSequenceDecodeBHist (pringsheimDoubleSequenceEncodeBHist T))
            (pringsheimDoubleSequenceDecodeBHist (pringsheimDoubleSequenceEncodeBHist Q))
            (pringsheimDoubleSequenceDecodeBHist (pringsheimDoubleSequenceEncodeBHist E))
            (pringsheimDoubleSequenceDecodeBHist (pringsheimDoubleSequenceEncodeBHist H))
            (pringsheimDoubleSequenceDecodeBHist (pringsheimDoubleSequenceEncodeBHist C))
            (pringsheimDoubleSequenceDecodeBHist (pringsheimDoubleSequenceEncodeBHist P))
            (pringsheimDoubleSequenceDecodeBHist (pringsheimDoubleSequenceEncodeBHist N))) =
          some (PringsheimDoubleSequenceUp.mk I J W T Q E H C P N)
      rw [PringsheimDoubleSequenceTasteGate_single_carrier_alignment_decode I,
        PringsheimDoubleSequenceTasteGate_single_carrier_alignment_decode J,
        PringsheimDoubleSequenceTasteGate_single_carrier_alignment_decode W,
        PringsheimDoubleSequenceTasteGate_single_carrier_alignment_decode T,
        PringsheimDoubleSequenceTasteGate_single_carrier_alignment_decode Q,
        PringsheimDoubleSequenceTasteGate_single_carrier_alignment_decode E,
        PringsheimDoubleSequenceTasteGate_single_carrier_alignment_decode H,
        PringsheimDoubleSequenceTasteGate_single_carrier_alignment_decode C,
        PringsheimDoubleSequenceTasteGate_single_carrier_alignment_decode P,
        PringsheimDoubleSequenceTasteGate_single_carrier_alignment_decode N]

private theorem PringsheimDoubleSequenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PringsheimDoubleSequenceUp} :
    pringsheimDoubleSequenceToEventFlow x = pringsheimDoubleSequenceToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      pringsheimDoubleSequenceFromEventFlow (pringsheimDoubleSequenceToEventFlow x) =
        pringsheimDoubleSequenceFromEventFlow (pringsheimDoubleSequenceToEventFlow y) :=
    congrArg pringsheimDoubleSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (PringsheimDoubleSequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (PringsheimDoubleSequenceTasteGate_single_carrier_alignment_round_trip y)))

private def pringsheimDoubleSequenceFields : PringsheimDoubleSequenceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PringsheimDoubleSequenceUp.mk I J W T Q E H C P N => [I, J, W, T, Q, E, H, C, P, N]

private theorem PringsheimDoubleSequenceTasteGate_single_carrier_alignment_fields :
    forall x y : PringsheimDoubleSequenceUp,
      pringsheimDoubleSequenceFields x = pringsheimDoubleSequenceFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 J1 W1 T1 Q1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 J2 W2 T2 Q2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance pringsheimDoubleSequenceBHistCarrier : BHistCarrier PringsheimDoubleSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := pringsheimDoubleSequenceToEventFlow
  fromEventFlow := pringsheimDoubleSequenceFromEventFlow

instance pringsheimDoubleSequenceChapterTasteGate :
    ChapterTasteGate PringsheimDoubleSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change pringsheimDoubleSequenceFromEventFlow (pringsheimDoubleSequenceToEventFlow x) =
      some x
    exact PringsheimDoubleSequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (PringsheimDoubleSequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance pringsheimDoubleSequenceFieldFaithful :
    FieldFaithful PringsheimDoubleSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := pringsheimDoubleSequenceFields
  field_faithful := PringsheimDoubleSequenceTasteGate_single_carrier_alignment_fields

instance pringsheimDoubleSequenceNontrivial :
    Nontrivial PringsheimDoubleSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PringsheimDoubleSequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PringsheimDoubleSequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PringsheimDoubleSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  pringsheimDoubleSequenceChapterTasteGate

theorem PringsheimDoubleSequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      pringsheimDoubleSequenceDecodeBHist (pringsheimDoubleSequenceEncodeBHist h) = h) ∧
      (∀ x : PringsheimDoubleSequenceUp,
        pringsheimDoubleSequenceFromEventFlow (pringsheimDoubleSequenceToEventFlow x) =
          some x) ∧
        (∀ x y : PringsheimDoubleSequenceUp,
          pringsheimDoubleSequenceToEventFlow x = pringsheimDoubleSequenceToEventFlow y ->
            x = y) ∧
          pringsheimDoubleSequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨PringsheimDoubleSequenceTasteGate_single_carrier_alignment_decode,
      PringsheimDoubleSequenceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        PringsheimDoubleSequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.PringsheimDoubleSequenceUp
