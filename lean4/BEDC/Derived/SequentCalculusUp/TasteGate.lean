import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SequentCalculusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SequentCalculusUp : Type where
  | mk (F Gamma Delta R T K H C P N : BHist) : SequentCalculusUp
  deriving DecidableEq

def sequentCalculusEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sequentCalculusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sequentCalculusEncodeBHist h

def sequentCalculusDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sequentCalculusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sequentCalculusDecodeBHist tail)

private theorem SequentCalculusTasteGate_single_carrier_alignment_decode :
    forall h : BHist, sequentCalculusDecodeBHist (sequentCalculusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sequentCalculusFields : SequentCalculusUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SequentCalculusUp.mk F Gamma Delta R T K H C P N => [F, Gamma, Delta, R, T, K, H, C, P, N]

def sequentCalculusToEventFlow : SequentCalculusUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (sequentCalculusFields x).map sequentCalculusEncodeBHist

private def sequentCalculusEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => sequentCalculusEventAt index rest

def sequentCalculusFromEventFlow (ef : EventFlow) : Option SequentCalculusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SequentCalculusUp.mk
      (sequentCalculusDecodeBHist (sequentCalculusEventAt 0 ef))
      (sequentCalculusDecodeBHist (sequentCalculusEventAt 1 ef))
      (sequentCalculusDecodeBHist (sequentCalculusEventAt 2 ef))
      (sequentCalculusDecodeBHist (sequentCalculusEventAt 3 ef))
      (sequentCalculusDecodeBHist (sequentCalculusEventAt 4 ef))
      (sequentCalculusDecodeBHist (sequentCalculusEventAt 5 ef))
      (sequentCalculusDecodeBHist (sequentCalculusEventAt 6 ef))
      (sequentCalculusDecodeBHist (sequentCalculusEventAt 7 ef))
      (sequentCalculusDecodeBHist (sequentCalculusEventAt 8 ef))
      (sequentCalculusDecodeBHist (sequentCalculusEventAt 9 ef)))

private theorem SequentCalculusTasteGate_single_carrier_alignment_round_trip
    (x : SequentCalculusUp) :
    sequentCalculusFromEventFlow (sequentCalculusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F Gamma Delta R T K H C P N =>
      change
        some
          (SequentCalculusUp.mk
            (sequentCalculusDecodeBHist (sequentCalculusEncodeBHist F))
            (sequentCalculusDecodeBHist (sequentCalculusEncodeBHist Gamma))
            (sequentCalculusDecodeBHist (sequentCalculusEncodeBHist Delta))
            (sequentCalculusDecodeBHist (sequentCalculusEncodeBHist R))
            (sequentCalculusDecodeBHist (sequentCalculusEncodeBHist T))
            (sequentCalculusDecodeBHist (sequentCalculusEncodeBHist K))
            (sequentCalculusDecodeBHist (sequentCalculusEncodeBHist H))
            (sequentCalculusDecodeBHist (sequentCalculusEncodeBHist C))
            (sequentCalculusDecodeBHist (sequentCalculusEncodeBHist P))
            (sequentCalculusDecodeBHist (sequentCalculusEncodeBHist N))) =
          some (SequentCalculusUp.mk F Gamma Delta R T K H C P N)
      rw [SequentCalculusTasteGate_single_carrier_alignment_decode F,
        SequentCalculusTasteGate_single_carrier_alignment_decode Gamma,
        SequentCalculusTasteGate_single_carrier_alignment_decode Delta,
        SequentCalculusTasteGate_single_carrier_alignment_decode R,
        SequentCalculusTasteGate_single_carrier_alignment_decode T,
        SequentCalculusTasteGate_single_carrier_alignment_decode K,
        SequentCalculusTasteGate_single_carrier_alignment_decode H,
        SequentCalculusTasteGate_single_carrier_alignment_decode C,
        SequentCalculusTasteGate_single_carrier_alignment_decode P,
        SequentCalculusTasteGate_single_carrier_alignment_decode N]

private theorem SequentCalculusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SequentCalculusUp} :
    sequentCalculusToEventFlow x = sequentCalculusToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sequentCalculusFromEventFlow (sequentCalculusToEventFlow x) =
        sequentCalculusFromEventFlow (sequentCalculusToEventFlow y) :=
    congrArg sequentCalculusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SequentCalculusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SequentCalculusTasteGate_single_carrier_alignment_round_trip y)))

private theorem SequentCalculusTasteGate_single_carrier_alignment_fields :
    forall x y : SequentCalculusUp, sequentCalculusFields x = sequentCalculusFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 Gamma1 Delta1 R1 T1 K1 H1 C1 P1 N1 =>
      cases y with
      | mk F2 Gamma2 Delta2 R2 T2 K2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance sequentCalculusBHistCarrier : BHistCarrier SequentCalculusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sequentCalculusToEventFlow
  fromEventFlow := sequentCalculusFromEventFlow

instance sequentCalculusChapterTasteGate : ChapterTasteGate SequentCalculusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sequentCalculusFromEventFlow (sequentCalculusToEventFlow x) = some x
    exact SequentCalculusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SequentCalculusTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance sequentCalculusFieldFaithful : FieldFaithful SequentCalculusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := sequentCalculusFields
  field_faithful := SequentCalculusTasteGate_single_carrier_alignment_fields

instance sequentCalculusNontrivial :
    BEDC.Meta.TasteGate.Nontrivial SequentCalculusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SequentCalculusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SequentCalculusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SequentCalculusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sequentCalculusChapterTasteGate

theorem SequentCalculusTasteGate_single_carrier_alignment :
    (forall h : BHist, sequentCalculusDecodeBHist (sequentCalculusEncodeBHist h) = h) ∧
      (forall x : SequentCalculusUp,
        sequentCalculusFromEventFlow (sequentCalculusToEventFlow x) = some x) ∧
          Nonempty (BHistCarrier SequentCalculusUp) ∧
            Nonempty (ChapterTasteGate SequentCalculusUp) ∧
              Nonempty (FieldFaithful SequentCalculusUp) ∧
                Nonempty (BEDC.Meta.TasteGate.Nontrivial SequentCalculusUp) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨SequentCalculusTasteGate_single_carrier_alignment_decode,
      SequentCalculusTasteGate_single_carrier_alignment_round_trip,
      ⟨sequentCalculusBHistCarrier⟩,
      ⟨sequentCalculusChapterTasteGate⟩,
      ⟨sequentCalculusFieldFaithful⟩,
      ⟨sequentCalculusNontrivial⟩⟩

end BEDC.Derived.SequentCalculusUp
