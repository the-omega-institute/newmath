import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedNormalConsistencyWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedNormalConsistencyWitnessUp : Type where
  | mk (T F L B E R H C P N : BHist) : ClosedNormalConsistencyWitnessUp
  deriving DecidableEq

def closedNormalConsistencyWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedNormalConsistencyWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedNormalConsistencyWitnessEncodeBHist h

def closedNormalConsistencyWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedNormalConsistencyWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedNormalConsistencyWitnessDecodeBHist tail)

private theorem ClosedNormalConsistencyWitnessTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      closedNormalConsistencyWitnessDecodeBHist
        (closedNormalConsistencyWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def closedNormalConsistencyWitnessFields :
    ClosedNormalConsistencyWitnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedNormalConsistencyWitnessUp.mk T F L B E R H C P N =>
      [T, F, L, B, E, R, H, C, P, N]

def closedNormalConsistencyWitnessToEventFlow :
    ClosedNormalConsistencyWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (closedNormalConsistencyWitnessFields x).map
      closedNormalConsistencyWitnessEncodeBHist

private def closedNormalConsistencyWitnessEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      closedNormalConsistencyWitnessEventAtDefault index rest

def closedNormalConsistencyWitnessFromEventFlow
    (ef : EventFlow) : Option ClosedNormalConsistencyWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ClosedNormalConsistencyWitnessUp.mk
      (closedNormalConsistencyWitnessDecodeBHist
        (closedNormalConsistencyWitnessEventAtDefault 0 ef))
      (closedNormalConsistencyWitnessDecodeBHist
        (closedNormalConsistencyWitnessEventAtDefault 1 ef))
      (closedNormalConsistencyWitnessDecodeBHist
        (closedNormalConsistencyWitnessEventAtDefault 2 ef))
      (closedNormalConsistencyWitnessDecodeBHist
        (closedNormalConsistencyWitnessEventAtDefault 3 ef))
      (closedNormalConsistencyWitnessDecodeBHist
        (closedNormalConsistencyWitnessEventAtDefault 4 ef))
      (closedNormalConsistencyWitnessDecodeBHist
        (closedNormalConsistencyWitnessEventAtDefault 5 ef))
      (closedNormalConsistencyWitnessDecodeBHist
        (closedNormalConsistencyWitnessEventAtDefault 6 ef))
      (closedNormalConsistencyWitnessDecodeBHist
        (closedNormalConsistencyWitnessEventAtDefault 7 ef))
      (closedNormalConsistencyWitnessDecodeBHist
        (closedNormalConsistencyWitnessEventAtDefault 8 ef))
      (closedNormalConsistencyWitnessDecodeBHist
        (closedNormalConsistencyWitnessEventAtDefault 9 ef)))

private theorem ClosedNormalConsistencyWitnessTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ClosedNormalConsistencyWitnessUp,
      closedNormalConsistencyWitnessFromEventFlow
        (closedNormalConsistencyWitnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T F L B E R H C P N =>
      change
        some
          (ClosedNormalConsistencyWitnessUp.mk
            (closedNormalConsistencyWitnessDecodeBHist
              (closedNormalConsistencyWitnessEncodeBHist T))
            (closedNormalConsistencyWitnessDecodeBHist
              (closedNormalConsistencyWitnessEncodeBHist F))
            (closedNormalConsistencyWitnessDecodeBHist
              (closedNormalConsistencyWitnessEncodeBHist L))
            (closedNormalConsistencyWitnessDecodeBHist
              (closedNormalConsistencyWitnessEncodeBHist B))
            (closedNormalConsistencyWitnessDecodeBHist
              (closedNormalConsistencyWitnessEncodeBHist E))
            (closedNormalConsistencyWitnessDecodeBHist
              (closedNormalConsistencyWitnessEncodeBHist R))
            (closedNormalConsistencyWitnessDecodeBHist
              (closedNormalConsistencyWitnessEncodeBHist H))
            (closedNormalConsistencyWitnessDecodeBHist
              (closedNormalConsistencyWitnessEncodeBHist C))
            (closedNormalConsistencyWitnessDecodeBHist
              (closedNormalConsistencyWitnessEncodeBHist P))
            (closedNormalConsistencyWitnessDecodeBHist
              (closedNormalConsistencyWitnessEncodeBHist N))) =
          some (ClosedNormalConsistencyWitnessUp.mk T F L B E R H C P N)
      rw [ClosedNormalConsistencyWitnessTasteGate_single_carrier_alignment_decode T,
        ClosedNormalConsistencyWitnessTasteGate_single_carrier_alignment_decode F,
        ClosedNormalConsistencyWitnessTasteGate_single_carrier_alignment_decode L,
        ClosedNormalConsistencyWitnessTasteGate_single_carrier_alignment_decode B,
        ClosedNormalConsistencyWitnessTasteGate_single_carrier_alignment_decode E,
        ClosedNormalConsistencyWitnessTasteGate_single_carrier_alignment_decode R,
        ClosedNormalConsistencyWitnessTasteGate_single_carrier_alignment_decode H,
        ClosedNormalConsistencyWitnessTasteGate_single_carrier_alignment_decode C,
        ClosedNormalConsistencyWitnessTasteGate_single_carrier_alignment_decode P,
        ClosedNormalConsistencyWitnessTasteGate_single_carrier_alignment_decode N]

private theorem ClosedNormalConsistencyWitnessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ClosedNormalConsistencyWitnessUp} :
    closedNormalConsistencyWitnessToEventFlow x =
      closedNormalConsistencyWitnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedNormalConsistencyWitnessFromEventFlow
          (closedNormalConsistencyWitnessToEventFlow x) =
        closedNormalConsistencyWitnessFromEventFlow
          (closedNormalConsistencyWitnessToEventFlow y) :=
    congrArg closedNormalConsistencyWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ClosedNormalConsistencyWitnessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ClosedNormalConsistencyWitnessTasteGate_single_carrier_alignment_round_trip y)))

private theorem ClosedNormalConsistencyWitnessTasteGate_single_carrier_alignment_fields :
    ∀ x y : ClosedNormalConsistencyWitnessUp,
      closedNormalConsistencyWitnessFields x = closedNormalConsistencyWitnessFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T1 F1 L1 B1 E1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk T2 F2 L2 B2 E2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance closedNormalConsistencyWitnessBHistCarrier :
    BHistCarrier ClosedNormalConsistencyWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedNormalConsistencyWitnessToEventFlow
  fromEventFlow := closedNormalConsistencyWitnessFromEventFlow

instance closedNormalConsistencyWitnessChapterTasteGate :
    ChapterTasteGate ClosedNormalConsistencyWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closedNormalConsistencyWitnessFromEventFlow
        (closedNormalConsistencyWitnessToEventFlow x) = some x
    exact ClosedNormalConsistencyWitnessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ClosedNormalConsistencyWitnessTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance closedNormalConsistencyWitnessFieldFaithful :
    FieldFaithful ClosedNormalConsistencyWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := closedNormalConsistencyWitnessFields
  field_faithful := ClosedNormalConsistencyWitnessTasteGate_single_carrier_alignment_fields

instance closedNormalConsistencyWitnessNontrivial :
    Nontrivial ClosedNormalConsistencyWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClosedNormalConsistencyWitnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ClosedNormalConsistencyWitnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ClosedNormalConsistencyWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  closedNormalConsistencyWitnessChapterTasteGate

theorem ClosedNormalConsistencyWitnessTasteGate_single_carrier_alignment :
    (forall h : BHist,
      closedNormalConsistencyWitnessDecodeBHist
        (closedNormalConsistencyWitnessEncodeBHist h) = h) ∧
      (forall x : ClosedNormalConsistencyWitnessUp,
        closedNormalConsistencyWitnessFromEventFlow
          (closedNormalConsistencyWitnessToEventFlow x) = some x) ∧
        (forall x y : ClosedNormalConsistencyWitnessUp,
          closedNormalConsistencyWitnessToEventFlow x =
            closedNormalConsistencyWitnessToEventFlow y -> x = y) ∧
          closedNormalConsistencyWitnessEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨ClosedNormalConsistencyWitnessTasteGate_single_carrier_alignment_decode,
      ClosedNormalConsistencyWitnessTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        ClosedNormalConsistencyWitnessTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ClosedNormalConsistencyWitnessUp
