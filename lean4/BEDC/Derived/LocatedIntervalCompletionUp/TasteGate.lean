import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedIntervalCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedIntervalCompletionUp : Type where
  | mk (E0 E1 D W Q M R H C P N : BHist) : LocatedIntervalCompletionUp
  deriving DecidableEq

def locatedIntervalCompletionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedIntervalCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedIntervalCompletionEncodeBHist h

def locatedIntervalCompletionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedIntervalCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedIntervalCompletionDecodeBHist tail)

private theorem LocatedIntervalCompletionTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedIntervalCompletionFields : LocatedIntervalCompletionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedIntervalCompletionUp.mk E0 E1 D W Q M R H C P N =>
      [E0, E1, D, W, Q, M, R, H, C, P, N]

def locatedIntervalCompletionToEventFlow : LocatedIntervalCompletionUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (locatedIntervalCompletionFields x).map locatedIntervalCompletionEncodeBHist

private def locatedIntervalCompletionEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedIntervalCompletionEventAtDefault index rest

def locatedIntervalCompletionFromEventFlow
    (ef : EventFlow) : Option LocatedIntervalCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedIntervalCompletionUp.mk
      (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEventAtDefault 0 ef))
      (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEventAtDefault 1 ef))
      (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEventAtDefault 2 ef))
      (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEventAtDefault 3 ef))
      (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEventAtDefault 4 ef))
      (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEventAtDefault 5 ef))
      (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEventAtDefault 6 ef))
      (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEventAtDefault 7 ef))
      (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEventAtDefault 8 ef))
      (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEventAtDefault 9 ef))
      (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEventAtDefault 10 ef)))

private theorem LocatedIntervalCompletionTasteGate_single_carrier_alignment_round_trip :
    forall x : LocatedIntervalCompletionUp,
      locatedIntervalCompletionFromEventFlow (locatedIntervalCompletionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E0 E1 D W Q M R H C P N =>
      change
        some
          (LocatedIntervalCompletionUp.mk
            (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEncodeBHist E0))
            (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEncodeBHist E1))
            (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEncodeBHist D))
            (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEncodeBHist W))
            (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEncodeBHist Q))
            (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEncodeBHist M))
            (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEncodeBHist R))
            (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEncodeBHist H))
            (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEncodeBHist C))
            (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEncodeBHist P))
            (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEncodeBHist N))) =
          some (LocatedIntervalCompletionUp.mk E0 E1 D W Q M R H C P N)
      rw [LocatedIntervalCompletionTasteGate_single_carrier_alignment_decode E0,
        LocatedIntervalCompletionTasteGate_single_carrier_alignment_decode E1,
        LocatedIntervalCompletionTasteGate_single_carrier_alignment_decode D,
        LocatedIntervalCompletionTasteGate_single_carrier_alignment_decode W,
        LocatedIntervalCompletionTasteGate_single_carrier_alignment_decode Q,
        LocatedIntervalCompletionTasteGate_single_carrier_alignment_decode M,
        LocatedIntervalCompletionTasteGate_single_carrier_alignment_decode R,
        LocatedIntervalCompletionTasteGate_single_carrier_alignment_decode H,
        LocatedIntervalCompletionTasteGate_single_carrier_alignment_decode C,
        LocatedIntervalCompletionTasteGate_single_carrier_alignment_decode P,
        LocatedIntervalCompletionTasteGate_single_carrier_alignment_decode N]

private theorem LocatedIntervalCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedIntervalCompletionUp} :
    locatedIntervalCompletionToEventFlow x = locatedIntervalCompletionToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedIntervalCompletionFromEventFlow (locatedIntervalCompletionToEventFlow x) =
        locatedIntervalCompletionFromEventFlow (locatedIntervalCompletionToEventFlow y) :=
    congrArg locatedIntervalCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedIntervalCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedIntervalCompletionTasteGate_single_carrier_alignment_round_trip y)))

private theorem LocatedIntervalCompletionTasteGate_single_carrier_alignment_fields :
    forall x y : LocatedIntervalCompletionUp,
      locatedIntervalCompletionFields x = locatedIntervalCompletionFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk E01 E11 D1 W1 Q1 M1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk E02 E12 D2 W2 Q2 M2 R2 H2 C2 P2 N2 =>
          cases h
          rfl

instance locatedIntervalCompletionBHistCarrier : BHistCarrier LocatedIntervalCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedIntervalCompletionToEventFlow
  fromEventFlow := locatedIntervalCompletionFromEventFlow

instance locatedIntervalCompletionChapterTasteGate :
    ChapterTasteGate LocatedIntervalCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedIntervalCompletionFromEventFlow (locatedIntervalCompletionToEventFlow x) = some x
    exact LocatedIntervalCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LocatedIntervalCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance locatedIntervalCompletionFieldFaithful : FieldFaithful LocatedIntervalCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedIntervalCompletionFields
  field_faithful := LocatedIntervalCompletionTasteGate_single_carrier_alignment_fields

def taste_gate : ChapterTasteGate LocatedIntervalCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedIntervalCompletionChapterTasteGate

theorem LocatedIntervalCompletionTasteGate_single_carrier_alignment :
    (forall h : BHist,
      locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEncodeBHist h) = h) ∧
      (forall x : LocatedIntervalCompletionUp,
        locatedIntervalCompletionFromEventFlow (locatedIntervalCompletionToEventFlow x) =
          some x) ∧
      (forall x y : LocatedIntervalCompletionUp,
        locatedIntervalCompletionToEventFlow x = locatedIntervalCompletionToEventFlow y ->
          x = y) ∧
      (forall x y : LocatedIntervalCompletionUp,
        locatedIntervalCompletionFields x = locatedIntervalCompletionFields y -> x = y) ∧
      locatedIntervalCompletionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨LocatedIntervalCompletionTasteGate_single_carrier_alignment_decode,
      LocatedIntervalCompletionTasteGate_single_carrier_alignment_round_trip,
      fun _ _ h =>
        LocatedIntervalCompletionTasteGate_single_carrier_alignment_toEventFlow_injective h,
      LocatedIntervalCompletionTasteGate_single_carrier_alignment_fields,
      rfl⟩

end BEDC.Derived.LocatedIntervalCompletionUp
