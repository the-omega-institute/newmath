import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCompletionSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedCompletionSpaceUp : Type where
  | mk (P S M E W R D A H C Q N : BHist) : LocatedCompletionSpaceUp
  deriving DecidableEq

def locatedCompletionSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCompletionSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCompletionSpaceEncodeBHist h

def locatedCompletionSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCompletionSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCompletionSpaceDecodeBHist tail)

private theorem LocatedCompletionSpaceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      locatedCompletionSpaceDecodeBHist (locatedCompletionSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedCompletionSpaceFields : LocatedCompletionSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCompletionSpaceUp.mk P S M E W R D A H C Q N => [P, S, M, E, W, R, D, A, H, C, Q, N]

def locatedCompletionSpaceToEventFlow : LocatedCompletionSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedCompletionSpaceFields x).map locatedCompletionSpaceEncodeBHist

private def locatedCompletionSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedCompletionSpaceEventAtDefault index rest

def locatedCompletionSpaceFromEventFlow :
    EventFlow → Option LocatedCompletionSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (LocatedCompletionSpaceUp.mk
          (locatedCompletionSpaceDecodeBHist (locatedCompletionSpaceEventAtDefault 0 ef))
          (locatedCompletionSpaceDecodeBHist (locatedCompletionSpaceEventAtDefault 1 ef))
          (locatedCompletionSpaceDecodeBHist (locatedCompletionSpaceEventAtDefault 2 ef))
          (locatedCompletionSpaceDecodeBHist (locatedCompletionSpaceEventAtDefault 3 ef))
          (locatedCompletionSpaceDecodeBHist (locatedCompletionSpaceEventAtDefault 4 ef))
          (locatedCompletionSpaceDecodeBHist (locatedCompletionSpaceEventAtDefault 5 ef))
          (locatedCompletionSpaceDecodeBHist (locatedCompletionSpaceEventAtDefault 6 ef))
          (locatedCompletionSpaceDecodeBHist (locatedCompletionSpaceEventAtDefault 7 ef))
          (locatedCompletionSpaceDecodeBHist (locatedCompletionSpaceEventAtDefault 8 ef))
          (locatedCompletionSpaceDecodeBHist (locatedCompletionSpaceEventAtDefault 9 ef))
          (locatedCompletionSpaceDecodeBHist (locatedCompletionSpaceEventAtDefault 10 ef))
          (locatedCompletionSpaceDecodeBHist (locatedCompletionSpaceEventAtDefault 11 ef)))

private theorem LocatedCompletionSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedCompletionSpaceUp,
      locatedCompletionSpaceFromEventFlow (locatedCompletionSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk P S M E W R D A H C Q N =>
      change
        some
          (LocatedCompletionSpaceUp.mk
            (locatedCompletionSpaceDecodeBHist (locatedCompletionSpaceEncodeBHist P))
            (locatedCompletionSpaceDecodeBHist (locatedCompletionSpaceEncodeBHist S))
            (locatedCompletionSpaceDecodeBHist (locatedCompletionSpaceEncodeBHist M))
            (locatedCompletionSpaceDecodeBHist (locatedCompletionSpaceEncodeBHist E))
            (locatedCompletionSpaceDecodeBHist (locatedCompletionSpaceEncodeBHist W))
            (locatedCompletionSpaceDecodeBHist (locatedCompletionSpaceEncodeBHist R))
            (locatedCompletionSpaceDecodeBHist (locatedCompletionSpaceEncodeBHist D))
            (locatedCompletionSpaceDecodeBHist (locatedCompletionSpaceEncodeBHist A))
            (locatedCompletionSpaceDecodeBHist (locatedCompletionSpaceEncodeBHist H))
            (locatedCompletionSpaceDecodeBHist (locatedCompletionSpaceEncodeBHist C))
            (locatedCompletionSpaceDecodeBHist (locatedCompletionSpaceEncodeBHist Q))
            (locatedCompletionSpaceDecodeBHist (locatedCompletionSpaceEncodeBHist N))) =
          some (LocatedCompletionSpaceUp.mk P S M E W R D A H C Q N)
      rw [LocatedCompletionSpaceTasteGate_single_carrier_alignment_decode P,
        LocatedCompletionSpaceTasteGate_single_carrier_alignment_decode S,
        LocatedCompletionSpaceTasteGate_single_carrier_alignment_decode M,
        LocatedCompletionSpaceTasteGate_single_carrier_alignment_decode E,
        LocatedCompletionSpaceTasteGate_single_carrier_alignment_decode W,
        LocatedCompletionSpaceTasteGate_single_carrier_alignment_decode R,
        LocatedCompletionSpaceTasteGate_single_carrier_alignment_decode D,
        LocatedCompletionSpaceTasteGate_single_carrier_alignment_decode A,
        LocatedCompletionSpaceTasteGate_single_carrier_alignment_decode H,
        LocatedCompletionSpaceTasteGate_single_carrier_alignment_decode C,
        LocatedCompletionSpaceTasteGate_single_carrier_alignment_decode Q,
        LocatedCompletionSpaceTasteGate_single_carrier_alignment_decode N]

private theorem LocatedCompletionSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedCompletionSpaceUp} :
    locatedCompletionSpaceToEventFlow x = locatedCompletionSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCompletionSpaceFromEventFlow (locatedCompletionSpaceToEventFlow x) =
        locatedCompletionSpaceFromEventFlow (locatedCompletionSpaceToEventFlow y) :=
    congrArg locatedCompletionSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedCompletionSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedCompletionSpaceTasteGate_single_carrier_alignment_round_trip y)))

private theorem LocatedCompletionSpaceTasteGate_single_carrier_alignment_fields :
    ∀ x y : LocatedCompletionSpaceUp,
      locatedCompletionSpaceFields x = locatedCompletionSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk P1 S1 M1 E1 W1 R1 D1 A1 H1 C1 Q1 N1 =>
      cases y with
      | mk P2 S2 M2 E2 W2 R2 D2 A2 H2 C2 Q2 N2 =>
          cases hfields
          rfl

instance locatedCompletionSpaceBHistCarrier :
    BHistCarrier LocatedCompletionSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCompletionSpaceToEventFlow
  fromEventFlow := locatedCompletionSpaceFromEventFlow

instance locatedCompletionSpaceChapterTasteGate :
    ChapterTasteGate LocatedCompletionSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedCompletionSpaceFromEventFlow (locatedCompletionSpaceToEventFlow x) =
      some x
    exact LocatedCompletionSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LocatedCompletionSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance locatedCompletionSpaceFieldFaithful :
    FieldFaithful LocatedCompletionSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedCompletionSpaceFields
  field_faithful := LocatedCompletionSpaceTasteGate_single_carrier_alignment_fields

instance locatedCompletionSpaceNontrivial :
    Nontrivial LocatedCompletionSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedCompletionSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      LocatedCompletionSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocatedCompletionSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedCompletionSpaceChapterTasteGate

theorem LocatedCompletionSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedCompletionSpaceDecodeBHist (locatedCompletionSpaceEncodeBHist h) = h) ∧
      (∀ x : LocatedCompletionSpaceUp,
        locatedCompletionSpaceFromEventFlow (locatedCompletionSpaceToEventFlow x) =
          some x) ∧
        (∀ x y : LocatedCompletionSpaceUp,
          locatedCompletionSpaceToEventFlow x = locatedCompletionSpaceToEventFlow y →
            x = y) ∧
          locatedCompletionSpaceEncodeBHist BHist.Empty = ([] : RawEvent) ∧
            locatedCompletionSpaceEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨LocatedCompletionSpaceTasteGate_single_carrier_alignment_decode,
      LocatedCompletionSpaceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        LocatedCompletionSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl,
      rfl⟩

end BEDC.Derived.LocatedCompletionSpaceUp
