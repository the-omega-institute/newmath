import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedSpaceUp : Type where
  | mk (X R A G W Q E H C P N : BHist) : LocatedSpaceUp
  deriving DecidableEq

def locatedSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedSpaceEncodeBHist h

def locatedSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedSpaceDecodeBHist tail)

private theorem LocatedSpaceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, locatedSpaceDecodeBHist (locatedSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedSpaceFields : LocatedSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedSpaceUp.mk X R A G W Q E H C P N => [X, R, A, G, W, Q, E, H, C, P, N]

def locatedSpaceToEventFlow : LocatedSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedSpaceFields x).map locatedSpaceEncodeBHist

private def locatedSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedSpaceEventAtDefault index rest

def locatedSpaceFromEventFlow : EventFlow → Option LocatedSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (LocatedSpaceUp.mk
        (locatedSpaceDecodeBHist (locatedSpaceEventAtDefault 0 ef))
        (locatedSpaceDecodeBHist (locatedSpaceEventAtDefault 1 ef))
        (locatedSpaceDecodeBHist (locatedSpaceEventAtDefault 2 ef))
        (locatedSpaceDecodeBHist (locatedSpaceEventAtDefault 3 ef))
        (locatedSpaceDecodeBHist (locatedSpaceEventAtDefault 4 ef))
        (locatedSpaceDecodeBHist (locatedSpaceEventAtDefault 5 ef))
        (locatedSpaceDecodeBHist (locatedSpaceEventAtDefault 6 ef))
        (locatedSpaceDecodeBHist (locatedSpaceEventAtDefault 7 ef))
        (locatedSpaceDecodeBHist (locatedSpaceEventAtDefault 8 ef))
        (locatedSpaceDecodeBHist (locatedSpaceEventAtDefault 9 ef))
        (locatedSpaceDecodeBHist (locatedSpaceEventAtDefault 10 ef)))

private theorem LocatedSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedSpaceUp, locatedSpaceFromEventFlow (locatedSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X R A G W Q E H C P N =>
      change
        some
            (LocatedSpaceUp.mk
              (locatedSpaceDecodeBHist (locatedSpaceEncodeBHist X))
              (locatedSpaceDecodeBHist (locatedSpaceEncodeBHist R))
              (locatedSpaceDecodeBHist (locatedSpaceEncodeBHist A))
              (locatedSpaceDecodeBHist (locatedSpaceEncodeBHist G))
              (locatedSpaceDecodeBHist (locatedSpaceEncodeBHist W))
              (locatedSpaceDecodeBHist (locatedSpaceEncodeBHist Q))
              (locatedSpaceDecodeBHist (locatedSpaceEncodeBHist E))
              (locatedSpaceDecodeBHist (locatedSpaceEncodeBHist H))
              (locatedSpaceDecodeBHist (locatedSpaceEncodeBHist C))
              (locatedSpaceDecodeBHist (locatedSpaceEncodeBHist P))
              (locatedSpaceDecodeBHist (locatedSpaceEncodeBHist N))) =
          some (LocatedSpaceUp.mk X R A G W Q E H C P N)
      rw [LocatedSpaceTasteGate_single_carrier_alignment_decode X,
        LocatedSpaceTasteGate_single_carrier_alignment_decode R,
        LocatedSpaceTasteGate_single_carrier_alignment_decode A,
        LocatedSpaceTasteGate_single_carrier_alignment_decode G,
        LocatedSpaceTasteGate_single_carrier_alignment_decode W,
        LocatedSpaceTasteGate_single_carrier_alignment_decode Q,
        LocatedSpaceTasteGate_single_carrier_alignment_decode E,
        LocatedSpaceTasteGate_single_carrier_alignment_decode H,
        LocatedSpaceTasteGate_single_carrier_alignment_decode C,
        LocatedSpaceTasteGate_single_carrier_alignment_decode P,
        LocatedSpaceTasteGate_single_carrier_alignment_decode N]

private theorem LocatedSpaceTasteGate_single_carrier_alignment_injective
    {x y : LocatedSpaceUp} :
    locatedSpaceToEventFlow x = locatedSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedSpaceFromEventFlow (locatedSpaceToEventFlow x) =
        locatedSpaceFromEventFlow (locatedSpaceToEventFlow y) :=
    congrArg locatedSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LocatedSpaceTasteGate_single_carrier_alignment_round_trip y)))

private theorem LocatedSpaceTasteGate_single_carrier_alignment_fields :
    ∀ x y : LocatedSpaceUp, locatedSpaceFields x = locatedSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 R1 A1 G1 W1 Q1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 R2 A2 G2 W2 Q2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance locatedSpaceBHistCarrier : BHistCarrier LocatedSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedSpaceToEventFlow
  fromEventFlow := locatedSpaceFromEventFlow

instance locatedSpaceChapterTasteGate : ChapterTasteGate LocatedSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedSpaceFromEventFlow (locatedSpaceToEventFlow x) = some x
    exact LocatedSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedSpaceTasteGate_single_carrier_alignment_injective heq)

instance locatedSpaceFieldFaithful : FieldFaithful LocatedSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedSpaceFields
  field_faithful := LocatedSpaceTasteGate_single_carrier_alignment_fields

instance locatedSpaceNontrivial : Nontrivial LocatedSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocatedSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedSpaceChapterTasteGate

theorem LocatedSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedSpaceDecodeBHist (locatedSpaceEncodeBHist h) = h) ∧
      locatedSpaceFromEventFlow
          (locatedSpaceToEventFlow
            (LocatedSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)) =
        some
          (LocatedSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact LocatedSpaceTasteGate_single_carrier_alignment_decode
  · exact LocatedSpaceTasteGate_single_carrier_alignment_round_trip
      (LocatedSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)

end BEDC.Derived.LocatedSpaceUp
