import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PointedGromovHausdorffUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PointedGromovHausdorffUp : Type where
  | mk (X Y x0 y0 KX KY R D B H Q U T C P N : BHist) : PointedGromovHausdorffUp
  deriving DecidableEq

def pointedGromovHausdorffEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: pointedGromovHausdorffEncodeBHist h
  | BHist.e1 h => BMark.b1 :: pointedGromovHausdorffEncodeBHist h

def pointedGromovHausdorffDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (pointedGromovHausdorffDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (pointedGromovHausdorffDecodeBHist tail)

private theorem PointedGromovHausdorffTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def pointedGromovHausdorffFields : PointedGromovHausdorffUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PointedGromovHausdorffUp.mk X Y x0 y0 KX KY R D B H Q U T C P N =>
      [X, Y, x0, y0, KX, KY, R, D, B, H, Q, U, T, C, P, N]

def pointedGromovHausdorffToEventFlow : PointedGromovHausdorffUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (pointedGromovHausdorffFields x).map pointedGromovHausdorffEncodeBHist

private def pointedGromovHausdorffEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => pointedGromovHausdorffEventAtDefault index rest

def pointedGromovHausdorffFromEventFlow
    (ef : EventFlow) : Option PointedGromovHausdorffUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PointedGromovHausdorffUp.mk
      (pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEventAtDefault 0 ef))
      (pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEventAtDefault 1 ef))
      (pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEventAtDefault 2 ef))
      (pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEventAtDefault 3 ef))
      (pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEventAtDefault 4 ef))
      (pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEventAtDefault 5 ef))
      (pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEventAtDefault 6 ef))
      (pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEventAtDefault 7 ef))
      (pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEventAtDefault 8 ef))
      (pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEventAtDefault 9 ef))
      (pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEventAtDefault 10 ef))
      (pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEventAtDefault 11 ef))
      (pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEventAtDefault 12 ef))
      (pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEventAtDefault 13 ef))
      (pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEventAtDefault 14 ef))
      (pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEventAtDefault 15 ef)))

private theorem PointedGromovHausdorffTasteGate_single_carrier_alignment_round_trip :
    forall x : PointedGromovHausdorffUp,
      pointedGromovHausdorffFromEventFlow (pointedGromovHausdorffToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y x0 y0 KX KY R D B H Q U T C P N =>
      change
        some
          (PointedGromovHausdorffUp.mk
            (pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEncodeBHist X))
            (pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEncodeBHist Y))
            (pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEncodeBHist x0))
            (pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEncodeBHist y0))
            (pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEncodeBHist KX))
            (pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEncodeBHist KY))
            (pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEncodeBHist R))
            (pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEncodeBHist D))
            (pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEncodeBHist B))
            (pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEncodeBHist H))
            (pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEncodeBHist Q))
            (pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEncodeBHist U))
            (pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEncodeBHist T))
            (pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEncodeBHist C))
            (pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEncodeBHist P))
            (pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEncodeBHist N))) =
          some (PointedGromovHausdorffUp.mk X Y x0 y0 KX KY R D B H Q U T C P N)
      rw [PointedGromovHausdorffTasteGate_single_carrier_alignment_decode X,
        PointedGromovHausdorffTasteGate_single_carrier_alignment_decode Y,
        PointedGromovHausdorffTasteGate_single_carrier_alignment_decode x0,
        PointedGromovHausdorffTasteGate_single_carrier_alignment_decode y0,
        PointedGromovHausdorffTasteGate_single_carrier_alignment_decode KX,
        PointedGromovHausdorffTasteGate_single_carrier_alignment_decode KY,
        PointedGromovHausdorffTasteGate_single_carrier_alignment_decode R,
        PointedGromovHausdorffTasteGate_single_carrier_alignment_decode D,
        PointedGromovHausdorffTasteGate_single_carrier_alignment_decode B,
        PointedGromovHausdorffTasteGate_single_carrier_alignment_decode H,
        PointedGromovHausdorffTasteGate_single_carrier_alignment_decode Q,
        PointedGromovHausdorffTasteGate_single_carrier_alignment_decode U,
        PointedGromovHausdorffTasteGate_single_carrier_alignment_decode T,
        PointedGromovHausdorffTasteGate_single_carrier_alignment_decode C,
        PointedGromovHausdorffTasteGate_single_carrier_alignment_decode P,
        PointedGromovHausdorffTasteGate_single_carrier_alignment_decode N]

private theorem PointedGromovHausdorffTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PointedGromovHausdorffUp} :
    pointedGromovHausdorffToEventFlow x = pointedGromovHausdorffToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      pointedGromovHausdorffFromEventFlow (pointedGromovHausdorffToEventFlow x) =
        pointedGromovHausdorffFromEventFlow (pointedGromovHausdorffToEventFlow y) :=
    congrArg pointedGromovHausdorffFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PointedGromovHausdorffTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PointedGromovHausdorffTasteGate_single_carrier_alignment_round_trip y)))

private theorem PointedGromovHausdorffTasteGate_single_carrier_alignment_fields :
    forall x y : PointedGromovHausdorffUp,
      pointedGromovHausdorffFields x = pointedGromovHausdorffFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 Y1 x01 y01 KX1 KY1 R1 D1 B1 H1 Q1 U1 T1 C1 P1 N1 =>
      cases y with
      | mk X2 Y2 x02 y02 KX2 KY2 R2 D2 B2 H2 Q2 U2 T2 C2 P2 N2 =>
          cases hfields
          rfl

instance pointedGromovHausdorffBHistCarrier : BHistCarrier PointedGromovHausdorffUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := pointedGromovHausdorffToEventFlow
  fromEventFlow := pointedGromovHausdorffFromEventFlow

instance pointedGromovHausdorffChapterTasteGate :
    ChapterTasteGate PointedGromovHausdorffUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change pointedGromovHausdorffFromEventFlow (pointedGromovHausdorffToEventFlow x) = some x
    exact PointedGromovHausdorffTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PointedGromovHausdorffTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance pointedGromovHausdorffFieldFaithful : FieldFaithful PointedGromovHausdorffUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := pointedGromovHausdorffFields
  field_faithful := PointedGromovHausdorffTasteGate_single_carrier_alignment_fields

instance pointedGromovHausdorffNontrivial :
    BEDC.Meta.TasteGate.Nontrivial PointedGromovHausdorffUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PointedGromovHausdorffUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PointedGromovHausdorffUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem PointedGromovHausdorffTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate PointedGromovHausdorffUp) ∧
      Nonempty (FieldFaithful PointedGromovHausdorffUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial PointedGromovHausdorffUp) ∧
      (∀ h : BHist,
        pointedGromovHausdorffDecodeBHist (pointedGromovHausdorffEncodeBHist h) = h) ∧
      (∀ x : PointedGromovHausdorffUp,
        pointedGromovHausdorffFromEventFlow (pointedGromovHausdorffToEventFlow x) = some x) ∧
      (∀ x y : PointedGromovHausdorffUp,
        pointedGromovHausdorffToEventFlow x = pointedGromovHausdorffToEventFlow y -> x = y) ∧
      pointedGromovHausdorffEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨pointedGromovHausdorffChapterTasteGate⟩,
      ⟨pointedGromovHausdorffFieldFaithful⟩,
      ⟨pointedGromovHausdorffNontrivial⟩,
      PointedGromovHausdorffTasteGate_single_carrier_alignment_decode,
      PointedGromovHausdorffTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => PointedGromovHausdorffTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.PointedGromovHausdorffUp.TasteGate
