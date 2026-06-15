import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PointedMetricSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PointedMetricSpaceUp : Type where
  | mk (M b D S R E H C P0 N : BHist) : PointedMetricSpaceUp
  deriving DecidableEq

def pointedMetricSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: pointedMetricSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: pointedMetricSpaceEncodeBHist h

def pointedMetricSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (pointedMetricSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (pointedMetricSpaceDecodeBHist tail)

private theorem pointedMetricSpace_decode_encode_bhist :
    ∀ h : BHist, pointedMetricSpaceDecodeBHist (pointedMetricSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def pointedMetricSpaceFields : PointedMetricSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PointedMetricSpaceUp.mk M b D S R E H C P0 N => [M, b, D, S, R, E, H, C, P0, N]

def pointedMetricSpaceToEventFlow : PointedMetricSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (pointedMetricSpaceFields x).map pointedMetricSpaceEncodeBHist

def pointedMetricSpaceSplitEventFlow :
    EventFlow →
      Option
        (RawEvent × RawEvent × RawEvent × RawEvent × RawEvent × RawEvent × RawEvent ×
          RawEvent × RawEvent × RawEvent)
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | m :: r0 =>
    match r0 with
    | [] => none
    | b :: r1 =>
      match r1 with
      | [] => none
      | d :: r2 =>
        match r2 with
        | [] => none
        | s :: r3 =>
          match r3 with
          | [] => none
          | r :: r4 =>
            match r4 with
            | [] => none
            | e :: r5 =>
              match r5 with
              | [] => none
              | h :: r6 =>
                match r6 with
                | [] => none
                | c :: r7 =>
                  match r7 with
                  | [] => none
                  | p0 :: r8 =>
                    match r8 with
                    | [] => none
                    | n :: r9 =>
                      match r9 with
                      | [] =>
                          some (m, b, d, s, r, e, h, c, p0, n)
                      | _ :: _ => none

def pointedMetricSpaceFromEventFlow (ef : EventFlow) : Option PointedMetricSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match pointedMetricSpaceSplitEventFlow ef with
  | some (m, b, d, s, r, e, h, c, p0, n) =>
      some
        (PointedMetricSpaceUp.mk
          (pointedMetricSpaceDecodeBHist m)
          (pointedMetricSpaceDecodeBHist b)
          (pointedMetricSpaceDecodeBHist d)
          (pointedMetricSpaceDecodeBHist s)
          (pointedMetricSpaceDecodeBHist r)
          (pointedMetricSpaceDecodeBHist e)
          (pointedMetricSpaceDecodeBHist h)
          (pointedMetricSpaceDecodeBHist c)
          (pointedMetricSpaceDecodeBHist p0)
          (pointedMetricSpaceDecodeBHist n))
  | none => none

private theorem pointedMetricSpace_round_trip :
    ∀ x : PointedMetricSpaceUp,
      pointedMetricSpaceFromEventFlow (pointedMetricSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M b D S R E H C P0 N =>
      change
        some
          (PointedMetricSpaceUp.mk
            (pointedMetricSpaceDecodeBHist (pointedMetricSpaceEncodeBHist M))
            (pointedMetricSpaceDecodeBHist (pointedMetricSpaceEncodeBHist b))
            (pointedMetricSpaceDecodeBHist (pointedMetricSpaceEncodeBHist D))
            (pointedMetricSpaceDecodeBHist (pointedMetricSpaceEncodeBHist S))
            (pointedMetricSpaceDecodeBHist (pointedMetricSpaceEncodeBHist R))
            (pointedMetricSpaceDecodeBHist (pointedMetricSpaceEncodeBHist E))
            (pointedMetricSpaceDecodeBHist (pointedMetricSpaceEncodeBHist H))
            (pointedMetricSpaceDecodeBHist (pointedMetricSpaceEncodeBHist C))
            (pointedMetricSpaceDecodeBHist (pointedMetricSpaceEncodeBHist P0))
            (pointedMetricSpaceDecodeBHist (pointedMetricSpaceEncodeBHist N))) =
          some (PointedMetricSpaceUp.mk M b D S R E H C P0 N)
      rw [pointedMetricSpace_decode_encode_bhist M, pointedMetricSpace_decode_encode_bhist b,
        pointedMetricSpace_decode_encode_bhist D, pointedMetricSpace_decode_encode_bhist S,
        pointedMetricSpace_decode_encode_bhist R, pointedMetricSpace_decode_encode_bhist E,
        pointedMetricSpace_decode_encode_bhist H, pointedMetricSpace_decode_encode_bhist C,
        pointedMetricSpace_decode_encode_bhist P0, pointedMetricSpace_decode_encode_bhist N]

private theorem pointedMetricSpaceToEventFlow_injective {x y : PointedMetricSpaceUp} :
    pointedMetricSpaceToEventFlow x = pointedMetricSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      pointedMetricSpaceFromEventFlow (pointedMetricSpaceToEventFlow x) =
        pointedMetricSpaceFromEventFlow (pointedMetricSpaceToEventFlow y) :=
    congrArg pointedMetricSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (pointedMetricSpace_round_trip x).symm
      (Eq.trans hread (pointedMetricSpace_round_trip y)))

private theorem pointedMetricSpace_fields_faithful :
    ∀ x y : PointedMetricSpaceUp,
      pointedMetricSpaceFields x = pointedMetricSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 b1 D1 S1 R1 E1 H1 C1 P01 N1 =>
      cases y with
      | mk M2 b2 D2 S2 R2 E2 H2 C2 P02 N2 =>
          cases hfields
          rfl

instance pointedMetricSpaceBHistCarrier : BHistCarrier PointedMetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := pointedMetricSpaceToEventFlow
  fromEventFlow := pointedMetricSpaceFromEventFlow

instance pointedMetricSpaceChapterTasteGate : ChapterTasteGate PointedMetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change pointedMetricSpaceFromEventFlow (pointedMetricSpaceToEventFlow x) = some x
    exact pointedMetricSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (pointedMetricSpaceToEventFlow_injective heq)

instance pointedMetricSpaceFieldFaithful : FieldFaithful PointedMetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := pointedMetricSpaceFields
  field_faithful := pointedMetricSpace_fields_faithful

instance pointedMetricSpaceNontrivial :
    BEDC.Meta.TasteGate.Nontrivial PointedMetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PointedMetricSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PointedMetricSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem PointedMetricSpaceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate PointedMetricSpaceUp) ∧
      Nonempty (FieldFaithful PointedMetricSpaceUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial PointedMetricSpaceUp) ∧
          (∀ h : BHist,
            pointedMetricSpaceDecodeBHist (pointedMetricSpaceEncodeBHist h) = h) ∧
            (∀ x : PointedMetricSpaceUp,
              pointedMetricSpaceFromEventFlow (pointedMetricSpaceToEventFlow x) = some x) ∧
              (∀ x y : PointedMetricSpaceUp,
                pointedMetricSpaceToEventFlow x = pointedMetricSpaceToEventFlow y → x = y) ∧
                pointedMetricSpaceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨pointedMetricSpaceChapterTasteGate⟩
  · constructor
    · exact ⟨pointedMetricSpaceFieldFaithful⟩
    · constructor
      · exact ⟨pointedMetricSpaceNontrivial⟩
      · constructor
        · exact pointedMetricSpace_decode_encode_bhist
        · constructor
          · exact pointedMetricSpace_round_trip
          · constructor
            · intro x y heq
              exact pointedMetricSpaceToEventFlow_injective heq
            · rfl

end BEDC.Derived.PointedMetricSpaceUp
