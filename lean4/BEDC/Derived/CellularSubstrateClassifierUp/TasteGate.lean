import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CellularSubstrateClassifierUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CellularSubstrateClassifierUp : Type where
  | mk (B E O F H C P N : BHist) : CellularSubstrateClassifierUp
  deriving DecidableEq

private def cellularSubstrateClassifierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cellularSubstrateClassifierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cellularSubstrateClassifierEncodeBHist h

private def cellularSubstrateClassifierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cellularSubstrateClassifierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cellularSubstrateClassifierDecodeBHist tail)

private theorem cellularSubstrateClassifier_decode_encode_bhist :
    ∀ h : BHist,
      cellularSubstrateClassifierDecodeBHist
        (cellularSubstrateClassifierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def cellularSubstrateClassifierToEventFlow :
    CellularSubstrateClassifierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CellularSubstrateClassifierUp.mk B E O F H C P N =>
      [[BMark.b0], cellularSubstrateClassifierEncodeBHist B,
        [BMark.b1, BMark.b0], cellularSubstrateClassifierEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b0], cellularSubstrateClassifierEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularSubstrateClassifierEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularSubstrateClassifierEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularSubstrateClassifierEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularSubstrateClassifierEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cellularSubstrateClassifierEncodeBHist N]

private def cellularSubstrateClassifierFromEventFlow :
    EventFlow → Option CellularSubstrateClassifierUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | B :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | E :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | O :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | F :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | H :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | C :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | P :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | N :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (CellularSubstrateClassifierUp.mk
                                                                          (cellularSubstrateClassifierDecodeBHist
                                                                            B)
                                                                          (cellularSubstrateClassifierDecodeBHist
                                                                            E)
                                                                          (cellularSubstrateClassifierDecodeBHist
                                                                            O)
                                                                          (cellularSubstrateClassifierDecodeBHist
                                                                            F)
                                                                          (cellularSubstrateClassifierDecodeBHist
                                                                            H)
                                                                          (cellularSubstrateClassifierDecodeBHist
                                                                            C)
                                                                          (cellularSubstrateClassifierDecodeBHist
                                                                            P)
                                                                          (cellularSubstrateClassifierDecodeBHist
                                                                            N))
                                                                  | _ :: _ => none

private theorem cellularSubstrateClassifier_round_trip :
    ∀ x : CellularSubstrateClassifierUp,
      cellularSubstrateClassifierFromEventFlow
        (cellularSubstrateClassifierToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B E O F H C P N =>
      change
        some
          (CellularSubstrateClassifierUp.mk
            (cellularSubstrateClassifierDecodeBHist
              (cellularSubstrateClassifierEncodeBHist B))
            (cellularSubstrateClassifierDecodeBHist
              (cellularSubstrateClassifierEncodeBHist E))
            (cellularSubstrateClassifierDecodeBHist
              (cellularSubstrateClassifierEncodeBHist O))
            (cellularSubstrateClassifierDecodeBHist
              (cellularSubstrateClassifierEncodeBHist F))
            (cellularSubstrateClassifierDecodeBHist
              (cellularSubstrateClassifierEncodeBHist H))
            (cellularSubstrateClassifierDecodeBHist
              (cellularSubstrateClassifierEncodeBHist C))
            (cellularSubstrateClassifierDecodeBHist
              (cellularSubstrateClassifierEncodeBHist P))
            (cellularSubstrateClassifierDecodeBHist
              (cellularSubstrateClassifierEncodeBHist N))) =
          some (CellularSubstrateClassifierUp.mk B E O F H C P N)
      rw [cellularSubstrateClassifier_decode_encode_bhist B,
        cellularSubstrateClassifier_decode_encode_bhist E,
        cellularSubstrateClassifier_decode_encode_bhist O,
        cellularSubstrateClassifier_decode_encode_bhist F,
        cellularSubstrateClassifier_decode_encode_bhist H,
        cellularSubstrateClassifier_decode_encode_bhist C,
        cellularSubstrateClassifier_decode_encode_bhist P,
        cellularSubstrateClassifier_decode_encode_bhist N]

private theorem cellularSubstrateClassifierToEventFlow_injective
    {x y : CellularSubstrateClassifierUp} :
    cellularSubstrateClassifierToEventFlow x =
      cellularSubstrateClassifierToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cellularSubstrateClassifierFromEventFlow
          (cellularSubstrateClassifierToEventFlow x) =
        cellularSubstrateClassifierFromEventFlow
          (cellularSubstrateClassifierToEventFlow y) :=
    congrArg cellularSubstrateClassifierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cellularSubstrateClassifier_round_trip x).symm
      (Eq.trans hread (cellularSubstrateClassifier_round_trip y)))

private def cellularSubstrateClassifierFields :
    CellularSubstrateClassifierUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CellularSubstrateClassifierUp.mk B E O F H C P N => [B, E, O, F, H, C, P, N]

private theorem cellularSubstrateClassifier_field_faithful :
    ∀ x y : CellularSubstrateClassifierUp,
      cellularSubstrateClassifierFields x = cellularSubstrateClassifierFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B E O F H C P N =>
      cases y with
      | mk B' E' O' F' H' C' P' N' =>
          cases hfields
          rfl

instance cellularSubstrateClassifierBHistCarrier :
    BHistCarrier CellularSubstrateClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cellularSubstrateClassifierToEventFlow
  fromEventFlow := cellularSubstrateClassifierFromEventFlow

instance cellularSubstrateClassifierChapterTasteGate :
    ChapterTasteGate CellularSubstrateClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cellularSubstrateClassifierFromEventFlow
        (cellularSubstrateClassifierToEventFlow x) = some x
    exact cellularSubstrateClassifier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cellularSubstrateClassifierToEventFlow_injective heq)

instance cellularSubstrateClassifierFieldFaithful :
    FieldFaithful CellularSubstrateClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cellularSubstrateClassifierFields
  field_faithful := cellularSubstrateClassifier_field_faithful

instance cellularSubstrateClassifierNontrivial :
    Nontrivial CellularSubstrateClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CellularSubstrateClassifierUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CellularSubstrateClassifierUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CellularSubstrateClassifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cellularSubstrateClassifierChapterTasteGate

theorem CellularSubstrateClassifierTasteGate_single_carrier_alignment :
    (∀ x : CellularSubstrateClassifierUp,
      cellularSubstrateClassifierFromEventFlow
        (cellularSubstrateClassifierToEventFlow x) = some x) ∧
      (∀ x y : CellularSubstrateClassifierUp,
        cellularSubstrateClassifierToEventFlow x =
          cellularSubstrateClassifierToEventFlow y → x = y) ∧
      cellularSubstrateClassifierEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨cellularSubstrateClassifier_round_trip,
      fun _ _ => cellularSubstrateClassifierToEventFlow_injective, rfl⟩

end BEDC.Derived.CellularSubstrateClassifierUp.TasteGate

namespace BEDC.Derived.CellularSubstrateClassifierUp

def taste_gate :
    BEDC.Meta.TasteGate.ChapterTasteGate TasteGate.CellularSubstrateClassifierUp :=
  TasteGate.taste_gate

end BEDC.Derived.CellularSubstrateClassifierUp
