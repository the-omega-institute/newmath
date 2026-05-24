import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyFilterMeetUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyFilterMeetUp : Type where
  | mk :
      (uniformRow filterLeft filterRight basisLeft basisRight refineRow windowRow regularRow
        toleranceRow limitRow sealRow transportRow routeRow provenanceRow certRow : BHist) ->
        CauchyFilterMeetUp
  deriving DecidableEq

def cauchyFilterMeetEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyFilterMeetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyFilterMeetEncodeBHist h

def cauchyFilterMeetDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyFilterMeetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyFilterMeetDecodeBHist tail)

theorem CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyFilterMeetFields : CauchyFilterMeetUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyFilterMeetUp.mk uniformRow filterLeft filterRight basisLeft basisRight refineRow
      windowRow regularRow toleranceRow limitRow sealRow transportRow routeRow provenanceRow
      certRow =>
      [uniformRow, filterLeft, filterRight, basisLeft, basisRight, refineRow, windowRow,
        regularRow, toleranceRow, limitRow, sealRow, transportRow, routeRow, provenanceRow,
        certRow]

def cauchyFilterMeetToEventFlow : CauchyFilterMeetUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyFilterMeetFields x).map cauchyFilterMeetEncodeBHist

def cauchyFilterMeetFromEventFlow : EventFlow -> Option CauchyFilterMeetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | uniformRow :: rest0 =>
      match rest0 with
      | [] => none
      | filterLeft :: rest1 =>
          match rest1 with
          | [] => none
          | filterRight :: rest2 =>
              match rest2 with
              | [] => none
              | basisLeft :: rest3 =>
                  match rest3 with
                  | [] => none
                  | basisRight :: rest4 =>
                      match rest4 with
                      | [] => none
                      | refineRow :: rest5 =>
                          match rest5 with
                          | [] => none
                          | windowRow :: rest6 =>
                              match rest6 with
                              | [] => none
                              | regularRow :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | toleranceRow :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | limitRow :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | sealRow :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transportRow :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | routeRow :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenanceRow :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | certRow :: rest14 =>
                                                              match rest14 with
                                                              | [] =>
                                                                  some
                                                                    (CauchyFilterMeetUp.mk
                                                                      (cauchyFilterMeetDecodeBHist
                                                                        uniformRow)
                                                                      (cauchyFilterMeetDecodeBHist
                                                                        filterLeft)
                                                                      (cauchyFilterMeetDecodeBHist
                                                                        filterRight)
                                                                      (cauchyFilterMeetDecodeBHist
                                                                        basisLeft)
                                                                      (cauchyFilterMeetDecodeBHist
                                                                        basisRight)
                                                                      (cauchyFilterMeetDecodeBHist
                                                                        refineRow)
                                                                      (cauchyFilterMeetDecodeBHist
                                                                        windowRow)
                                                                      (cauchyFilterMeetDecodeBHist
                                                                        regularRow)
                                                                      (cauchyFilterMeetDecodeBHist
                                                                        toleranceRow)
                                                                      (cauchyFilterMeetDecodeBHist
                                                                        limitRow)
                                                                      (cauchyFilterMeetDecodeBHist
                                                                        sealRow)
                                                                      (cauchyFilterMeetDecodeBHist
                                                                        transportRow)
                                                                      (cauchyFilterMeetDecodeBHist
                                                                        routeRow)
                                                                      (cauchyFilterMeetDecodeBHist
                                                                        provenanceRow)
                                                                      (cauchyFilterMeetDecodeBHist
                                                                        certRow))
                                                              | _ :: _ => none

theorem CauchyFilterMeetTasteGate_single_carrier_alignment_round_trip :
    forall x : CauchyFilterMeetUp,
      cauchyFilterMeetFromEventFlow (cauchyFilterMeetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk uniformRow filterLeft filterRight basisLeft basisRight refineRow windowRow regularRow
      toleranceRow limitRow sealRow transportRow routeRow provenanceRow certRow =>
      change
        some
          (CauchyFilterMeetUp.mk
            (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist uniformRow))
            (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist filterLeft))
            (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist filterRight))
            (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist basisLeft))
            (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist basisRight))
            (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist refineRow))
            (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist windowRow))
            (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist regularRow))
            (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist toleranceRow))
            (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist limitRow))
            (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist sealRow))
            (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist transportRow))
            (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist routeRow))
            (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist provenanceRow))
            (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist certRow))) =
          some
            (CauchyFilterMeetUp.mk uniformRow filterLeft filterRight basisLeft basisRight
              refineRow windowRow regularRow toleranceRow limitRow sealRow transportRow routeRow
              provenanceRow certRow)
      rw [CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode uniformRow,
        CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode filterLeft,
        CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode filterRight,
        CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode basisLeft,
        CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode basisRight,
        CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode refineRow,
        CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode windowRow,
        CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode regularRow,
        CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode toleranceRow,
        CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode limitRow,
        CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode sealRow,
        CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode transportRow,
        CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode routeRow,
        CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode provenanceRow,
        CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode certRow]

theorem CauchyFilterMeetTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyFilterMeetUp} :
    cauchyFilterMeetToEventFlow x = cauchyFilterMeetToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyFilterMeetFromEventFlow (cauchyFilterMeetToEventFlow x) =
        cauchyFilterMeetFromEventFlow (cauchyFilterMeetToEventFlow y) :=
    congrArg cauchyFilterMeetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyFilterMeetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyFilterMeetTasteGate_single_carrier_alignment_round_trip y)))

theorem CauchyFilterMeetTasteGate_single_carrier_alignment_field_faithful :
    forall x y : CauchyFilterMeetUp, cauchyFilterMeetFields x = cauchyFilterMeetFields y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk uniformRow₁ filterLeft₁ filterRight₁ basisLeft₁ basisRight₁ refineRow₁ windowRow₁
      regularRow₁ toleranceRow₁ limitRow₁ sealRow₁ transportRow₁ routeRow₁ provenanceRow₁
      certRow₁ =>
      cases y with
      | mk uniformRow₂ filterLeft₂ filterRight₂ basisLeft₂ basisRight₂ refineRow₂ windowRow₂
          regularRow₂ toleranceRow₂ limitRow₂ sealRow₂ transportRow₂ routeRow₂ provenanceRow₂
          certRow₂ =>
          cases hfields
          rfl

instance cauchyFilterMeetBHistCarrier : BHistCarrier CauchyFilterMeetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyFilterMeetToEventFlow
  fromEventFlow := cauchyFilterMeetFromEventFlow

instance cauchyFilterMeetChapterTasteGate : ChapterTasteGate CauchyFilterMeetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x =>
    id (CauchyFilterMeetTasteGate_single_carrier_alignment_round_trip x)
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyFilterMeetTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyFilterMeetFieldFaithful : FieldFaithful CauchyFilterMeetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyFilterMeetFields
  field_faithful := CauchyFilterMeetTasteGate_single_carrier_alignment_field_faithful

instance cauchyFilterMeetNontrivial : BEDC.Meta.TasteGate.Nontrivial CauchyFilterMeetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyFilterMeetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      CauchyFilterMeetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def cauchyFilterMeetTasteGate : ChapterTasteGate CauchyFilterMeetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyFilterMeetChapterTasteGate

theorem CauchyFilterMeetTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyFilterMeetUp) ∧
      Nonempty (FieldFaithful CauchyFilterMeetUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CauchyFilterMeetUp) ∧
          (∀ h : BHist, cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist h) = h) ∧
            (∀ x : CauchyFilterMeetUp,
              cauchyFilterMeetFromEventFlow (cauchyFilterMeetToEventFlow x) = some x) ∧
              (∀ x y : CauchyFilterMeetUp,
                cauchyFilterMeetToEventFlow x = cauchyFilterMeetToEventFlow y -> x = y) ∧
                cauchyFilterMeetEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨cauchyFilterMeetChapterTasteGate⟩
  · constructor
    · exact ⟨cauchyFilterMeetFieldFaithful⟩
    · constructor
      · exact ⟨cauchyFilterMeetNontrivial⟩
      · constructor
        · exact CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact CauchyFilterMeetTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact CauchyFilterMeetTasteGate_single_carrier_alignment_toEventFlow_injective heq
            · rfl

end BEDC.Derived.CauchyFilterMeetUp.TasteGate
