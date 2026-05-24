import BEDC.Derived.DyadicMeshUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicMeshUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicMeshUp : Type where
  | mk :
      (level cellIndex interval enclosure handoff consumer provenance nameCert : BHist) →
        DyadicMeshUp
  deriving DecidableEq

def dyadicMeshEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicMeshEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicMeshEncodeBHist h

def dyadicMeshDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicMeshDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicMeshDecodeBHist tail)

private theorem dyadicMesh_decode_encode :
    ∀ h : BHist, dyadicMeshDecodeBHist (dyadicMeshEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def dyadicMeshFields : DyadicMeshUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | DyadicMeshUp.mk level cellIndex interval enclosure handoff consumer provenance nameCert =>
      [level, cellIndex, interval, enclosure, handoff, consumer, provenance, nameCert]

def dyadicMeshToEventFlow : DyadicMeshUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (dyadicMeshFields x).map dyadicMeshEncodeBHist

def dyadicMeshFromEventFlow : EventFlow → Option DyadicMeshUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    match ef with
    | level :: rest1 =>
        match rest1 with
        | cellIndex :: rest2 =>
            match rest2 with
            | interval :: rest3 =>
                match rest3 with
                | enclosure :: rest4 =>
                    match rest4 with
                    | handoff :: rest5 =>
                        match rest5 with
                        | consumer :: rest6 =>
                            match rest6 with
                            | provenance :: rest7 =>
                                match rest7 with
                                | nameCert :: rest8 =>
                                    match rest8 with
                                    | [] =>
                                        some
                                          (DyadicMeshUp.mk
                                            (dyadicMeshDecodeBHist level)
                                            (dyadicMeshDecodeBHist cellIndex)
                                            (dyadicMeshDecodeBHist interval)
                                            (dyadicMeshDecodeBHist enclosure)
                                            (dyadicMeshDecodeBHist handoff)
                                            (dyadicMeshDecodeBHist consumer)
                                            (dyadicMeshDecodeBHist provenance)
                                            (dyadicMeshDecodeBHist nameCert))
                                    | _ :: _ => none
                                | [] => none
                            | [] => none
                        | [] => none
                    | [] => none
                | [] => none
            | [] => none
        | [] => none
    | [] => none

private theorem dyadicMesh_round_trip :
    ∀ x : DyadicMeshUp, dyadicMeshFromEventFlow (dyadicMeshToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk level cellIndex interval enclosure handoff consumer provenance nameCert =>
      change
        some
            (DyadicMeshUp.mk
              (dyadicMeshDecodeBHist (dyadicMeshEncodeBHist level))
              (dyadicMeshDecodeBHist (dyadicMeshEncodeBHist cellIndex))
              (dyadicMeshDecodeBHist (dyadicMeshEncodeBHist interval))
              (dyadicMeshDecodeBHist (dyadicMeshEncodeBHist enclosure))
              (dyadicMeshDecodeBHist (dyadicMeshEncodeBHist handoff))
              (dyadicMeshDecodeBHist (dyadicMeshEncodeBHist consumer))
              (dyadicMeshDecodeBHist (dyadicMeshEncodeBHist provenance))
              (dyadicMeshDecodeBHist (dyadicMeshEncodeBHist nameCert))) =
          some
            (DyadicMeshUp.mk level cellIndex interval enclosure handoff consumer provenance
              nameCert)
      rw [dyadicMesh_decode_encode level]
      rw [dyadicMesh_decode_encode cellIndex]
      rw [dyadicMesh_decode_encode interval]
      rw [dyadicMesh_decode_encode enclosure]
      rw [dyadicMesh_decode_encode handoff]
      rw [dyadicMesh_decode_encode consumer]
      rw [dyadicMesh_decode_encode provenance]
      rw [dyadicMesh_decode_encode nameCert]

private theorem dyadicMeshToEventFlow_injective {x y : DyadicMeshUp} :
    dyadicMeshToEventFlow x = dyadicMeshToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = dyadicMeshFromEventFlow (dyadicMeshToEventFlow x) :=
        (dyadicMesh_round_trip x).symm
      _ = dyadicMeshFromEventFlow (dyadicMeshToEventFlow y) :=
        congrArg dyadicMeshFromEventFlow hxy
      _ = some y := dyadicMesh_round_trip y
  exact Option.some.inj optionEq

instance dyadicMeshBHistCarrier : BHistCarrier DyadicMeshUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicMeshToEventFlow
  fromEventFlow := dyadicMeshFromEventFlow

instance dyadicMeshChapterTasteGate : ChapterTasteGate DyadicMeshUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicMeshFromEventFlow (dyadicMeshToEventFlow x) = some x
    exact dyadicMesh_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicMeshToEventFlow_injective heq)

def taste_gate : ChapterTasteGate DyadicMeshUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicMeshChapterTasteGate

theorem DyadicMeshTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicMeshDecodeBHist (dyadicMeshEncodeBHist h) = h) ∧
      (∀ x : DyadicMeshUp,
        dyadicMeshFromEventFlow (dyadicMeshToEventFlow x) = some x) ∧
        (∀ x y : DyadicMeshUp,
          dyadicMeshToEventFlow x = dyadicMeshToEventFlow y → x = y) ∧
          dyadicMeshEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact dyadicMesh_decode_encode
  · constructor
    · exact dyadicMesh_round_trip
    · constructor
      · intro x y heq
        exact dyadicMeshToEventFlow_injective heq
      · rfl

theorem dyadicMeshTasteGate_single_carrier_alignment :
    (∀ x : DyadicMeshUp, dyadicMeshFromEventFlow (dyadicMeshToEventFlow x) = some x) ∧
    (∀ {x y : DyadicMeshUp}, dyadicMeshToEventFlow x = dyadicMeshToEventFlow y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact dyadicMesh_round_trip
  · intro x y hxy
    exact dyadicMeshToEventFlow_injective hxy

end BEDC.Derived.DyadicMeshUp
