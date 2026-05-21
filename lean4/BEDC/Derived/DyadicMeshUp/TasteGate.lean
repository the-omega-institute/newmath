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
      (level cell interval ledger transport routes provenance name : BHist) →
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

private theorem dyadicMeshDecode_encode_bhist :
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

def dyadicMeshToEventFlow : DyadicMeshUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicMeshUp.mk level cell interval ledger transport routes provenance name =>
      [[BMark.b0],
        dyadicMeshEncodeBHist level,
        [BMark.b1, BMark.b0],
        dyadicMeshEncodeBHist cell,
        [BMark.b1, BMark.b1, BMark.b0],
        dyadicMeshEncodeBHist interval,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicMeshEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicMeshEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicMeshEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicMeshEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        dyadicMeshEncodeBHist name]

def dyadicMeshFromEventFlow : EventFlow → Option DyadicMeshUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | level :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | cell :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | interval :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | ledger :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | routes :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | name :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (DyadicMeshUp.mk
                                                                          (dyadicMeshDecodeBHist
                                                                            level)
                                                                          (dyadicMeshDecodeBHist
                                                                            cell)
                                                                          (dyadicMeshDecodeBHist
                                                                            interval)
                                                                          (dyadicMeshDecodeBHist
                                                                            ledger)
                                                                          (dyadicMeshDecodeBHist
                                                                            transport)
                                                                          (dyadicMeshDecodeBHist
                                                                            routes)
                                                                          (dyadicMeshDecodeBHist
                                                                            provenance)
                                                                          (dyadicMeshDecodeBHist
                                                                            name))
                                                                  | _ :: _ => none

private theorem dyadicMesh_round_trip :
    ∀ x : DyadicMeshUp, dyadicMeshFromEventFlow (dyadicMeshToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk level cell interval ledger transport routes provenance name =>
      change
        some
          (DyadicMeshUp.mk
            (dyadicMeshDecodeBHist (dyadicMeshEncodeBHist level))
            (dyadicMeshDecodeBHist (dyadicMeshEncodeBHist cell))
            (dyadicMeshDecodeBHist (dyadicMeshEncodeBHist interval))
            (dyadicMeshDecodeBHist (dyadicMeshEncodeBHist ledger))
            (dyadicMeshDecodeBHist (dyadicMeshEncodeBHist transport))
            (dyadicMeshDecodeBHist (dyadicMeshEncodeBHist routes))
            (dyadicMeshDecodeBHist (dyadicMeshEncodeBHist provenance))
            (dyadicMeshDecodeBHist (dyadicMeshEncodeBHist name))) =
          some
            (DyadicMeshUp.mk level cell interval ledger transport routes provenance name)
      rw [dyadicMeshDecode_encode_bhist level,
        dyadicMeshDecode_encode_bhist cell,
        dyadicMeshDecode_encode_bhist interval,
        dyadicMeshDecode_encode_bhist ledger,
        dyadicMeshDecode_encode_bhist transport,
        dyadicMeshDecode_encode_bhist routes,
        dyadicMeshDecode_encode_bhist provenance,
        dyadicMeshDecode_encode_bhist name]

private theorem dyadicMeshToEventFlow_injective {x y : DyadicMeshUp} :
    dyadicMeshToEventFlow x = dyadicMeshToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicMeshFromEventFlow (dyadicMeshToEventFlow x) =
        dyadicMeshFromEventFlow (dyadicMeshToEventFlow y) :=
    congrArg dyadicMeshFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicMesh_round_trip x).symm
      (Eq.trans hread (dyadicMesh_round_trip y)))

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
  · exact dyadicMeshDecode_encode_bhist
  · constructor
    · exact dyadicMesh_round_trip
    · constructor
      · intro x y heq
        exact dyadicMeshToEventFlow_injective heq
      · rfl

end BEDC.Derived.DyadicMeshUp
