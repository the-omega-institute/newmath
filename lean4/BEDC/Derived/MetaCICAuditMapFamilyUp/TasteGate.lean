import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICAuditMapFamilyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICAuditMapFamilyUp : Type where
  | mk :
      (localMaps synthesisRows obstructionRows frontierRows dependencyLedger transports
        routes provenance localName : BHist) →
      MetaCICAuditMapFamilyUp
  deriving DecidableEq

def metaCICAuditMapFamilyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICAuditMapFamilyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICAuditMapFamilyEncodeBHist h

def metaCICAuditMapFamilyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICAuditMapFamilyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICAuditMapFamilyDecodeBHist tail)

private theorem metaCICAuditMapFamilyDecode_encode_bhist :
    ∀ h : BHist, metaCICAuditMapFamilyDecodeBHist
      (metaCICAuditMapFamilyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metaCICAuditMapFamilyFields : MetaCICAuditMapFamilyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICAuditMapFamilyUp.mk localMaps synthesisRows obstructionRows frontierRows
      dependencyLedger transports routes provenance localName =>
      [localMaps, synthesisRows, obstructionRows, frontierRows, dependencyLedger,
        transports, routes, provenance, localName]

def metaCICAuditMapFamilyToEventFlow : MetaCICAuditMapFamilyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICAuditMapFamilyUp.mk localMaps synthesisRows obstructionRows frontierRows
      dependencyLedger transports routes provenance localName =>
      [[BMark.b0],
        metaCICAuditMapFamilyEncodeBHist localMaps,
        [BMark.b1, BMark.b0],
        metaCICAuditMapFamilyEncodeBHist synthesisRows,
        [BMark.b1, BMark.b1, BMark.b0],
        metaCICAuditMapFamilyEncodeBHist obstructionRows,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICAuditMapFamilyEncodeBHist frontierRows,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICAuditMapFamilyEncodeBHist dependencyLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICAuditMapFamilyEncodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICAuditMapFamilyEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metaCICAuditMapFamilyEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metaCICAuditMapFamilyEncodeBHist localName]

def metaCICAuditMapFamilyFromEventFlow : EventFlow → Option MetaCICAuditMapFamilyUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | localMaps :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | synthesisRows :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | obstructionRows :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | frontierRows :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | dependencyLedger :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transports :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | routes :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | localName ::
                                                                          rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (MetaCICAuditMapFamilyUp.mk
                                                                                  (metaCICAuditMapFamilyDecodeBHist
                                                                                    localMaps)
                                                                                  (metaCICAuditMapFamilyDecodeBHist
                                                                                    synthesisRows)
                                                                                  (metaCICAuditMapFamilyDecodeBHist
                                                                                    obstructionRows)
                                                                                  (metaCICAuditMapFamilyDecodeBHist
                                                                                    frontierRows)
                                                                                  (metaCICAuditMapFamilyDecodeBHist
                                                                                    dependencyLedger)
                                                                                  (metaCICAuditMapFamilyDecodeBHist
                                                                                    transports)
                                                                                  (metaCICAuditMapFamilyDecodeBHist
                                                                                    routes)
                                                                                  (metaCICAuditMapFamilyDecodeBHist
                                                                                    provenance)
                                                                                  (metaCICAuditMapFamilyDecodeBHist
                                                                                    localName))
                                                                          | _ :: _ => none

private theorem metaCICAuditMapFamily_round_trip :
    ∀ x : MetaCICAuditMapFamilyUp,
      metaCICAuditMapFamilyFromEventFlow
        (metaCICAuditMapFamilyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk localMaps synthesisRows obstructionRows frontierRows dependencyLedger transports
      routes provenance localName =>
      change
        some
          (MetaCICAuditMapFamilyUp.mk
            (metaCICAuditMapFamilyDecodeBHist
              (metaCICAuditMapFamilyEncodeBHist localMaps))
            (metaCICAuditMapFamilyDecodeBHist
              (metaCICAuditMapFamilyEncodeBHist synthesisRows))
            (metaCICAuditMapFamilyDecodeBHist
              (metaCICAuditMapFamilyEncodeBHist obstructionRows))
            (metaCICAuditMapFamilyDecodeBHist
              (metaCICAuditMapFamilyEncodeBHist frontierRows))
            (metaCICAuditMapFamilyDecodeBHist
              (metaCICAuditMapFamilyEncodeBHist dependencyLedger))
            (metaCICAuditMapFamilyDecodeBHist
              (metaCICAuditMapFamilyEncodeBHist transports))
            (metaCICAuditMapFamilyDecodeBHist
              (metaCICAuditMapFamilyEncodeBHist routes))
            (metaCICAuditMapFamilyDecodeBHist
              (metaCICAuditMapFamilyEncodeBHist provenance))
            (metaCICAuditMapFamilyDecodeBHist
              (metaCICAuditMapFamilyEncodeBHist localName))) =
          some
            (MetaCICAuditMapFamilyUp.mk localMaps synthesisRows obstructionRows
              frontierRows dependencyLedger transports routes provenance localName)
      rw [metaCICAuditMapFamilyDecode_encode_bhist localMaps,
        metaCICAuditMapFamilyDecode_encode_bhist synthesisRows,
        metaCICAuditMapFamilyDecode_encode_bhist obstructionRows,
        metaCICAuditMapFamilyDecode_encode_bhist frontierRows,
        metaCICAuditMapFamilyDecode_encode_bhist dependencyLedger,
        metaCICAuditMapFamilyDecode_encode_bhist transports,
        metaCICAuditMapFamilyDecode_encode_bhist routes,
        metaCICAuditMapFamilyDecode_encode_bhist provenance,
        metaCICAuditMapFamilyDecode_encode_bhist localName]

private theorem metaCICAuditMapFamilyToEventFlow_injective
    {x y : MetaCICAuditMapFamilyUp} :
    metaCICAuditMapFamilyToEventFlow x =
      metaCICAuditMapFamilyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICAuditMapFamilyFromEventFlow (metaCICAuditMapFamilyToEventFlow x) =
        metaCICAuditMapFamilyFromEventFlow (metaCICAuditMapFamilyToEventFlow y) :=
    congrArg metaCICAuditMapFamilyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaCICAuditMapFamily_round_trip x).symm
      (Eq.trans hread (metaCICAuditMapFamily_round_trip y)))

private theorem MetaCICAuditMapFamilyTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : MetaCICAuditMapFamilyUp,
      metaCICAuditMapFamilyFields x = metaCICAuditMapFamilyFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk localMaps synthesisRows obstructionRows frontierRows dependencyLedger transports
      routes provenance localName =>
      cases y with
      | mk localMaps' synthesisRows' obstructionRows' frontierRows' dependencyLedger'
          transports' routes' provenance' localName' =>
          cases hfields
          rfl

instance metaCICAuditMapFamilyBHistCarrier :
    BHistCarrier MetaCICAuditMapFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICAuditMapFamilyToEventFlow
  fromEventFlow := metaCICAuditMapFamilyFromEventFlow

instance metaCICAuditMapFamilyChapterTasteGate :
    ChapterTasteGate MetaCICAuditMapFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICAuditMapFamilyFromEventFlow
        (metaCICAuditMapFamilyToEventFlow x) = some x
    exact metaCICAuditMapFamily_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICAuditMapFamilyToEventFlow_injective heq)

instance metaCICAuditMapFamilyFieldFaithful :
    FieldFaithful MetaCICAuditMapFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metaCICAuditMapFamilyFields
  field_faithful := MetaCICAuditMapFamilyTasteGate_single_carrier_alignment_field_faithful

def taste_gate : ChapterTasteGate MetaCICAuditMapFamilyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICAuditMapFamilyChapterTasteGate

theorem MetaCICAuditMapFamilyTasteGate_single_carrier_alignment :
    (∀ h : BHist, metaCICAuditMapFamilyDecodeBHist
      (metaCICAuditMapFamilyEncodeBHist h) = h) ∧
      (∀ x : MetaCICAuditMapFamilyUp,
        metaCICAuditMapFamilyFromEventFlow
          (metaCICAuditMapFamilyToEventFlow x) = some x) ∧
        (∀ x y : MetaCICAuditMapFamilyUp,
          metaCICAuditMapFamilyToEventFlow x =
            metaCICAuditMapFamilyToEventFlow y → x = y) ∧
          metaCICAuditMapFamilyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact metaCICAuditMapFamilyDecode_encode_bhist
  · constructor
    · exact metaCICAuditMapFamily_round_trip
    · constructor
      · intro x y heq
        exact metaCICAuditMapFamilyToEventFlow_injective heq
      · rfl

end BEDC.Derived.MetaCICAuditMapFamilyUp
